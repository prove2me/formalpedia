-- Prove2me | solution 1 for SmaleNinth.lp_strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T02:05:09.665562+00:00
-- url     : https://prove2.me/submissions/44977966-e7c1-491b-804c-1e94c1a6b126

import Definitions.Def_Polyhedron
import Mathlib.Tactic

/-!
# Strong duality for linear programming

The classical derivation from Farkas' lemma, itself proved here by
Fourier–Motzkin elimination.

* `fm_step` eliminates the last variable from a system of linear inequalities
  indexed by an arbitrary finite type; `redF` is the reduced data, `feas_red`
  the invariance of feasibility, and `yOf`/`transfer` the lifting of
  nonnegative multipliers.  Induction on the number of variables gives the
  infeasibility certificate `farkas_cert`, and `farkas_cert'` transports it to
  systems whose variables are indexed by any finite type.
* `dual_feasible`: boundedness of the primal objective forbids a feasible
  direction of descent, hence the dual is feasible.
* `strong_duality`: Farkas applied to the combined system in `(x, y)` — primal
  feasibility, dual feasibility and the coupling `c'x ≤ b'y` — is feasible,
  because an infeasibility certificate is impossible whether or not its
  multiplier on the coupling row vanishes.
-/

open Matrix LinearOptimization Finset

namespace FarkasDev

/-- Feasibility of the system indexed by an arbitrary finite type. -/
def Feas {ι : Type} [Fintype ι] {n : ℕ} (A : ι → Fin n → ℝ) (c : ι → ℝ) : Prop :=
  ∃ x : Fin n → ℝ, ∀ i, c i ≤ ∑ k, A i k * x k

/-- Fourier–Motzkin elimination of the last variable, for an arbitrary finite index type. -/
theorem fm_step {ι : Type} [Fintype ι] {n : ℕ} (A : ι → Fin (n + 1) → ℝ) (c : ι → ℝ) :
    Feas A c ↔
      ∃ y : Fin n → ℝ,
        (∀ i, A i (Fin.last n) = 0 → c i ≤ ∑ k : Fin n, A i k.castSucc * y k) ∧
        (∀ i j, 0 < A i (Fin.last n) → A j (Fin.last n) < 0 →
            A i (Fin.last n) * c j - A j (Fin.last n) * c i ≤
              ∑ k : Fin n, (A i (Fin.last n) * A j k.castSucc
                - A j (Fin.last n) * A i k.castSucc) * y k) := by
  classical
  have hmv : ∀ (x : Fin (n + 1) → ℝ) (i : ι),
      (∑ k, A i k * x k)
        = (∑ k : Fin n, A i k.castSucc * x k.castSucc) + A i (Fin.last n) * x (Fin.last n) :=
    fun x i => Fin.sum_univ_castSucc _
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun k => x k.castSucc, ?_, ?_⟩
    · intro i hi
      have := hx i
      rw [hmv, hi] at this
      linarith
    · intro i j hi hj
      have h1 := hx i
      have h2 := hx j
      rw [hmv] at h1 h2
      have hsum : ∑ k : Fin n, (A i (Fin.last n) * A j k.castSucc
            - A j (Fin.last n) * A i k.castSucc) * x k.castSucc
          = A i (Fin.last n) * (∑ k : Fin n, A j k.castSucc * x k.castSucc)
            - A j (Fin.last n) * (∑ k : Fin n, A i k.castSucc * x k.castSucc) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [hsum]
      nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt (neg_pos.mpr hj)),
        mul_le_mul_of_nonneg_left h2 (le_of_lt hi)]
  · rintro ⟨y, hZ, hPN⟩
    set S : ι → ℝ := fun i => ∑ k : Fin n, A i k.castSucc * y k with hS
    set B : ι → ℝ := fun i => A i (Fin.last n) with hB
    have hpair : ∀ i j, 0 < B i → B j < 0 → B i * c j - B j * c i ≤ B i * S j - B j * S i := by
      intro i j hi hj
      have h := hPN i j hi hj
      have hsum : ∑ k : Fin n, (A i (Fin.last n) * A j k.castSucc
            - A j (Fin.last n) * A i k.castSucc) * y k = B i * S j - B j * S i := by
        rw [hS, hB]
        simp only
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [hsum] at h
      exact h
    set P : Finset ι := Finset.univ.filter (fun i => 0 < B i) with hPdef
    set N : Finset ι := Finset.univ.filter (fun i => B i < 0) with hNdef
    have key : ∀ v : ℝ,
        (∀ i ∈ P, (c i - S i) / B i ≤ v) → (∀ j ∈ N, v ≤ (c j - S j) / B j) → Feas A c := by
      intro v hlow hup
      refine ⟨Fin.snoc y v, fun i => ?_⟩
      have hval : (∑ k, A i k * (Fin.snoc y v : Fin (n+1) → ℝ) k) = S i + B i * v := by
        rw [hmv]
        simp [hS, hB, Fin.snoc_castSucc, Fin.snoc_last]
      rw [hval]
      rcases lt_trichotomy (B i) 0 with hneg | hzero | hpos
      · have := hup i (by simp [hNdef, hneg])
        rw [le_div_iff_of_neg hneg] at this
        linarith
      · have h0 : A i (Fin.last n) = 0 := hzero
        have := hZ i h0
        rw [hzero]
        simpa [hS] using this
      · have := hlow i (by simp [hPdef, hpos])
        rw [div_le_iff₀ hpos] at this
        linarith
    by_cases hP : P.Nonempty
    · obtain ⟨i₀, hi₀, hmax⟩ := P.exists_max_image (fun i => (c i - S i) / B i) hP
      refine key ((c i₀ - S i₀) / B i₀) (fun i hi => hmax i hi) (fun j hj => ?_)
      have hi₀' : 0 < B i₀ := by simpa [hPdef] using hi₀
      have hj' : B j < 0 := by simpa [hNdef] using hj
      have hp := hpair i₀ j hi₀' hj'
      rw [le_div_iff_of_neg hj', div_mul_eq_mul_div, le_div_iff₀ hi₀']
      nlinarith [hp]
    · by_cases hN : N.Nonempty
      · obtain ⟨j₀, hj₀, hmin⟩ := N.exists_min_image (fun j => (c j - S j) / B j) hN
        exact key ((c j₀ - S j₀) / B j₀) (fun i hi => absurd ⟨i, hi⟩ hP) (fun j hj => hmin j hj)
      · exact key 0 (fun i hi => absurd ⟨i, hi⟩ hP) (fun j hj => absurd ⟨j, hj⟩ hN)

end FarkasDev

namespace FarkasDev

open Classical in
/-- The reduced data after eliminating the last variable: rows with vanishing
last coefficient are kept, pairs of rows with opposite last coefficients are
combined. -/
noncomputable def redF {ι : Type} {n : ℕ} (A : ι → Fin (n + 1) → ℝ) (f : ι → ℝ) :
    (ι ⊕ ι × ι) → ℝ
  | Sum.inl i => if A i (Fin.last n) = 0 then f i else 0
  | Sum.inr (i, j) =>
      if 0 < A i (Fin.last n) ∧ A j (Fin.last n) < 0 then
        A i (Fin.last n) * f j - A j (Fin.last n) * f i
      else 0

open Classical in
/-- The multipliers of the original rows obtained from multipliers of the reduced rows. -/
noncomputable def yOf {ι : Type} [Fintype ι] {n : ℕ} (A : ι → Fin (n + 1) → ℝ)
    (z : (ι ⊕ ι × ι) → ℝ) : ι → ℝ := fun i =>
  (if A i (Fin.last n) = 0 then z (Sum.inl i) else 0)
  + (∑ j, if 0 < A i (Fin.last n) ∧ A j (Fin.last n) < 0 then
        (- A j (Fin.last n)) * z (Sum.inr (i, j)) else 0)
  + (∑ j, if 0 < A j (Fin.last n) ∧ A i (Fin.last n) < 0 then
        A j (Fin.last n) * z (Sum.inr (j, i)) else 0)

/-- Transfer of a linear functional along the elimination. -/
lemma transfer {ι : Type} [Fintype ι] {n : ℕ} (A : ι → Fin (n + 1) → ℝ)
    (z : (ι ⊕ ι × ι) → ℝ) (f : ι → ℝ) :
    ∑ i, yOf A z i * f i = ∑ i', z i' * redF A f i' := by
  classical
  rw [Fintype.sum_sum_type]
  have hL : ∑ i, yOf A z i * f i
      = (∑ i, (if A i (Fin.last n) = 0 then z (Sum.inl i) else 0) * f i)
        + (∑ i, ∑ j, (if 0 < A i (Fin.last n) ∧ A j (Fin.last n) < 0 then
            (- A j (Fin.last n)) * z (Sum.inr (i, j)) else 0) * f i)
        + (∑ i, ∑ j, (if 0 < A j (Fin.last n) ∧ A i (Fin.last n) < 0 then
            A j (Fin.last n) * z (Sum.inr (j, i)) else 0) * f i) := by
    simp only [yOf, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [hL]
  have h1 : (∑ i, (if A i (Fin.last n) = 0 then z (Sum.inl i) else 0) * f i)
      = ∑ i, z (Sum.inl i) * redF A f (Sum.inl i) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [redF]
    split_ifs <;> ring
  have h3 : (∑ i, ∑ j, (if 0 < A j (Fin.last n) ∧ A i (Fin.last n) < 0 then
        A j (Fin.last n) * z (Sum.inr (j, i)) else 0) * f i)
      = ∑ i, ∑ j, (if 0 < A i (Fin.last n) ∧ A j (Fin.last n) < 0 then
        A i (Fin.last n) * z (Sum.inr (i, j)) else 0) * f j := by
    rw [Finset.sum_comm]
  rw [Fintype.sum_prod_type, h1, h3, add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [redF]
  split_ifs <;> ring

end FarkasDev

namespace FarkasDev

/-- Feasibility is preserved by the elimination. -/
lemma feas_red {ι : Type} [Fintype ι] {n : ℕ} (A : ι → Fin (n + 1) → ℝ) (c : ι → ℝ) :
    Feas A c ↔ Feas (fun i' k => redF A (fun i => A i k.castSucc) i') (redF A c) := by
  classical
  rw [fm_step]
  constructor
  · rintro ⟨y, hZ, hPN⟩
    refine ⟨y, ?_⟩
    rintro (i | ⟨i, j⟩)
    · by_cases h : A i (Fin.last n) = 0
      · have e : ∀ k : Fin n, redF A (fun i => A i k.castSucc) (Sum.inl i) = A i k.castSucc := by
          intro k; simp only [redF, if_pos h]
        simp only [e, redF, if_pos h]
        exact hZ i h
      · simp only [redF, if_neg h]
        simp
    · by_cases h : 0 < A i (Fin.last n) ∧ A j (Fin.last n) < 0
      · have e : ∀ k : Fin n, redF A (fun i => A i k.castSucc) (Sum.inr (i, j))
            = A i (Fin.last n) * A j k.castSucc - A j (Fin.last n) * A i k.castSucc := by
          intro k; simp only [redF, if_pos h]
        simp only [e, redF, if_pos h]
        exact hPN i j h.1 h.2
      · simp only [redF, if_neg h]
        simp
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_, ?_⟩
    · intro i hi
      have := hy (Sum.inl i)
      simp only [redF, if_pos hi] at this
      exact this
    · intro i j hi hj
      have := hy (Sum.inr (i, j))
      simp only [redF, if_pos (And.intro hi hj)] at this
      exact this

/-- The eliminated column receives multiplier zero. -/
lemma redF_last {ι : Type} {n : ℕ} (A : ι → Fin (n + 1) → ℝ) :
    ∀ i', redF A (fun i => A i (Fin.last n)) i' = 0 := by
  classical
  rintro (i | ⟨i, j⟩)
  · simp only [redF]
    split_ifs with h
    · exact h
    · rfl
  · simp only [redF]
    split_ifs with h
    · ring
    · rfl

/-- **Farkas' lemma, certificate form.** An infeasible system of linear inequalities
carries a nonnegative combination of its rows that is identically zero with positive
right-hand side. -/
theorem farkas_cert : ∀ (n : ℕ) {ι : Type} [Fintype ι] (A : ι → Fin n → ℝ) (c : ι → ℝ),
    ¬ Feas A c →
      ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ k, ∑ i, y i * A i k = 0) ∧ 0 < ∑ i, y i * c i := by
  intro n
  induction n with
  | zero =>
    intro ι _ A c hinf
    classical
    have hx : ¬ ∀ i, c i ≤ 0 := by
      intro h
      exact hinf ⟨fun _ => 0, fun i => by simpa using h i⟩
    push_neg at hx
    obtain ⟨i₀, hi₀⟩ := hx
    refine ⟨fun i => if i = i₀ then 1 else 0, fun i => by dsimp only; split_ifs <;> norm_num,
      fun k => Fin.elim0 k, ?_⟩
    simpa using hi₀
  | succ n ih =>
    intro ι _ A c hinf
    classical
    have hred : ¬ Feas (fun i' k => redF A (fun i => A i k.castSucc) i') (redF A c) := by
      rw [← feas_red]; exact hinf
    obtain ⟨z, hz0, hzA, hzc⟩ := ih _ _ hred
    refine ⟨yOf A z, ?_, ?_, ?_⟩
    · intro i
      unfold yOf
      have t1 : 0 ≤ (if A i (Fin.last n) = 0 then z (Sum.inl i) else 0) := by
        split_ifs
        · exact hz0 _
        · exact le_rfl
      have t2 : 0 ≤ ∑ j, (if 0 < A i (Fin.last n) ∧ A j (Fin.last n) < 0 then
            (- A j (Fin.last n)) * z (Sum.inr (i, j)) else 0) := by
        refine Finset.sum_nonneg (fun j _ => ?_)
        split_ifs with h
        · exact mul_nonneg (by linarith [h.2]) (hz0 _)
        · exact le_rfl
      have t3 : 0 ≤ ∑ j, (if 0 < A j (Fin.last n) ∧ A i (Fin.last n) < 0 then
            A j (Fin.last n) * z (Sum.inr (j, i)) else 0) := by
        refine Finset.sum_nonneg (fun j _ => ?_)
        split_ifs with h
        · exact mul_nonneg (le_of_lt h.1) (hz0 _)
        · exact le_rfl
      linarith
    · intro k
      rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
      · rw [transfer]
        exact hzA k'
      · rw [transfer]
        simp [redF_last A]
    · rw [transfer]
      exact hzc

end FarkasDev


open FarkasDev

namespace DualDev

/-- Farkas certificate for a system whose variables are indexed by any finite type. -/
theorem farkas_cert' {ι κ : Type} [Fintype ι] [Fintype κ] (A : ι → κ → ℝ) (c : ι → ℝ)
    (hinf : ¬ ∃ x : κ → ℝ, ∀ i, c i ≤ ∑ k, A i k * x k) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ k, ∑ i, y i * A i k = 0) ∧ 0 < ∑ i, y i * c i := by
  classical
  set e := Fintype.equivFin κ with he
  have hinf' : ¬ Feas (fun i (j : Fin (Fintype.card κ)) => A i (e.symm j)) c := by
    rintro ⟨x, hx⟩
    refine hinf ⟨fun k => x (e k), fun i => ?_⟩
    have := hx i
    calc c i ≤ ∑ j, A i (e.symm j) * x j := this
      _ = ∑ k, A i k * x (e k) := by
          rw [← Equiv.sum_comp e (fun j => A i (e.symm j) * x j)]
          exact Finset.sum_congr rfl (fun k _ => by simp)
  obtain ⟨y, hy0, hyA, hyc⟩ := farkas_cert _ _ _ hinf'
  refine ⟨y, hy0, fun k => ?_, hyc⟩
  have := hyA (e k)
  simpa using this

variable {m n : ℕ}

/-- `x` satisfies the primal constraints. -/
def PFeas (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ i, b i ≤ ∑ k, A i k * x k

/-- `y` satisfies the dual constraints. -/
def DFeas (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ ∀ k, ∑ i, y i * A i k = c k

lemma mem_polyhedron_iff (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    x ∈ polyhedron A b ↔ PFeas A b x := by
  constructor
  · intro hx i; simpa [Matrix.mulVec, dotProduct] using hx i
  · intro hx i; simpa [Matrix.mulVec, dotProduct] using hx i

/-- **Weak duality.** -/
theorem weak_duality (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    {x : Fin n → ℝ} {y : Fin m → ℝ} (hx : PFeas A b x) (hy : DFeas A c y) :
    ∑ i, y i * b i ≤ ∑ k, c k * x k := by
  have h1 : ∑ i, y i * b i ≤ ∑ i, y i * (∑ k, A i k * x k) :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i) (hy.1 i))
  have h2 : ∑ i, y i * (∑ k, A i k * x k) = ∑ k, (∑ i, y i * A i k) * x k := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => by ring))
  rw [h2] at h1
  simpa [hy.2] using h1

/-- If the primal is feasible and bounded below, the dual is feasible. -/
theorem dual_feasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    {x₀ : Fin n → ℝ} (hx₀ : PFeas A b x₀) {v : ℝ}
    (hbdd : ∀ x, PFeas A b x → v ≤ ∑ k, c k * x k) :
    ∃ y, DFeas A c y := by
  classical
  by_contra hno
  push_neg at hno
  -- the dual system, written with inequalities only
  set B : (Fin m ⊕ Fin n ⊕ Fin n) → Fin m → ℝ := fun r i =>
    match r with
    | Sum.inl i₀ => if i = i₀ then 1 else 0
    | Sum.inr (Sum.inl k) => A i k
    | Sum.inr (Sum.inr k) => - A i k with hB
  set d : (Fin m ⊕ Fin n ⊕ Fin n) → ℝ := fun r =>
    match r with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl k) => c k
    | Sum.inr (Sum.inr k) => - c k with hd
  have hinf : ¬ ∃ y : Fin m → ℝ, ∀ r, d r ≤ ∑ i, B r i * y i := by
    rintro ⟨y, hy⟩
    refine hno y ⟨fun i => ?_, fun k => ?_⟩
    · have := hy (Sum.inl i)
      simpa [hB, hd, Finset.sum_ite_eq'] using this
    · have h1 := hy (Sum.inr (Sum.inl k))
      have h2 := hy (Sum.inr (Sum.inr k))
      simp only [hB, hd] at h1 h2
      have e2 : ∑ i, -A i k * y i = - ∑ i, y i * A i k := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      have e1 : ∑ i, A i k * y i = ∑ i, y i * A i k :=
        Finset.sum_congr rfl (fun i _ => by ring)
      rw [e1] at h1
      rw [e2] at h2
      linarith
  obtain ⟨z, hz0, hzB, hzd⟩ := farkas_cert' B d hinf
  -- read off the improving direction
  set w : Fin n → ℝ := fun k => z (Sum.inr (Sum.inl k)) - z (Sum.inr (Sum.inr k)) with hw
  have hrow : ∀ i, ∑ k, A i k * w k = - z (Sum.inl i) := by
    intro i
    have := hzB i
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at this
    simp only [hB] at this
    have e0 : ∑ r : Fin m, z (Sum.inl r) * (if i = r then (1:ℝ) else 0) = z (Sum.inl i) := by
      simp [Finset.sum_ite_eq']
    rw [e0] at this
    have e3 : ∑ k, z (Sum.inr (Sum.inl k)) * A i k + ∑ k, z (Sum.inr (Sum.inr k)) * (-A i k)
        = ∑ k, A i k * w k := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by simp [hw]; ring)
    linarith [this, e3 ▸ this]
  have hobj : 0 < ∑ k, c k * w k := by
    have e : ∑ r, z r * d r = ∑ k, c k * w k := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      have z0 : ∑ i : Fin m, z (Sum.inl i) * d (Sum.inl i) = 0 := by simp [hd]
      rw [z0, zero_add, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by simp only [hd, hw]; ring)
    rw [← e]
    exact hzd
  -- the direction keeps feasibility and drives the objective down
  have hstep : ∀ t : ℝ, 0 ≤ t → PFeas A b (fun k => x₀ k - t * w k) := by
    intro t ht i
    have h1 : ∑ k, A i k * (x₀ k - t * w k) = (∑ k, A i k * x₀ k) - t * (∑ k, A i k * w k) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [h1, hrow i]
    have := hx₀ i
    nlinarith [hz0 (Sum.inl i)]
  have hval : ∀ t : ℝ, ∑ k, c k * (x₀ k - t * w k)
      = (∑ k, c k * x₀ k) - t * (∑ k, c k * w k) := by
    intro t
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  set T : ℝ := ((∑ k, c k * x₀ k) - v + 1) / (∑ k, c k * w k) with hT
  have hTpos : 0 ≤ T := by
    rw [hT]
    apply div_nonneg _ (le_of_lt hobj)
    have := hbdd x₀ hx₀
    linarith
  have hcontra := hbdd _ (hstep T hTpos)
  rw [hval T, hT, div_mul_cancel₀ _ (ne_of_gt hobj)] at hcontra
  linarith

end DualDev

namespace DualDev

/-- Splitting a sum over the row type of the combined system. -/
lemma row_split {m n : ℕ} (f : (Fin m ⊕ Fin m ⊕ Fin n ⊕ Fin n ⊕ Unit) → ℝ) :
    ∑ r, f r = (∑ i, f (Sum.inl i)) + ((∑ i, f (Sum.inr (Sum.inl i)))
      + ((∑ k, f (Sum.inr (Sum.inr (Sum.inl k))))
        + ((∑ k, f (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
          + f (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp

variable {m n : ℕ}

/-- **Strong duality.** -/
theorem strong_duality (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    {x₀ : Fin n → ℝ} (hx₀ : PFeas A b x₀) {v : ℝ}
    (hbdd : ∀ x, PFeas A b x → v ≤ ∑ k, c k * x k) :
    ∃ (x : Fin n → ℝ) (y : Fin m → ℝ), PFeas A b x ∧ DFeas A c y ∧
      ∑ k, c k * x k = ∑ i, y i * b i := by
  classical
  obtain ⟨y₀, hy₀⟩ := dual_feasible A b c hx₀ hbdd
  set M : (Fin m ⊕ Fin m ⊕ Fin n ⊕ Fin n ⊕ Unit) → (Fin n ⊕ Fin m) → ℝ := fun r kk =>
    match r, kk with
    | Sum.inl i, Sum.inl k => A i k
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr (Sum.inl _), Sum.inl _ => 0
    | Sum.inr (Sum.inl i₀), Sum.inr i => if i = i₀ then 1 else 0
    | Sum.inr (Sum.inr (Sum.inl _)), Sum.inl _ => 0
    | Sum.inr (Sum.inr (Sum.inl k)), Sum.inr i => A i k
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))), Sum.inl _ => 0
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl k))), Sum.inr i => - A i k
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))), Sum.inl k => - c k
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))), Sum.inr i => b i with hM
  set g : (Fin m ⊕ Fin m ⊕ Fin n ⊕ Fin n ⊕ Unit) → ℝ := fun r =>
    match r with
    | Sum.inl i => b i
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (Sum.inl k)) => c k
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl k))) => - c k
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => 0 with hg
  by_cases hfeas : ∃ z : (Fin n ⊕ Fin m) → ℝ, ∀ r, g r ≤ ∑ kk, M r kk * z kk
  · -- a solution of the combined system is a pair of optimal solutions
    obtain ⟨z, hz⟩ := hfeas
    set x : Fin n → ℝ := fun k => z (Sum.inl k) with hx
    set y : Fin m → ℝ := fun i => z (Sum.inr i) with hy
    have hP : PFeas A b x := by
      intro i
      have h := hz (Sum.inl i)
      rw [Fintype.sum_sum_type] at h
      simpa [hM, hg, hx] using h
    have hY0 : ∀ i, 0 ≤ y i := by
      intro i
      have h := hz (Sum.inr (Sum.inl i))
      rw [Fintype.sum_sum_type] at h
      simpa [hM, hg, hy, Finset.sum_ite_eq'] using h
    have hEq : ∀ k, ∑ i, y i * A i k = c k := by
      intro k
      have h1 := hz (Sum.inr (Sum.inr (Sum.inl k)))
      have h2 := hz (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))
      rw [Fintype.sum_sum_type] at h1 h2
      simp only [hM, hg, zero_mul, Finset.sum_const_zero, zero_add] at h1 h2
      have e1 : ∑ i, A i k * z (Sum.inr i) = ∑ i, y i * A i k :=
        Finset.sum_congr rfl (fun i _ => by simp [hy]; try ring)
      have e2 : ∑ i, -A i k * z (Sum.inr i) = - ∑ i, y i * A i k := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by simp [hy]; try ring)
      rw [e1] at h1
      rw [e2] at h2
      linarith
    have hD : DFeas A c y := ⟨hY0, hEq⟩
    have hcouple : ∑ k, c k * x k ≤ ∑ i, y i * b i := by
      have h := hz (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))
      rw [Fintype.sum_sum_type] at h
      simp only [hM, hg] at h
      have e1 : ∑ k, -c k * z (Sum.inl k) = - ∑ k, c k * x k := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun k _ => by simp [hx]; try ring)
      have e2 : ∑ i, b i * z (Sum.inr i) = ∑ i, y i * b i :=
        Finset.sum_congr rfl (fun i _ => by simp [hy]; try ring)
      rw [e1, e2] at h
      linarith
    exact ⟨x, y, hP, hD, le_antisymm hcouple (weak_duality A b c hP hD)⟩
  · -- infeasibility of the combined system is impossible
    exfalso
    obtain ⟨t, ht0, htM, htg⟩ := farkas_cert' M g hfeas
    set u : Fin m → ℝ := fun i => t (Sum.inl i) with hu
    set w : Fin n → ℝ := fun k =>
      t (Sum.inr (Sum.inr (Sum.inl k))) - t (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))) with hw
    set s : ℝ := t (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))) with hs
    have hs0 : 0 ≤ s := ht0 _
    have hu0 : ∀ i, 0 ≤ u i := fun i => ht0 _
    -- the columns of the `x` block
    have hcolx : ∀ k, ∑ i, u i * A i k = s * c k := by
      intro k
      have h := htM (Sum.inl k)
      rw [row_split] at h
      simp only [hM, mul_zero, Finset.sum_const_zero, zero_add, add_zero] at h
      have e : ∑ i, t (Sum.inl i) * A i k = ∑ i, u i * A i k := rfl
      rw [e] at h
      have h2 : ∑ i, u i * A i k + s * (- c k) = 0 := h
      linarith [h2]
    -- the columns of the `y` block
    have hcoly : ∀ i, ∑ k, A i k * w k + s * b i ≤ 0 := by
      intro i
      have h := htM (Sum.inr i)
      rw [row_split] at h
      simp only [hM, mul_zero, Finset.sum_const_zero, zero_add] at h
      have e0 : ∑ i', t (Sum.inr (Sum.inl i')) * (if i = i' then (1:ℝ) else 0)
          = t (Sum.inr (Sum.inl i)) := by simp
      rw [e0] at h
      have e1 : ∑ k, t (Sum.inr (Sum.inr (Sum.inl k))) * A i k
            + ∑ k, t (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))) * (- A i k)
          = ∑ k, A i k * w k := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        show _ = A i k * (t (Sum.inr (Sum.inr (Sum.inl k)))
          - t (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
        ring
      have hv : 0 ≤ t (Sum.inr (Sum.inl i)) := ht0 _
      linarith [h, e1]
    -- the right-hand side
    have hrhs : 0 < (∑ i, u i * b i) + ∑ k, c k * w k := by
      have e : ∑ r, t r * g r = (∑ i, u i * b i) + ∑ k, c k * w k := by
        rw [row_split]
        simp only [hg, mul_zero, Finset.sum_const_zero, add_zero, zero_add]
        have e1 : ∑ i, t (Sum.inl i) * b i = ∑ i, u i * b i := rfl
        have e2 : ∑ k, t (Sum.inr (Sum.inr (Sum.inl k))) * c k
              + ∑ k, t (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))) * (- c k)
            = ∑ k, c k * w k := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          show _ = c k * (t (Sum.inr (Sum.inr (Sum.inl k)))
            - t (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
          ring
        rw [e1, e2]
      rw [← e]
      exact htg
    rcases lt_or_eq_of_le hs0 with hspos | hszero
    · -- a positive multiplier on the coupling row contradicts the certificate itself
      have hkey : ∑ i, u i * (∑ k, A i k * w k + s * b i) ≤ 0 :=
        Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hu0 i) (hcoly i))
      have he : ∑ i, u i * (∑ k, A i k * w k + s * b i)
          = s * ((∑ i, u i * b i) + ∑ k, c k * w k) := by
        have step1 : ∀ i, u i * (∑ k, A i k * w k + s * b i)
            = (∑ k, u i * A i k * w k) + s * (u i * b i) := by
          intro i
          rw [mul_add, Finset.mul_sum]
          congr 1
          · exact Finset.sum_congr rfl (fun k _ => by ring)
          · ring
        rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => step1 i),
          Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
        have step2 : ∑ k, ∑ i, u i * A i k * w k = s * ∑ k, c k * w k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [← Finset.sum_mul, hcolx k]
          ring
        rw [step2]
        ring
      rw [he] at hkey
      nlinarith [mul_pos hspos hrhs]
    · -- a zero multiplier contradicts feasibility of the primal and of the dual
      have hsz : s = 0 := hszero.symm
      have h1 : ∑ i, u i * b i ≤ 0 := by
        have hle : ∑ i, u i * b i ≤ ∑ i, u i * (∑ k, A i k * x₀ k) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx₀ i) (hu0 i))
        have he : ∑ i, u i * (∑ k, A i k * x₀ k) = ∑ k, (∑ i, u i * A i k) * x₀ k := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => by ring))
        rw [he] at hle
        have hz : ∀ k, (∑ i, u i * A i k) * x₀ k = 0 := by
          intro k; rw [hcolx k, hsz]; ring
        rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hz k)] at hle
        simpa using hle
      have h2 : ∑ k, c k * w k ≤ 0 := by
        have he : ∑ k, c k * w k = ∑ i, y₀ i * (∑ k, A i k * w k) := by
          have hc : ∀ k, c k = ∑ i, y₀ i * A i k := fun k => (hy₀.2 k).symm
          calc ∑ k, c k * w k = ∑ k, (∑ i, y₀ i * A i k) * w k :=
                Finset.sum_congr rfl (fun k _ => by rw [← hc k])
            _ = ∑ k, ∑ i, y₀ i * A i k * w k :=
                Finset.sum_congr rfl (fun k _ => by rw [Finset.sum_mul])
            _ = ∑ i, ∑ k, y₀ i * A i k * w k := Finset.sum_comm
            _ = ∑ i, y₀ i * (∑ k, A i k * w k) := by
                refine Finset.sum_congr rfl (fun i _ => ?_)
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl (fun k _ => by ring)
        rw [he]
        refine Finset.sum_nonpos (fun i _ => ?_)
        have hcy := hcoly i
        rw [hsz] at hcy
        exact mul_nonpos_of_nonneg_of_nonpos (hy₀.1 i) (by linarith [hcy])
      linarith

end DualDev

open DualDev in
/-- **Strong duality for linear programming.** -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hfeas : (polyhedron A b).Nonempty)
    (hbdd : ∃ v : ℝ, ∀ x ∈ polyhedron A b, v ≤ ∑ k, c k * x k) :
    ∃ (x : Fin n → ℝ) (y : Fin m → ℝ),
      x ∈ polyhedron A b ∧ (∀ i, 0 ≤ y i) ∧ (∀ k, ∑ i, y i * A i k = c k) ∧
      (∑ k, c k * x k = ∑ i, y i * b i) ∧
      (∀ x' ∈ polyhedron A b, ∑ k, c k * x k ≤ ∑ k, c k * x' k) := by
  obtain ⟨x₀, hx₀⟩ := hfeas
  obtain ⟨v, hv⟩ := hbdd
  have hx₀' : PFeas A b x₀ := (mem_polyhedron_iff A b x₀).mp hx₀
  have hbdd' : ∀ x, PFeas A b x → v ≤ ∑ k, c k * x k :=
    fun x hx => hv x ((mem_polyhedron_iff A b x).mpr hx)
  obtain ⟨x, y, hP, hD, hval⟩ := strong_duality A b c hx₀' hbdd'
  refine ⟨x, y, (mem_polyhedron_iff A b x).mpr hP, hD.1, hD.2, hval, ?_⟩
  intro x' hx'
  have hP' : PFeas A b x' := (mem_polyhedron_iff A b x').mp hx'
  have := weak_duality A b c hP' hD
  linarith [hval]
