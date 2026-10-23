-- Prove2me | solution 1 for TwoEchelonCVRP.LPCompare.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T16:56:47.04219+00:00
-- url     : https://prove2.me/submissions/848c6c80-5fe2-4cf4-8edd-f4e2529e8f31

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LPCompare_Relaxations

set_option autoImplicit false

namespace TEC295

lemma exists_between_fin {ι : Type} (s r : Finset ι) (L U : ι → ℝ)
    (h : ∀ q ∈ s, ∀ p ∈ r, L q ≤ U p) :
    ∃ t : ℝ, (∀ q ∈ s, L q ≤ t) ∧ ∀ p ∈ r, t ≤ U p := by
  by_cases hs : s.Nonempty
  · refine ⟨s.sup' hs L, fun q hq => Finset.le_sup' L hq, fun p hp => ?_⟩
    exact Finset.sup'_le hs L (fun q hq => h q hq p hp)
  · by_cases hr : r.Nonempty
    · exact ⟨r.inf' hr U, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => Finset.inf'_le U hp⟩
    · exact ⟨0, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => absurd ⟨p, hp⟩ hr⟩

/-- Theorem of alternatives (Fourier–Motzkin), variables indexed by `Fin n`. -/
theorem fm_alt (n : ℕ) : ∀ {ι : Type} [Fintype ι] (a : ι → Fin n → ℝ) (b : ι → ℝ),
    (∃ x : Fin n → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  induction n with
  | zero =>
    intro ι _ a b
    classical
    by_cases h : ∀ i, 0 ≤ b i
    · left; exact ⟨0, fun i => by simpa using h i⟩
    · right
      push Not at h
      obtain ⟨i, hi⟩ := h
      refine ⟨fun j => if j = i then 1 else 0, fun j => ?_, fun s => s.elim0, ?_⟩
      · dsimp only; split_ifs <;> norm_num
      · simpa using hi
  | succ n ih =>
    intro ι _ a b
    classical
    let W : ι ⊕ (ι × ι) → ι → ℝ := Sum.elim (fun z i => if a z 0 = 0 ∧ i = z then 1 else 0)
      (fun pq i => if 0 < a pq.1 0 ∧ a pq.2 0 < 0 then
        (if i = pq.1 then -a pq.2 0 else 0) + (if i = pq.2 then a pq.1 0 else 0) else 0)
    have hW0 : ∀ k i, 0 ≤ W k i := by
      intro k i
      rcases k with z | ⟨p, q⟩
      · simp only [W, Sum.elim_inl]; split_ifs <;> norm_num
      · simp only [W, Sum.elim_inr]
        split_ifs with h1 h2 h3 h3 <;> subst_vars <;> first | linarith [h1.1, h1.2] | norm_num
    let C : ι ⊕ (ι × ι) → Fin (n + 1) → ℝ := fun k s => ∑ i, W k i * a i s
    let D : ι ⊕ (ι × ι) → ℝ := fun k => ∑ i, W k i * b i
    have hC0 : ∀ k, C k 0 = 0 := by
      intro k
      rcases k with z | ⟨p, q⟩
      · by_cases hz : a z 0 = 0
        · simp [C, W, hz]
        · simp [C, W, hz]
      · by_cases h : 0 < a p 0 ∧ a q 0 < 0
        · simp only [C, W, Sum.elim_inr, if_pos h, add_mul, ite_mul, zero_mul,
            Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        · simp [C, W, h]
    rcases ih (fun k s => C k s.succ) D with ⟨y, hy⟩ | ⟨μ, hμ0, hμ1, hμ2⟩
    · left
      let r : ι → ℝ := fun i => b i - ∑ s : Fin n, a i s.succ * y s
      have key : ∀ k, 0 ≤ ∑ i, W k i * r i := by
        intro k
        have e : ∑ i, W k i * r i = D k - ∑ s, C k s.succ * y s := by
          simp only [r, D, C, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul,
            mul_assoc]
          congr 1
          exact Finset.sum_comm
        rw [e]; linarith [hy k]
      have kinl : ∀ z, a z 0 = 0 → 0 ≤ r z := by
        intro z hz
        have := key (Sum.inl z)
        simpa [W, hz] using this
      have kinr : ∀ p q, 0 < a p 0 → a q 0 < 0 → 0 ≤ -a q 0 * r p + a p 0 * r q := by
        intro p q hp hq
        have := key (Sum.inr (p, q))
        simp only [W, Sum.elim_inr, if_pos (And.intro hp hq), add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
        exact this
      obtain ⟨t, ht1, ht2⟩ := exists_between_fin (Finset.univ.filter (fun q => a q 0 < 0))
        (Finset.univ.filter (fun p => 0 < a p 0)) (fun q => r q / a q 0) (fun p => r p / a p 0)
        (by
          intro q hq p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq hp
          have h := kinr p q hp hq
          have e : -a q 0 * r p + a p 0 * r q =
              -(a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0)) := by
            have h1 : r p = (r p / a p 0) * a p 0 := (div_mul_cancel₀ _ hp.ne').symm
            have h2 : r q = (r q / a q 0) * a q 0 := (div_mul_cancel₀ _ hq.ne).symm
            set U := r p / a p 0
            set V := r q / a q 0
            rw [h1, h2]; ring
          by_contra hc
          push Not at hc
          have hpq : 0 < a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0) :=
            mul_pos (mul_pos hp (neg_pos.2 hq)) (sub_pos.2 hc)
          linarith)
      refine ⟨Fin.cons t y, fun i => ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have hr : r i = b i - ∑ s : Fin n, a i s.succ * y s := rfl
      suffices a i 0 * t ≤ r i by linarith
      rcases lt_trichotomy (a i 0) 0 with hneg | hz | hpos
      · have := ht1 i (by simp [hneg])
        rw [div_le_iff_of_neg hneg] at this
        linarith
      · rw [hz, zero_mul]; exact kinl i hz
      · have := ht2 i (by simp [hpos])
        rw [le_div_iff₀ hpos] at this
        linarith
    · right
      refine ⟨fun i => ∑ k, μ k * W k i, fun i => Finset.sum_nonneg
        (fun k _ => mul_nonneg (hμ0 k) (hW0 k i)), fun s => ?_, ?_⟩
      · have e : ∑ i, (∑ k, μ k * W k i) * a i s = ∑ k, μ k * C k s := by
          simp only [C, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]
        refine Fin.cases ?_ (fun s => ?_) s
        · simp [hC0]
        · exact hμ1 s
      · have e : ∑ i, (∑ k, μ k * W k i) * b i = ∑ k, μ k * D k := by
          simp only [D, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]; exact hμ2

/-- Theorem of alternatives over an arbitrary finite variable type. -/
theorem fm_alt' {σ ι : Type} [Fintype σ] [Fintype ι] (a : ι → σ → ℝ) (b : ι → ℝ) :
    (∃ x : σ → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  classical
  let e := Fintype.equivFin σ
  rcases fm_alt _ (fun i k => a i (e.symm k)) b with ⟨x, hx⟩ | ⟨l, h0, h1, h2⟩
  · left
    refine ⟨fun s => x (e s), fun i => ?_⟩
    rw [Fintype.sum_equiv e _ (fun k => a i (e.symm k) * x k) (fun s => by simp)]
    exact hx i
  · right
    exact ⟨l, h0, fun s => by simpa using h1 (e s), h2⟩

/-- Affine Farkas lemma for a system `x ≥ 0, a x ≤ b` whose solutions all have cost `≥ v`. -/
theorem farkas_nn {σ ι : Type} [Fintype σ] [Fintype ι] [DecidableEq ι] (a : ι → σ → ℝ)
    (b : ι → ℝ) (c : σ → ℝ) (v : ℝ)
    (hfeas : ∃ x : σ → ℝ, (∀ s, 0 ≤ x s) ∧ ∀ i, ∑ s, a i s * x s ≤ b i)
    (hbd : ∀ x : σ → ℝ, (∀ s, 0 ≤ x s) → (∀ i, ∑ s, a i s * x s ≤ b i) →
      v ≤ ∑ s, c s * x s) :
    ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, 0 ≤ c s + ∑ i, l i * a i s) ∧
      v + ∑ i, l i * b i ≤ 0 := by
  classical
  let A : (ι ⊕ σ ⊕ Unit) → ι → ℝ :=
    Sum.elim (fun i j => if j = i then -1 else 0) (Sum.elim (fun s j => - a j s) (fun _ j => b j))
  let B : (ι ⊕ σ ⊕ Unit) → ℝ := Sum.elim (fun _ => 0) (Sum.elim c (fun _ => -v))
  rcases fm_alt' A B with ⟨l, hl⟩ | ⟨w, hw0, hw1, hw2⟩
  · refine ⟨l, fun i => ?_, fun s => ?_, ?_⟩
    · have h := hl (Sum.inl i)
      simp [A, B] at h
      linarith
    · have h := hl (Sum.inr (Sum.inl s))
      simp only [A, B, Sum.elim_inl, Sum.elim_inr] at h
      have e : ∑ j, -a j s * l j = -∑ i, l i * a i s := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      linarith
    · have h := hl (Sum.inr (Sum.inr ()))
      simp only [A, B, Sum.elim_inl, Sum.elim_inr] at h
      have e : ∑ j, b j * l j = ∑ i, l i * b i :=
        Finset.sum_congr rfl (fun j _ => by ring)
      linarith
  · exfalso
    set z : σ → ℝ := fun s => w (Sum.inr (Sum.inl s)) with hz
    set t : ℝ := w (Sum.inr (Sum.inr ())) with ht
    have hz0 : ∀ s, 0 ≤ z s := fun s => hw0 _
    have ht0 : 0 ≤ t := hw0 _
    have hA : ∀ j, ∑ s, a j s * z s ≤ t * b j := by
      intro j
      have h := hw1 j
      simp only [A, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_ite, mul_neg, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.univ_unique,
        Finset.sum_singleton, Finset.sum_neg_distrib] at h
      have h0 := hw0 (Sum.inl j)
      have e : ∑ s, a j s * z s = ∑ s, w (Sum.inr (Sum.inl s)) * a j s :=
        Finset.sum_congr rfl (fun s _ => by simp only [hz]; ring)
      have e2 : w (Sum.inr (Sum.inr default)) = t := rfl
      rw [e2] at h
      linarith
    have hC : ∑ s, c s * z s < t * v := by
      have h := hw2
      simp only [B, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_zero,
        Finset.sum_const_zero, zero_add, Finset.univ_unique, Finset.sum_singleton, mul_neg] at h
      have e : ∑ s, c s * z s = ∑ s, w (Sum.inr (Sum.inl s)) * c s :=
        Finset.sum_congr rfl (fun s _ => by simp only [hz]; ring)
      have e2 : w (Sum.inr (Sum.inr default)) = t := rfl
      rw [e2] at h
      linarith
    rcases lt_or_eq_of_le ht0 with htp | ht0'
    · -- scale down
      have h := hbd (fun s => z s / t) (fun s => div_nonneg (hz0 s) ht0) (fun i => by
        have e : ∑ s, a i s * (z s / t) = (∑ s, a i s * z s) / t := by
          rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun s _ => by ring)
        rw [e, div_le_iff₀ htp]; linarith [hA i])
      have e : ∑ s, c s * (z s / t) = (∑ s, c s * z s) / t := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun s _ => by ring)
      rw [e, le_div_iff₀ htp] at h
      linarith
    · -- recession direction
      rw [← ht0'] at hA hC
      simp only [zero_mul] at hA hC
      obtain ⟨x0, hx00, hx0⟩ := hfeas
      set S := ∑ s, c s * z s with hS
      set D := |∑ s, c s * x0 s - v| with hD
      have hD0 : 0 ≤ D := abs_nonneg _
      set K := (D + 1) / (-S) with hK
      have hKpos : 0 ≤ K := div_nonneg (by linarith) (by linarith)
      have hKS : K * S = -(D + 1) := by
        rw [hK, div_mul_eq_mul_div, div_eq_iff (by linarith)]; ring
      have h := hbd (fun s => x0 s + K * z s)
        (fun s => add_nonneg (hx00 s) (mul_nonneg hKpos (hz0 s))) (fun i => by
          have e : ∑ s, a i s * (x0 s + K * z s) = ∑ s, a i s * x0 s + K * ∑ s, a i s * z s := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun s _ => by ring)
          rw [e]; nlinarith [hA i, hx0 i])
      have e : ∑ s, c s * (x0 s + K * z s) = ∑ s, c s * x0 s + K * S := by
        rw [hS, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun s _ => by ring)
      rw [e, hKS] at h
      have := le_abs_self (∑ s, c s * x0 s - v)
      linarith

/-- The same lemma for rows given as linear functionals, in Lagrangian form. -/
theorem farkas_lin {σ ι : Type} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
    (row : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (b : ι → ℝ) (c : (σ → ℝ) →ₗ[ℝ] ℝ) (v : ℝ)
    (hfeas : ∃ x : σ → ℝ, (∀ s, 0 ≤ x s) ∧ ∀ i, row i x ≤ b i)
    (hbd : ∀ x : σ → ℝ, (∀ s, 0 ≤ x s) → (∀ i, row i x ≤ b i) → v ≤ c x) :
    ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧
      (∀ s, 0 ≤ c (fun j => if s = j then 1 else 0)
        + ∑ i, l i * row i (fun j => if s = j then 1 else 0)) ∧
      (∀ x : σ → ℝ, (∀ s, 0 ≤ x s) → v ≤ c x + ∑ i, l i * (row i x - b i)) := by
  have key : ∀ (f : (σ → ℝ) →ₗ[ℝ] ℝ) (x : σ → ℝ),
      ∑ s, f (fun j => if s = j then 1 else 0) * x s = f x := by
    intro f x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    exact Finset.sum_congr rfl (fun s _ => by rw [smul_eq_mul, mul_comm])
  obtain ⟨l, hl0, hl1, hl2⟩ := farkas_nn (fun i s => row i (fun j => if s = j then 1 else 0)) b
    (fun s => c (fun j => if s = j then 1 else 0)) v
    (by
      obtain ⟨x, hx0, hx⟩ := hfeas
      exact ⟨x, hx0, fun i => by rw [key]; exact hx i⟩)
    (fun x hx0 hx => by rw [key]; exact hbd x hx0 (fun i => by rw [← key]; exact hx i))
  refine ⟨l, hl0, hl1, fun x hx0 => ?_⟩
  have h1 : ∑ s, (c (fun j => if s = j then 1 else 0)
        + ∑ i, l i * row i (fun j => if s = j then 1 else 0)) * x s
      = c x + ∑ i, l i * row i x := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, key c x]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← key (row i) x, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  have h2 : 0 ≤ ∑ s, (c (fun j => if s = j then 1 else 0)
        + ∑ i, l i * row i (fun j => if s = j then 1 else 0)) * x s :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (hl1 s) (hx0 s))
  have h3 : ∑ i, l i * (row i x - b i) = ∑ i, l i * row i x - ∑ i, l i * b i := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h3]
  linarith

section Enc

open TwoEchelonCVRP.LPCompare Finset

variable {I : Instance} (RS : RouteSystem I)

/-- Variables of `LF`: `x_l`, `y_r`, `q_{rk}`. -/
abbrev Var := RS.SR ⊕ RS.FR ⊕ (RS.FR × Fin I.ns)

/-- Constraint labels of `LF` in `≤` form. -/
abbrev Con := Fin I.nc ⊕ Fin I.nc ⊕ Fin I.ns ⊕ Unit ⊕ Fin I.ns ⊕ Unit ⊕ Fin I.ns ⊕ Fin I.ns ⊕
  RS.FR ⊕ RS.FR ⊕ (RS.FR × Fin I.ns)

def px (l : RS.SR) : (Var RS → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (Sum.inl l)
def py (r : RS.FR) : (Var RS → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (Sum.inr (Sum.inl r))
def pq (r : RS.FR) (k : Fin I.ns) : (Var RS → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj (Sum.inr (Sum.inr (r, k)))

@[simp] lemma px_apply (l : RS.SR) (z : Var RS → ℝ) : px RS l z = z (Sum.inl l) := rfl
@[simp] lemma py_apply (r : RS.FR) (z : Var RS → ℝ) : py RS r z = z (Sum.inr (Sum.inl r)) := rfl
@[simp] lemma pq_apply (r : RS.FR) (k : Fin I.ns) (z : Var RS → ℝ) :
    pq RS r k z = z (Sum.inr (Sum.inr (r, k))) := rfl

def cst : (Var RS → ℝ) →ₗ[ℝ] ℝ := ∑ l, RS.c l • px RS l + ∑ r, RS.g r • py RS r

def rowE (i : Fin I.nc) : (Var RS → ℝ) →ₗ[ℝ] ℝ :=
  ∑ l ∈ univ.filter (fun l => i ∈ RS.cust l), px RS l
def rowS (k : Fin I.ns) : (Var RS → ℝ) →ₗ[ℝ] ℝ :=
  ∑ l ∈ univ.filter (fun l => RS.sat l = k), px RS l
def rowW (k : Fin I.ns) : (Var RS → ℝ) →ₗ[ℝ] ℝ :=
  ∑ l ∈ univ.filter (fun l => RS.sat l = k), (RS.w l : ℝ) • px RS l
def rowBal (k : Fin I.ns) : (Var RS → ℝ) →ₗ[ℝ] ℝ :=
  ∑ r ∈ univ.filter (fun r => k ∈ RS.R1 r), pq RS r k - rowW RS k
def rowCap (r : RS.FR) : (Var RS → ℝ) →ₗ[ℝ] ℝ :=
  ∑ k ∈ RS.R1 r, pq RS r k - (I.Q1 : ℝ) • py RS r
def rowZ (p : RS.FR × Fin I.ns) : (Var RS → ℝ) →ₗ[ℝ] ℝ :=
  (if p.2 ∈ RS.R1 p.1 then (0 : ℝ) else 1) • pq RS p.1 p.2

@[simp] lemma cst_apply (z : Var RS → ℝ) :
    cst RS z = ∑ l, RS.c l * z (Sum.inl l) + ∑ r, RS.g r * z (Sum.inr (Sum.inl r)) := by
  simp [cst]
@[simp] lemma rowE_apply (i : Fin I.nc) (z : Var RS → ℝ) :
    rowE RS i z = ∑ l ∈ univ.filter (fun l => i ∈ RS.cust l), z (Sum.inl l) := by
  simp [rowE]
@[simp] lemma rowS_apply (k : Fin I.ns) (z : Var RS → ℝ) :
    rowS RS k z = ∑ l ∈ univ.filter (fun l => RS.sat l = k), z (Sum.inl l) := by
  simp [rowS]
@[simp] lemma rowW_apply (k : Fin I.ns) (z : Var RS → ℝ) :
    rowW RS k z = ∑ l ∈ univ.filter (fun l => RS.sat l = k), (RS.w l : ℝ) * z (Sum.inl l) := by
  simp [rowW]
@[simp] lemma rowBal_apply (k : Fin I.ns) (z : Var RS → ℝ) :
    rowBal RS k z = ∑ r ∈ univ.filter (fun r => k ∈ RS.R1 r), z (Sum.inr (Sum.inr (r, k)))
      - ∑ l ∈ univ.filter (fun l => RS.sat l = k), (RS.w l : ℝ) * z (Sum.inl l) := by
  simp [rowBal]
@[simp] lemma rowCap_apply (r : RS.FR) (z : Var RS → ℝ) :
    rowCap RS r z = ∑ k ∈ RS.R1 r, z (Sum.inr (Sum.inr (r, k)))
      - (I.Q1 : ℝ) * z (Sum.inr (Sum.inl r)) := by
  simp [rowCap]
@[simp] lemma rowZ_apply (p : RS.FR × Fin I.ns) (z : Var RS → ℝ) :
    rowZ RS p z = (if p.2 ∈ RS.R1 p.1 then (0 : ℝ) else 1) * z (Sum.inr (Sum.inr p)) := by
  by_cases h : p.2 ∈ RS.R1 p.1 <;> simp [rowZ, h]
@[simp] lemma sumx_apply (z : Var RS → ℝ) : (∑ l, px RS l) z = ∑ l, z (Sum.inl l) := by
  simp
@[simp] lemma sumy_apply (z : Var RS → ℝ) :
    (∑ r, py RS r) z = ∑ r, z (Sum.inr (Sum.inl r)) := by
  simp

def row : Con RS → (Var RS → ℝ) →ₗ[ℝ] ℝ :=
  Sum.elim (rowE RS) (Sum.elim (fun i => - rowE RS i) (Sum.elim (rowS RS)
  (Sum.elim (fun _ => ∑ l, px RS l) (Sum.elim (rowW RS) (Sum.elim (fun _ => ∑ r, py RS r)
  (Sum.elim (rowBal RS) (Sum.elim (fun k => - rowBal RS k) (Sum.elim (rowCap RS)
  (Sum.elim (py RS) (rowZ RS))))))))))

def rhs : Con RS → ℝ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun _ => -1) (Sum.elim (fun k => (I.m k : ℝ))
  (Sum.elim (fun _ => (I.m2 : ℝ)) (Sum.elim (fun k => (I.B k : ℝ))
  (Sum.elim (fun _ => (I.m1 : ℝ)) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0)
  (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0))))))))))

def X (z : Var RS → ℝ) : LFPoint RS :=
  ⟨fun l => z (Sum.inl l), fun r => z (Sum.inr (Sum.inl r)),
    fun r k => z (Sum.inr (Sum.inr (r, k)))⟩

def Zp (p : LFPoint RS) : Var RS → ℝ := Sum.elim p.x (Sum.elim p.y (fun pr => p.qd pr.1 pr.2))

lemma cst_X (z : Var RS → ℝ) : cst RS z = costLF (X RS z) := by
  simp [costLF, X]

lemma Zp_nonneg (p : LFPoint RS) (hp : IsFeasibleLF p) : ∀ s, 0 ≤ Zp RS p s := by
  obtain ⟨-, -, -, -, -, -, -, h9, h10, h11, -⟩ := hp
  rintro (l | r | pr)
  · exact (h9 l).1
  · exact (h10 r).1
  · exact h11 pr.1 pr.2

lemma rows_of (p : LFPoint RS) (hp : IsFeasibleLF p) : ∀ i, row RS i (Zp RS p) ≤ rhs RS i := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hp
  rintro (i | i | k | u | k | u | k | k | r | r | pr)
  · simp [row, rhs, Zp]; linarith [h2 i]
  · simp [row, rhs, Zp]; linarith [h2 i]
  · simp [row, rhs, Zp]; linarith [h3 k]
  · simp [row, rhs, Zp]; linarith [h4]
  · simp [row, rhs, Zp]; linarith [h5 k]
  · simp [row, rhs, Zp]; linarith [h6]
  · simp [row, rhs, Zp]; linarith [h7 k]
  · simp [row, rhs, Zp]; linarith [h7 k]
  · simp [row, rhs, Zp]; linarith [h8 r]
  · simp [row, rhs, Zp]; linarith [(h10 r).2]
  · by_cases h : pr.2 ∈ RS.R1 pr.1
    · simp [row, rhs, Zp, h]
    · simp [row, rhs, Zp, h, h12 pr.1 pr.2 h]

lemma feas_of (z : Var RS → ℝ) (hz : ∀ s, 0 ≤ z s) (h : ∀ i, row RS i z ≤ rhs RS i) :
    IsFeasibleLF (X RS z) := by
  have hE1 := fun i => h (Sum.inl i)
  have hE2 := fun i => h (Sum.inr (Sum.inl i))
  have h3 := fun k => h (Sum.inr (Sum.inr (Sum.inl k)))
  have h4 := h (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))
  have h5 := fun k => h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
  have h6 := h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))))
  have h7a := fun k => h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))))
  have h7b := fun k =>
    h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))))
  have h8 := fun r =>
    h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl r)))))))))
  have hy := fun r =>
    h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (Sum.inl r))))))))))
  have hzq := fun pr =>
    h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (Sum.inr pr))))))))))
  simp only [row, rhs, Sum.elim_inl, Sum.elim_inr, LinearMap.neg_apply, rowE_apply, rowS_apply,
    rowW_apply, rowBal_apply, rowCap_apply, rowZ_apply, sumx_apply, sumy_apply] at hE1 hE2 h3 h4 h5 h6 h7a h7b h8 hy hzq
  have hx1 : ∀ i, ∑ l ∈ univ.filter (fun l => i ∈ RS.cust l), z (Sum.inl l) = 1 :=
    fun i => le_antisymm (hE1 i) (by linarith [hE2 i])
  refine ⟨fun i => hx1 i, fun k => h3 k, h4, fun k => h5 k, h6,
    fun k => by have := h7a k; have := h7b k; simp only [X]; linarith,
    fun r => by have := h8 r; simp only [X]; linarith,
    fun l => ⟨hz _, ?_⟩, fun r => ⟨hz _, hy r⟩, fun r k => hz _, fun r k hk => ?_⟩
  · obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil (RS.tour2 l) (RS.tour2_ne l)
    have hil : i ∈ RS.cust l := List.mem_toFinset.mpr hi
    have hle := Finset.single_le_sum (f := fun l' => z (Sum.inl l'))
      (s := univ.filter (fun l' => i ∈ RS.cust l')) (fun l' _ => hz _)
      (show l ∈ univ.filter (fun l' => i ∈ RS.cust l') by simp [hil])
    simp only [X]
    linarith [hx1 i]
  · have := hzq (r, k)
    simp only [hk, if_false, one_mul] at this
    simp only [X]
    exact le_antisymm this (hz _)

lemma sum_a (l : RS.SR) (f : Fin I.nc → ℝ) :
    ∑ i, (RS.a i l : ℝ) * f i = ∑ i ∈ RS.cust l, f i := by
  classical
  have hnd := RS.tour2_nodup l
  rw [← Finset.sum_subset (Finset.subset_univ (RS.cust l)) (fun i _ hi => by
      have : RS.a i l = 0 := List.count_eq_zero.mpr (fun hm => hi (List.mem_toFinset.mpr hm))
      simp [this])]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have : RS.a i l = 1 := List.count_eq_one_of_mem hnd (List.mem_toFinset.mp hi)
  simp [this]

lemma w_cast (l : RS.SR) : (RS.w l : ℝ) = ∑ i ∈ RS.cust l, (I.q i : ℝ) := by
  simp [RouteSystem.w]

end Enc

section Part1

open TwoEchelonCVRP.LPCompare Finset

set_option maxHeartbeats 1000000 in
theorem part1 (I : Instance) (RS : RouteSystem I) (hF : ∃ p : LFPoint RS, IsFeasibleLF p) :
    ∃ (beta : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (mu : Fin I.ns → ℝ) (mu0 : ℝ),
      Admissible RS beta lam mu mu0 ∧ zLF RS ≤ zRF RS beta lam mu mu0 := by
  classical
  obtain ⟨p0, hp0⟩ := hF
  set Kc : ℝ := ∑ l, |RS.c l| + ∑ r, |RS.g r| with hKc
  have hlow : ∀ p : LFPoint RS, IsFeasibleLF p → -Kc ≤ costLF p := by
    intro p hp
    obtain ⟨-, -, -, -, -, -, -, h9, h10, -, -⟩ := hp
    have a1 : ∀ l, -|RS.c l| ≤ RS.c l * p.x l := fun l => by
      have hx0 := (h9 l).1
      have hx1 := (h9 l).2
      nlinarith [mul_nonneg (by linarith [neg_abs_le (RS.c l)] : 0 ≤ RS.c l + |RS.c l|) hx0,
        mul_nonneg (abs_nonneg (RS.c l)) (sub_nonneg.2 hx1)]
    have a2 : ∀ r, -|RS.g r| ≤ RS.g r * p.y r := fun r => by
      have hy0 := (h10 r).1
      have hy1 := (h10 r).2
      nlinarith [mul_nonneg (by linarith [neg_abs_le (RS.g r)] : 0 ≤ RS.g r + |RS.g r|) hy0,
        mul_nonneg (abs_nonneg (RS.g r)) (sub_nonneg.2 hy1)]
    have s1 := Finset.sum_le_sum (fun l (_ : l ∈ (univ : Finset RS.SR)) => a1 l)
    have s2 := Finset.sum_le_sum (fun r (_ : r ∈ (univ : Finset RS.FR)) => a2 r)
    simp only [Finset.sum_neg_distrib] at s1 s2
    unfold costLF
    linarith
  have hle : ∀ p : LFPoint RS, IsFeasibleLF p → zLF RS ≤ ((costLF p : ℝ) : EReal) := fun p hp =>
    iInf_le (fun q : {q : LFPoint RS // IsFeasibleLF q} => ((costLF q.1 : ℝ) : EReal)) ⟨p, hp⟩
  have hne_bot : zLF RS ≠ ⊥ := by
    have h : ((-Kc : ℝ) : EReal) ≤ zLF RS :=
      le_iInf (fun q => EReal.coe_le_coe_iff.2 (hlow q.1 q.2))
    intro h'
    rw [h'] at h
    exact EReal.coe_ne_bot _ (le_bot_iff.1 h)
  have hne_top : zLF RS ≠ ⊤ := by
    intro h'
    have h := hle p0 hp0
    rw [h'] at h
    exact EReal.coe_ne_top _ (top_le_iff.1 h)
  set v : ℝ := (zLF RS).toReal with hvdef
  have hv : zLF RS = (v : EReal) := (EReal.coe_toReal hne_top hne_bot).symm
  have hvle : ∀ p : LFPoint RS, IsFeasibleLF p → v ≤ costLF p := fun p hp => by
    have h := hle p hp
    rw [hv] at h
    exact EReal.coe_le_coe_iff.1 h
  obtain ⟨l, hl0, hcoef, hlag⟩ := farkas_lin (row RS) (rhs RS) (cst RS) v
    ⟨Zp RS p0, Zp_nonneg RS p0 hp0, rows_of RS p0 hp0⟩
    (fun z hz hr => by rw [cst_X]; exact hvle _ (feas_of RS z hz hr))
  -- the multipliers
  obtain ⟨lam, hlam⟩ : ∃ f : Fin I.nc → ℝ, ∀ i, f i = l (Sum.inr (Sum.inl i)) - l (Sum.inl i) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨mu, hmu⟩ : ∃ f : Fin I.ns → ℝ, ∀ k, f k = - l (Sum.inr (Sum.inr (Sum.inl k))) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨mu0, hmu0⟩ : ∃ t : ℝ, t = - l (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))) :=
    ⟨_, rfl⟩
  obtain ⟨a5, ha5⟩ : ∃ f : Fin I.ns → ℝ,
      ∀ k, f k = l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))) := ⟨_, fun _ => rfl⟩
  obtain ⟨sg, hsg⟩ : ∃ f : Fin I.ns → ℝ,
      ∀ k, f k = l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))))
        - l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))))) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨beta, hbeta⟩ : ∃ f : Fin I.nc → Fin I.ns → ℝ,
      ∀ i k, f i k = (I.q i : ℝ) * (sg k - a5 k) := ⟨_, fun _ _ => rfl⟩
  refine ⟨beta, lam, mu, mu0, ⟨fun k => by rw [hmu]; linarith [hl0 (Sum.inr (Sum.inr (Sum.inl k)))],
    by rw [hmu0]; linarith [hl0 (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))], ?_⟩, ?_⟩
  · -- inequalities (12): the reduced cost of `x_l` is nonnegative
    intro l0
    have h := hcoef (Sum.inl l0)
    simp only [Fintype.sum_sum_type] at h
    set e : Var RS → ℝ := fun j => if Sum.inl l0 = j then 1 else 0 with he
    have b0 : cst RS e = RS.c l0 := by simp [he]
    have b1 : ∑ i, l (Sum.inl i) * row RS (Sum.inl i) e = ∑ i ∈ RS.cust l0, l (Sum.inl i) := by
      simp [row, he]
    have b2 : ∑ i, l (Sum.inr (Sum.inl i)) * row RS (Sum.inr (Sum.inl i)) e
        = - ∑ i ∈ RS.cust l0, l (Sum.inr (Sum.inl i)) := by
      simp [row, he]
    have b3 : ∑ k, l (Sum.inr (Sum.inr (Sum.inl k))) * row RS (Sum.inr (Sum.inr (Sum.inl k))) e
        = l (Sum.inr (Sum.inr (Sum.inl (RS.sat l0)))) := by
      simp [row, he]
    have b4 : ∑ u, l (Sum.inr (Sum.inr (Sum.inr (Sum.inl u))))
        * row RS (Sum.inr (Sum.inr (Sum.inr (Sum.inl u)))) e
        = l (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))) := by
      simp [row, he]
    have b5 : ∑ k, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
        * row RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))) e
        = a5 (RS.sat l0) * (RS.w l0 : ℝ) := by
      simp [row, he, ha5]
    have b6 : ∑ u, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl u))))))
        * row RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl u)))))) e = 0 := by
      simp [row, he]
    have b7 : ∑ k, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))))
        * row RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))) e
        + ∑ k, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))))
        * row RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))))) e
        = - sg (RS.sat l0) * (RS.w l0 : ℝ) := by
      simp [row, he, hsg]
      ring
    have b8 : ∑ r, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl r)))))))))
        * row RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl r))))))))) e = 0 := by
      simp [row, he]
    have b9 : ∑ r, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inl r))))))))))
        * row RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inl r)))))))))) e = 0 := by
      simp [row, he]
    have b10 : ∑ pr, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inr pr))))))))))
        * row RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inr pr)))))))))) e = 0 := by
      simp [row, he]
    have hlhs : ∑ i, (RS.a i l0 : ℝ) * beta i (RS.sat l0)
        = (sg (RS.sat l0) - a5 (RS.sat l0)) * (RS.w l0 : ℝ) := by
      rw [sum_a, w_cast, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [hbeta]; ring)
    have hrhs : ∑ i, (RS.a i l0 : ℝ) * lam i
        = ∑ i ∈ RS.cust l0, l (Sum.inr (Sum.inl i)) - ∑ i ∈ RS.cust l0, l (Sum.inl i) := by
      rw [sum_a, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => hlam i)
    rw [hlhs, hrhs, hmu, hmu0]
    linarith
  · -- every `RF` solution costs at least `v`
    rw [hv]
    refine le_iInf (fun s => ?_)
    obtain ⟨s, hs⟩ := s
    obtain ⟨h14, h15, h16, h6, h8, h11⟩ := hs
    refine EReal.coe_le_coe_iff.2 ?_
    set z : Var RS → ℝ := Sum.elim (fun _ => 0)
      (Sum.elim (fun r => ((s.y r).toNat : ℝ)) (fun pr => (s.qd pr.1 pr.2 : ℝ))) with hz
    have hz0 : ∀ j, 0 ≤ z j := by
      rintro (l | r | pr) <;> simp [hz]
    have h := hlag z hz0
    simp only [Fintype.sum_sum_type] at h
    set D : Fin I.ns → ℝ := fun k => ∑ i, (I.q i : ℝ) * ((s.xi i k).toNat : ℝ) with hD
    have F15 : ∀ k, ∑ r ∈ univ.filter (fun r => k ∈ RS.R1 r), (s.qd r k : ℝ) = D k := by
      intro k
      have := congrArg (fun n : ℕ => (n : ℝ)) (h15 k)
      simpa [hD] using this
    have F16 : ∀ k, D k ≤ (I.B k : ℝ) := by
      intro k
      have := (Nat.cast_le (α := ℝ)).2 (h16 k)
      simpa [hD] using this
    have F6 : ∑ r, ((s.y r).toNat : ℝ) ≤ (I.m1 : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).2 h6
      simpa using this
    have F8 : ∀ r, ∑ k ∈ RS.R1 r, (s.qd r k : ℝ) ≤ (I.Q1 : ℝ) * ((s.y r).toNat : ℝ) := by
      intro r
      have := (Nat.cast_le (α := ℝ)).2 (h8 r)
      simpa using this
    have Fy : ∀ r, ((s.y r).toNat : ℝ) ≤ 1 := by
      intro r
      cases s.y r <;> simp
    have c0 : cst RS z = ∑ r, RS.g r * ((s.y r).toNat : ℝ) := by simp [hz]
    have c12 : ∑ i, l (Sum.inl i) * (row RS (Sum.inl i) z - rhs RS (Sum.inl i))
        + ∑ i, l (Sum.inr (Sum.inl i)) * (row RS (Sum.inr (Sum.inl i)) z
          - rhs RS (Sum.inr (Sum.inl i))) = ∑ i, lam i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [row, rhs, hz, hlam] <;> ring
    have c3 : ∑ k, l (Sum.inr (Sum.inr (Sum.inl k))) * (row RS (Sum.inr (Sum.inr (Sum.inl k))) z
        - rhs RS (Sum.inr (Sum.inr (Sum.inl k)))) = ∑ k, (I.m k : ℝ) * mu k := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [row, rhs, hz, hmu] <;> ring
    have c4 : ∑ u, l (Sum.inr (Sum.inr (Sum.inr (Sum.inl u))))
        * (row RS (Sum.inr (Sum.inr (Sum.inr (Sum.inl u)))) z
          - rhs RS (Sum.inr (Sum.inr (Sum.inr (Sum.inl u))))) = (I.m2 : ℝ) * mu0 := by
      simp [row, rhs, hz, hmu0] <;> ring
    have c5 : ∑ k, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
        * (row RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))) z
          - rhs RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))
        ≤ - ∑ k, a5 k * D k := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum (fun k _ => ?_)
      have h0 := hl0 (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
      have := F16 k
      simp [row, rhs, hz, ha5]
      nlinarith
    have c6 : ∑ u, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl u))))))
        * (row RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl u)))))) z
          - rhs RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl u))))))) ≤ 0 := by
      have h0 := hl0 (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))))
      simp [row, rhs, hz]
      nlinarith
    have c7 : ∑ k, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))))
        * (row RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))) z
          - rhs RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))))
        + ∑ k, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))))
        * (row RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))))
            z - rhs RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
            (Sum.inl k)))))))))
        = ∑ k, sg k * D k := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have := F15 k
      simp [row, rhs, hz, hsg]
      rw [this]
      ring
    have c8 : ∑ r, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl r)))))))))
        * (row RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (Sum.inl r))))))))) z - rhs RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (Sum.inr (Sum.inr (Sum.inl r)))))))))) ≤ 0 := by
      refine Finset.sum_nonpos (fun r _ => ?_)
      have h0 := hl0 (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl r)))))))))
      have := F8 r
      simp [row, rhs, hz]
      nlinarith
    have c9 : ∑ r, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inl r))))))))))
        * (row RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (Sum.inr (Sum.inl r)))))))))) z - rhs RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl r))))))))))) ≤ 0 := by
      refine Finset.sum_nonpos (fun r _ => ?_)
      have h0 := hl0 (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inl r))))))))))
      have := Fy r
      simp [row, rhs, hz]
      nlinarith
    have c10 : ∑ pr, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inr pr))))))))))
        * (row RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (Sum.inr (Sum.inr pr)))))))))) z - rhs RS (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr pr))))))))))) = 0 := by
      refine Finset.sum_eq_zero (fun pr _ => ?_)
      by_cases hk : pr.2 ∈ RS.R1 pr.1
      · simp [row, rhs, hz, hk]
      · simp [row, rhs, hz, hk, h11 pr.1 pr.2 hk]
    have cobj : ∑ k, ∑ i, beta i k * ((s.xi i k).toNat : ℝ) = ∑ k, (sg k - a5 k) * D k := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hD, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [hbeta]; ring)
    have csub : ∑ k, (sg k - a5 k) * D k = ∑ k, sg k * D k - ∑ k, a5 k * D k := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    unfold objRF
    rw [cobj, csub]
    linarith

end Part1

section Part2

open TwoEchelonCVRP.LPCompare Finset

/-- One satellite, one customer of demand 1, all travel costs 1, `Q₁ = 2`, `Q₂ = 1`. -/
abbrev I0 : Instance where
  ns := 1
  nc := 1
  d := fun _ _ => 1
  d_symm := fun _ _ => rfl
  q := fun _ => 1
  q_pos := fun _ => Nat.one_pos
  Q1 := 2
  Q2 := 1
  Q2_pos := Nat.one_pos
  Q2_lt_Q1 := by norm_num
  m1 := 1
  m2 := 1
  m := fun _ => 1
  m2_le := by simp
  B := fun _ => 1
  H := fun _ => 0

/-- One first-level route `(0, 1, 0)` and one second-level route `(1, c, 1)`. -/
abbrev RS0 : RouteSystem I0 where
  FR := Unit
  tour1 := fun _ => [0]
  tour1_ne := fun _ => by simp
  tour1_nodup := fun _ => by simp
  SR := Unit
  sat := fun _ => 0
  tour2 := fun _ => [0]
  tour2_ne := fun _ => by simp
  tour2_nodup := fun _ => by simp
  load_le := fun _ => by decide

lemma cwc1 {V : Type} (d : V → V → ℝ) (s v : V) :
    TwoEchelonCVRP.LowerBound.closedWalkCost d s [v] = d s v + d v s := by
  simp [TwoEchelonCVRP.LowerBound.closedWalkCost]

lemma RS0_R1 (k : Fin I0.ns) (r : RS0.FR) : k ∈ RS0.R1 r := by
  fin_cases k; simp [RouteSystem.R1]

lemma RS0_R1_eq (r : RS0.FR) : RS0.R1 r = univ := by
  ext k; exact iff_of_true (RS0_R1 _ _) (Finset.mem_univ _)

lemma RS0_cust (i : Fin I0.nc) (l : RS0.SR) : i ∈ RS0.cust l := by
  fin_cases i; simp [RouteSystem.cust]

lemma RS0_a (i : Fin I0.nc) (l : RS0.SR) : RS0.a i l = 1 := by
  fin_cases i; simp [RouteSystem.a]

lemma RS0_w (l : RS0.SR) : RS0.w l = 1 := by cases l; decide

lemma RS0_g (r : RS0.FR) : RS0.g r = 2 := by
  show TwoEchelonCVRP.LowerBound.closedWalkCost I0.d _ [_] = 2
  rw [cwc1]; norm_num

lemma RS0_c (l : RS0.SR) : RS0.c l = 2 := by
  show TwoEchelonCVRP.LowerBound.closedWalkCost I0.d _ [_] + I0.H 0 * (RS0.w l : ℝ) = 2
  rw [cwc1]; norm_num

theorem part2 :
    ∃ (I : Instance) (RS : RouteSystem I) (beta : Fin I.nc → Fin I.ns → ℝ)
      (lam : Fin I.nc → ℝ) (mu : Fin I.ns → ℝ) (mu0 : ℝ),
      Admissible RS beta lam mu mu0 ∧ zLF RS < zRF RS beta lam mu mu0 ∧
        zRF RS beta lam mu mu0 < ⊤ := by
  refine ⟨I0, RS0, fun _ _ => 2, fun _ => 0, fun _ => 0, 0, ?_, ?_⟩
  · refine ⟨fun _ => le_rfl, le_rfl, fun l => ?_⟩
    simp [RS0_a, RS0_c]
  · -- an `LF` point of cost 3
    let p : LFPoint RS0 := ⟨fun _ => 1, fun _ => 1 / 2, fun _ _ => 1⟩
    have hp : IsFeasibleLF p := by
      refine ⟨fun i => ?_, fun k => ?_, ?_, fun k => ?_, ?_, fun k => ?_, fun r => ?_,
        fun l => ?_, fun r => ?_, fun r k => ?_, fun r k hk => ?_⟩
      · fin_cases i <;> simp [p, RouteSystem.cust]
      · fin_cases k <;> simp [p]
      · simp [p]
      · fin_cases k <;> simp [p, RS0_w]
      · simp [p]; norm_num
      · fin_cases k <;> simp [p, RS0_w, RouteSystem.R1]
      · simp [p, RS0_R1_eq]
      · simp [p]
      · simp [p]; norm_num
      · simp [p]
      · exact absurd (RS0_R1 k r) hk
    have hcost : costLF p = 3 := by
      simp [costLF, p, RS0_c, RS0_g]; norm_num
    have hLF : zLF RS0 ≤ ((3 : ℝ) : EReal) := by
      rw [← hcost]
      exact iInf_le (fun q : {q : LFPoint RS0 // IsFeasibleLF q} => ((costLF q.1 : ℝ) : EReal))
        ⟨p, hp⟩
    -- every `RF` solution costs 4
    have hRF : ((4 : ℝ) : EReal) ≤ zRF RS0 (fun _ _ => 2) (fun _ => 0) (fun _ => 0) 0 := by
      refine le_iInf (fun s => ?_)
      obtain ⟨s, h14, h15, h16, h6, h8, h11⟩ := s
      refine EReal.coe_le_coe_iff.2 ?_
      have hx : (s.xi 0 0).toNat = 1 := by simpa using h14 0
      have hq : s.qd () 0 = (s.xi 0 0).toNat := by
        have := h15 0
        simp [RouteSystem.R1] at this
        simpa using this
      have hy : s.qd () 0 ≤ 2 * (s.y ()).toNat := by
        have := h8 ()
        simp [RS0_R1_eq] at this
        simpa using this
      have hxv : s.xi 0 0 = true := by
        cases h : s.xi 0 0
        · rw [h] at hx; simp at hx
        · rfl
      have hyv : s.y () = true := by
        cases h : s.y ()
        · rw [h] at hy; rw [hq, hxv] at hy; simp at hy
        · rfl
      have hobj : objRF (fun _ _ => (2 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) 0 s = 4 := by
        simp [objRF, RS0_g, hxv, hyv]
        norm_num
      rw [hobj]
    let s0 : RFSol RS0 := ⟨fun _ _ => true, fun _ => true, fun _ _ => 1⟩
    have hs0 : IsFeasibleRF s0 := by
      refine ⟨fun i => ?_, fun k => ?_, fun k => ?_, ?_, fun r => ?_, fun r k hk => ?_⟩
      · simp [s0]
      · fin_cases k <;> simp [s0, RouteSystem.R1]
      · fin_cases k <;> simp [s0]
      · simp [s0]
      · simp [s0, RS0_R1_eq]
      · exact absurd (RS0_R1 k r) hk
    have hRF' : zRF RS0 (fun _ _ => 2) (fun _ => 0) (fun _ => 0) 0 ≤ ((4 : ℝ) : EReal) := by
      have h4 : objRF (fun _ _ => (2 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) 0 s0 = 4 := by
        simp [objRF, s0, RS0_g]; norm_num
      rw [← h4]
      exact iInf_le (fun s : {s : RFSol RS0 // IsFeasibleRF s} =>
        ((objRF (fun _ _ => (2 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) 0 s.1 : ℝ) : EReal))
        ⟨s0, hs0⟩
    refine ⟨lt_of_le_of_lt hLF (lt_of_lt_of_le ?_ hRF), lt_of_le_of_lt hRF' (EReal.coe_lt_top 4)⟩
    exact EReal.coe_lt_coe_iff.2 (by norm_num)

end Part2

end TEC295

open TwoEchelonCVRP.LPCompare in
theorem solution :
    (∀ (I : Instance) (RS : RouteSystem I), (∃ p : LFPoint RS, IsFeasibleLF p) →
      ∃ (beta : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (mu : Fin I.ns → ℝ) (mu0 : ℝ),
        Admissible RS beta lam mu mu0 ∧ zLF RS ≤ zRF RS beta lam mu mu0) ∧
    (∃ (I : Instance) (RS : RouteSystem I) (beta : Fin I.nc → Fin I.ns → ℝ)
      (lam : Fin I.nc → ℝ) (mu : Fin I.ns → ℝ) (mu0 : ℝ),
      Admissible RS beta lam mu mu0 ∧ zLF RS < zRF RS beta lam mu mu0 ∧
        zRF RS beta lam mu mu0 < ⊤) := by
  exact ⟨fun I RS h => TEC295.part1 I RS h, TEC295.part2⟩
