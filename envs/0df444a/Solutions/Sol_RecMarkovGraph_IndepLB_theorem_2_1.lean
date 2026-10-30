-- Prove2me | solution 1 for RecMarkovGraph.IndepLB.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T11:43:53.040985+00:00
-- url     : https://prove2.me/submissions/84e41372-fdb9-4b46-b09b-15b1d5d00105

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model
import Theorems.Thm_RecMarkovGraph_IndepLB_eq_11
import Theorems.Thm_RecMarkovGraph_IndepLB_theorem_2_2

open Filter Topology Finset
open scoped Classical

namespace RecMarkovGraph.IndepLB.RedAux

lemma recSeq_mem (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1) :
    ∀ k, 0 ≤ recSeq (1 - r) p k ∧ recSeq (1 - r) p k ≤ 1
  | 0 => ⟨hp.le, hp1⟩
  | k + 1 => by
    obtain ⟨h0, h1⟩ := recSeq_mem p r hp hp1 hr hr1 k
    simp only [recSeq, fa]
    have hpos : 0 ≤ 1 - (1 - r) * recSeq (1 - r) p k := by nlinarith
    constructor
    · exact mul_nonneg h0 hpos
    · nlinarith [mul_nonneg (mul_nonneg h0 h0) (by linarith : (0:ℝ) ≤ 1 - r)]

lemma stepWeight_nonneg (r q : ℝ) (hr : 0 < r) (hr1 : r < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (P Q : Prop) : 0 ≤ stepWeight r q P Q := by
  unfold stepWeight
  split_ifs <;> nlinarith

lemma stepWeight_sum (r q : ℝ) (P : Prop) :
    ∑ b : Bool, stepWeight r q P (b = true) = 1 := by
  simp only [Fintype.sum_bool, stepWeight]
  split_ifs <;> simp_all

lemma chainWeight_nonneg (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (m : ℕ) (x : ℕ → Prop) : 0 ≤ chainWeight p r m x := by
  unfold chainWeight
  by_cases hm : m = 0
  · rw [if_pos hm]; exact zero_le_one
  · rw [if_neg hm]
    refine mul_nonneg (by split_ifs <;> linarith) (Finset.prod_nonneg fun j _ => ?_)
    obtain ⟨h0, h1⟩ := recSeq_mem p r hp hp1 hr hr1 j
    exact stepWeight_nonneg r _ hr hr1 h0 h1 _ _

lemma stepWeight_congr (r q : ℝ) (P P' Q Q' : Prop) (hP : P ↔ P') (hQ : Q ↔ Q') :
    stepWeight r q P Q = stepWeight r q P' Q' := by
  rw [propext hP, propext hQ]

lemma chainWeight_congr (p r : ℝ) (m : ℕ) (x y : ℕ → Prop) (h : ∀ j < m, (x j ↔ y j)) :
    chainWeight p r m x = chainWeight p r m y := by
  unfold chainWeight
  by_cases hm : m = 0
  · rw [if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm]
    congr 1
    · exact if_congr (h 0 (by omega)) rfl rfl
    · refine Finset.prod_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      exact stepWeight_congr r _ _ _ _ _ (h j (by omega)) (h (j + 1) (by omega))

lemma chainWeight_succ (p r : ℝ) (m : ℕ) (hm : 1 ≤ m) (x : ℕ → Prop) :
    chainWeight p r (m + 1) x =
      chainWeight p r m x * stepWeight r (recSeq (1 - r) p (m - 1)) (x (m - 1)) (x m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  unfold chainWeight
  simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  rw [Finset.prod_range_succ]
  ring

/-- The row law sums to one. -/
lemma rowSum (p r : ℝ) : ∀ m : ℕ,
    ∑ y : Fin m → Bool, chainWeight p r m (fun j => ∃ h : j < m, y ⟨j, h⟩ = true) = 1
  | 0 => by simp [chainWeight]
  | m + 1 => by
    rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => Bool)) _ _ (fun _ => rfl)]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hlt : ∀ (y' : Fin m → Bool) (b : Bool), ∀ j < m,
        ((∃ h : j < m + 1, (Fin.snocEquiv (fun _ => Bool) (b, y')) ⟨j, h⟩ = true) ↔
          ∃ h : j < m, y' ⟨j, h⟩ = true) := by
      intro y' b j hj
      have e : ∀ h : j < m + 1, (Fin.snocEquiv (fun _ => Bool) (b, y')) ⟨j, h⟩ = y' ⟨j, hj⟩ := by
        intro h
        simp only [Fin.snocEquiv_apply]
        exact Fin.snoc_castSucc (α := fun _ => Bool) (p := y') (x := b) (i := ⟨j, hj⟩)
      constructor
      · rintro ⟨h, hh⟩; exact ⟨hj, by rw [← e h]; exact hh⟩
      · rintro ⟨h, hh⟩; exact ⟨by omega, by rw [e]; exact hh⟩
    have hlast : ∀ (y' : Fin m → Bool) (b : Bool),
        ((∃ h : m < m + 1, (Fin.snocEquiv (fun _ => Bool) (b, y')) ⟨m, h⟩ = true) ↔ b = true) := by
      intro y' b
      have e : (Fin.snocEquiv (fun _ => Bool) (b, y')) ⟨m, by omega⟩ = b := by
        simp only [Fin.snocEquiv_apply]
        exact Fin.snoc_last (α := fun _ => Bool) (p := y') (x := b)
      constructor
      · rintro ⟨h, hh⟩; rw [← e]; exact hh
      · intro hb; exact ⟨by omega, by rw [e]; exact hb⟩
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [chainWeight, Nat.add_one_ne_zero, if_false, Nat.sub_self, Finset.range_zero,
        Finset.prod_empty, mul_one]
      rw [Fintype.sum_unique]
      rw [Fintype.sum_bool]
      have h1 := hlast (default : Fin 0 → Bool) true
      have h2 := hlast (default : Fin 0 → Bool) false
      split_ifs with ha hb hb
      · exact absurd (h2.mp hb) (by simp)
      · ring
      · exact absurd (h1.mpr rfl) ha
      · exact absurd (h1.mpr rfl) ha
    · rw [← rowSum p r m]
      refine Finset.sum_congr rfl (fun y' _ => ?_)
      have hc : ∀ b : Bool, chainWeight p r (m + 1)
          (fun j => ∃ h : j < m + 1, (Fin.snocEquiv (fun _ => Bool) (b, y')) ⟨j, h⟩ = true) =
          chainWeight p r m (fun j => ∃ h : j < m, y' ⟨j, h⟩ = true) *
            stepWeight r (recSeq (1 - r) p (m - 1)) (∃ h : m - 1 < m, y' ⟨m - 1, h⟩ = true)
              (b = true) := by
        intro b
        rw [chainWeight_succ p r m hm]
        rw [chainWeight_congr p r m _ _ (hlt y' b)]
        exact congrArg _ (stepWeight_congr r _ _ _ _ _ (hlt y' b (m - 1) (by omega)) (hlast y' b))
      simp only [hc]
      rw [← Finset.mul_sum, stepWeight_sum, mul_one]

noncomputable def rowEquiv (n : ℕ) : SimpleGraph (Fin n) ≃ (∀ i : Fin n, Fin i → Bool) where
  toFun G i j := decide (G.Adj ⟨j, j.2.trans i.2⟩ i)
  invFun f :=
    { Adj := fun a b => (∃ h : b.val < a.val, f a ⟨b, h⟩ = true) ∨
        (∃ h : a.val < b.val, f b ⟨a, h⟩ = true)
      symm := ⟨fun _ _ h => Or.symm h⟩
      loopless := ⟨fun a h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact lt_irrefl _ h⟩ }
  left_inv G := by
    ext a b
    simp only [decide_eq_true_eq, Fin.eta]
    rcases lt_trichotomy a.val b.val with h | h | h
    · constructor
      · rintro (⟨h', _⟩ | ⟨_, h'⟩)
        · omega
        · exact h'
      · intro hab; exact Or.inr ⟨h, hab⟩
    · have : a = b := Fin.ext h
      subst this
      simp
    · constructor
      · rintro (⟨_, h'⟩ | ⟨h', _⟩)
        · exact G.adj_symm h'
        · omega
      · intro hab; exact Or.inl ⟨h, G.adj_symm hab⟩
  right_inv f := by
    funext i j
    have hj := j.2
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro (⟨h', _⟩ | ⟨_, h'⟩)
      · omega
      · exact h'
    · intro hf; exact Or.inr ⟨hj, hf⟩

lemma weight_eq (n : ℕ) (p r : ℝ) (G : SimpleGraph (Fin n)) :
    rmrgWeight n p r G = ∏ i : Fin n,
      chainWeight p r i (fun j => ∃ h : j < (i : ℕ), rowEquiv n G i ⟨j, h⟩ = true) := by
  unfold rmrgWeight
  refine Finset.prod_congr rfl (fun i _ => chainWeight_congr p r _ _ _ (fun j hj => ?_))
  simp only [rowEquiv, Equiv.coe_fn_mk, decide_eq_true_eq]
  constructor
  · rintro ⟨_, h⟩; exact ⟨hj, h⟩
  · rintro ⟨_, h⟩; exact ⟨hj.trans i.2, h⟩

lemma weight_nonneg (n : ℕ) (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (G : SimpleGraph (Fin n)) : 0 ≤ rmrgWeight n p r G :=
  Finset.prod_nonneg fun i _ => chainWeight_nonneg p r hp hp1 hr hr1 _ _

lemma total_eq_one (n : ℕ) (p r : ℝ) : rmrgProb n p r (fun _ => True) = 1 := by
  unfold rmrgProb
  simp only [if_true, mul_one]
  rw [Fintype.sum_equiv (rowEquiv n) _
    (fun f => ∏ i : Fin n, chainWeight p r i (fun j => ∃ h : j < (i : ℕ), f i ⟨j, h⟩ = true))
    (fun G => weight_eq n p r G)]
  have hps := Fintype.prod_sum (fun (i : Fin n) (y : Fin i → Bool) =>
    chainWeight p r i (fun j => ∃ h : j < (i : ℕ), y ⟨j, h⟩ = true))
  rw [← hps]
  exact Finset.prod_eq_one (fun i _ => rowSum p r i)

lemma prob_mono (n : ℕ) (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (E F : SimpleGraph (Fin n) → Prop) (h : ∀ G, E G → F G) :
    rmrgProb n p r E ≤ rmrgProb n p r F := by
  unfold rmrgProb
  refine Finset.sum_le_sum (fun G _ => mul_le_mul_of_nonneg_left ?_
    (weight_nonneg n p r hp hp1 hr hr1 G))
  by_cases hE : E G
  · simp [hE, h G hE]
  · simp only [hE, if_false]; split_ifs <;> norm_num

lemma prob_le_one (n : ℕ) (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (E : SimpleGraph (Fin n) → Prop) : rmrgProb n p r E ≤ 1 := by
  rw [← total_eq_one n p r]
  exact prob_mono n p r hp hp1 hr hr1 _ _ (fun _ _ => trivial)

end RecMarkovGraph.IndepLB.RedAux

open RecMarkovGraph.IndepLB RecMarkovGraph.IndepLB.RedAux in
theorem solution (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => rmrgProb n p r
        (fun G => (1 - r) / (2 + ε) * ((n : ℝ) / Real.log n) ≤ (G.indepNum : ℝ)))
      atTop (𝓝 1) := by
  have hγ : 0 < 1 - r := by linarith
  have hε₀ : 0 < ε / 2 := by positivity
  have h22 := theorem_2_2 p r hp hp1 hr hr1 (ε / 2 / (1 - r)) (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h22 tendsto_const_nhds ?_ ?_
  · have hev : ∀ᶠ n : ℕ in atTop, Real.exp ((1 - r) / (ε - ε / 2)) < (n : ℝ) := by
      obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp ((1 - r) / (ε - ε / 2)))
      filter_upwards [eventually_ge_atTop N] with n hn
      exact lt_of_lt_of_le hN (by exact_mod_cast hn)
    filter_upwards [hev] with n hn
    obtain ⟨h1, h2⟩ := eq_11 p r hp hp1 hr hr1 ε (ε / 2) hε₀ (by linarith) n hn
    have e : ∀ G : SimpleGraph (Fin n),
        ((n : ℝ) / ((2 + ε) / (1 - r) * Real.log n) ≤ (G.indepNum : ℝ)) →
          (1 - r) / (2 + ε) * ((n : ℝ) / Real.log n) ≤ (G.indepNum : ℝ) := by
      intro G hG
      have : (n : ℝ) / ((2 + ε) / (1 - r) * Real.log n) =
          (1 - r) / (2 + ε) * ((n : ℝ) / Real.log n) := by
        rw [div_eq_mul_inv, mul_inv, inv_div]; ring
      rwa [this] at hG
    calc rmrgProb n p r (fun G => |avgDeg G / Real.log n - 2 / (1 - r)| ≤ ε / 2 / (1 - r))
        ≤ rmrgProb n p r (fun G => avgDeg G / Real.log n ≤ (2 + ε / 2) / (1 - r)) :=
          prob_mono n p r hp hp1 hr hr1 _ _ (fun G hG => by
            have := (abs_le.mp hG).2
            have e2 : (2 + ε / 2) / (1 - r) = 2 / (1 - r) + ε / 2 / (1 - r) := by ring
            linarith)
      _ ≤ _ := h2
      _ ≤ _ := h1
      _ ≤ _ := prob_mono n p r hp hp1 hr hr1 _ _ e
  · exact Eventually.of_forall (fun n => prob_le_one n p r hp hp1 hr hr1 _)
