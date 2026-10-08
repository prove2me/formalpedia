-- Prove2me | solution 1 for PolicyGradTheory.ChainLB.chain_value_eq_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:30:21.045775+00:00
-- url     : https://prove2.me/submissions/a1c32f1c-f511-4120-a85f-afeed880d584

import Mathlib
import Definitions.Def_PolicyGradTheory_ChainLB_Chain



namespace PolicyGradTheory.ChainLB

open FoundationsML.ReinforcementLearning

lemma induced_eq_core (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (s s' : Fin (H + 2)) :
    InducedTransition (chainPolicy H θ) (chainP H) s s' = chainMatrix H (forwardProb H θ) s s' := by
  unfold InducedTransition chainPolicy chainP chainMatrix forwardProb
  rw [Fin.sum_univ_four]
  by_cases h0 : s.val = 0
  · simp [h0]
  by_cases h1 : s.val = H + 1
  · have : ¬ (0 < s.val ∧ s.val ≤ H) := by omega
    simp [h1, this]
  have hs : 0 < s.val ∧ s.val ≤ H := ⟨by omega, by omega⟩
  simp [h0, h1, hs]
  split_ifs <;> first | (exfalso; omega) | ring

lemma chainMatrix_nonneg (H : ℕ) (p : Fin H → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (s s' : Fin (H + 2)) : 0 ≤ chainMatrix H p s s' := by
  unfold chainMatrix
  split_ifs <;> first | exact (hp _).1 | exact sub_nonneg.2 (hp _).2 | norm_num

lemma chainMatrix_rowsum (H : ℕ) (p : Fin H → ℝ) (s : Fin (H + 2)) :
    ∑ s', chainMatrix H p s s' = 1 := by
  by_cases h0 : s.val = 0
  · have : ∀ s' : Fin (H + 2), chainMatrix H p s s' = if s' = ⟨1, by omega⟩ then 1 else 0 := by
      intro s'; unfold chainMatrix; simp [h0, Fin.ext_iff]
    rw [Finset.sum_congr rfl (fun s' _ => this s'), Finset.sum_ite_eq']; simp
  by_cases h1 : s.val = H + 1
  · have : ∀ s' : Fin (H + 2), chainMatrix H p s s' = if s' = s then 1 else 0 := by
      intro s'; unfold chainMatrix; simp [h0, h1]
    simp [this]
  have hs : 0 < s.val ∧ s.val ≤ H := ⟨by omega, by omega⟩
  have : ∀ s' : Fin (H + 2), chainMatrix H p s s' =
      p ⟨s.val - 1, by omega⟩ * (if s' = ⟨s.val + 1, by omega⟩ then 1 else 0) +
      (1 - p ⟨s.val - 1, by omega⟩) * (if s' = ⟨s.val - 1, by omega⟩ then 1 else 0) := by
    intro s'; unfold chainMatrix
    simp only [h0, h1, hs, and_self, dif_pos, if_false, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  ring

lemma pow_bounds (H : ℕ) (p : Fin H → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (t : ℕ) :
    (∀ s s', 0 ≤ (chainMatrix H p ^ t) s s') ∧ ∀ s, ∑ s', (chainMatrix H p ^ t) s s' = 1 := by
  induction t with
  | zero =>
    refine ⟨fun s s' => ?_, fun s => ?_⟩
    · rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [Matrix.one_apply]
  | succ t ih =>
    refine ⟨fun s s' => ?_, fun s => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (ih.1 _ _) (chainMatrix_nonneg H p hp _ _)
    · rw [pow_succ]
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp [← Finset.mul_sum, chainMatrix_rowsum, ih.2]

lemma pow_le_one (H : ℕ) (p : Fin H → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (t : ℕ)
    (s s' : Fin (H + 2)) : (chainMatrix H p ^ t) s s' ≤ 1 := by
  have h := pow_bounds H p hp t
  rw [← h.2 s]
  exact Finset.single_le_sum (fun k _ => h.1 s k) (Finset.mem_univ s')

lemma gamma_bounds (H : ℕ) : 0 ≤ chainGamma H ∧ chainGamma H < 1 := by
  unfold chainGamma
  constructor
  · positivity
  · rw [div_lt_one (by positivity)]; linarith

lemma summable_entry (H : ℕ) (p : Fin H → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (s s' : Fin (H + 2)) :
    Summable (fun t : ℕ => chainGamma H ^ t * (chainMatrix H p ^ t) s s') := by
  obtain ⟨g0, g1⟩ := gamma_bounds H
  refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg g0 _)
    ((pow_bounds H p hp t).1 s s')) (fun t => ?_) (summable_geometric_of_lt_one g0 g1)
  calc chainGamma H ^ t * (chainMatrix H p ^ t) s s' ≤ chainGamma H ^ t * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one H p hp t s s') (pow_nonneg g0 _)
    _ = _ := mul_one _

lemma resolvent_eq_tsum (H : ℕ) (p : Fin H → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    chainResolvent H p = Matrix.of (fun s s' => ∑' t : ℕ, chainGamma H ^ t * (chainMatrix H p ^ t) s s') := by
  unfold chainResolvent
  apply Matrix.inv_eq_right_inv
  ext i j
  set A := chainMatrix H p
  set γ := chainGamma H
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.smul_mul, Matrix.smul_apply,
    Matrix.mul_apply, smul_eq_mul]
  simp only [Matrix.of_apply]
  have hs := summable_entry H p hp
  have h1 : ∑ k, A i k * ∑' t : ℕ, γ ^ t * (A ^ t) k j = ∑' t : ℕ, γ ^ t * (A ^ (t + 1)) i j := by
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun k _ => (hs k j).mul_left _)]
    congr 1; ext t
    rw [pow_succ', Matrix.mul_apply, Finset.mul_sum]
    congr 1; ext k; ring
  rw [h1, (hs i j).tsum_eq_zero_add]
  rw [← tsum_mul_left]
  simp only [pow_zero, one_mul]
  have : ∀ t : ℕ, γ * (γ ^ t * (A ^ (t + 1)) i j) = γ ^ (t + 1) * (A ^ (t + 1)) i j := by
    intro t; ring
  simp_rw [this]
  ring

theorem chain_value_eq_resolvent_core (H : ℕ)
    (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hθ : ∀ i j, 0 < θ (i, j) ∧ θ (i, j) < 1) :
    chainValue H θ = chainResolvent H (forwardProb H θ) 0 (Fin.last (H + 1)) := by
  have hp : ∀ i, 0 ≤ forwardProb H θ i ∧ forwardProb H θ i ≤ 1 :=
    fun i => ⟨(hθ i 0).1.le, (hθ i 0).2.le⟩
  rw [resolvent_eq_tsum H _ hp, Matrix.of_apply]
  unfold chainValue PolicyValue
  have hocc : ∀ t s', OccupationDist (chainPolicy H θ) (chainP H) 0 t s' =
      (chainMatrix H (forwardProb H θ) ^ t) 0 s' := by
    intro t
    induction t with
    | zero => intro s'; simp [OccupationDist, Matrix.one_apply, eq_comm]
    | succ t ih =>
      intro s'
      simp only [OccupationDist, ih, induced_eq_core, pow_succ, Matrix.mul_apply]
  have hrew : ∀ s', InducedReward (chainPolicy H θ) (chainR H) s' =
      if s' = Fin.last (H + 1) then 1 else 0 := by
    intro s'
    unfold InducedReward chainR chainPolicy
    rw [Fin.sum_univ_four]
    by_cases h : s' = Fin.last (H + 1)
    · have : ¬ (0 < s'.val ∧ s'.val ≤ H) := by subst h; simp
      simp [h, this]
    · simp [h]
  congr 1; ext t
  simp [hocc, hrew]

end PolicyGradTheory.ChainLB

open PolicyGradTheory.ChainLB


theorem solution (H : ℕ) (hH : 1 ≤ H)
    (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hθ : ∀ i j, 0 < θ (i, j) ∧ θ (i, j) < 1)
    (hθ1 : ∀ i, θ (i, (0 : Fin 3)) < 1 / 4) :
    chainValue H θ = chainResolvent H (forwardProb H θ) 0 (Fin.last (H + 1)) := by
  exact chain_value_eq_resolvent_core H θ hθ
