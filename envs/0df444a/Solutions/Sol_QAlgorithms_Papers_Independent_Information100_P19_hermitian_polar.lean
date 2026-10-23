-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.hermitian_polar
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:22:32.138755+00:00
-- url     : https://prove2.me/submissions/ddae4b92-1f2c-482c-961e-ca1f32a79f03

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

lemma X7HP_pairing_eq {n : ℕ} (f : Coeff n) (y : Part n → ℝ) :
    pairing f y = ∑ l ∈ f.support, f l * y l := by
  unfold pairing Finsupp.sum; rfl

lemma X7HP_pairing_cont {n : ℕ} (f : Coeff n) : Continuous (fun y : Part n → ℝ => pairing f y) := by
  simp_rw [X7HP_pairing_eq]
  exact continuous_finset_sum _ (fun l _ => continuous_const.mul (continuous_apply l))

lemma X7HP_closedCone {n : ℕ} (f : Coeff n) (S : Set (Part n → ℝ))
    (hS : ∀ y ∈ S, 0 ≤ pairing f y) : ∀ y ∈ closedCone S, 0 ≤ pairing f y := by
  have hsub : finiteCone S ⊆ {y | 0 ≤ pairing f y} := by
    rintro y ⟨N, c, u, hcu, rfl⟩
    simp only [Set.mem_setOf_eq, X7HP_pairing_eq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_nonneg
    intro i _
    have h := hS (u i) (hcu i).2
    rw [X7HP_pairing_eq] at h
    have : ∑ l ∈ f.support, f l * (c i * u i l) = c i * ∑ l ∈ f.support, f l * u i l := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun l _ => by ring)
    rw [this]
    exact mul_nonneg (hcu i).1 h
  have hcl : IsClosed {y : Part n → ℝ | 0 ≤ pairing f y} :=
    isClosed_le continuous_const (X7HP_pairing_cont f)
  intro y hy
  exact (closure_minimal hsub hcl) hy

lemma X7HP_mem_closedCone {V : Type*} [AddCommMonoid V] [Module ℝ V] [TopologicalSpace V]
    (S : Set V) (y : V) (hy : y ∈ S) : y ∈ closedCone S := by
  apply subset_closure
  refine ⟨1, fun _ => 1, fun _ => y, fun _ => ⟨zero_le_one, hy⟩, ?_⟩
  simp

end QAlgorithms.Papers.Independent.Information100.P19

end

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution (n : ℕ) (hn : 1 ≤ n) : allCone n = spectralPolar (allMom n) := by
  ext f
  constructor
  · intro hf y hy
    exact X7HP_closedCone f _ (by rintro y ⟨d, hd, x, rfl⟩; exact hf d hd x) y hy
  · intro hf d hd x
    exact hf _ (X7HP_mem_closedCone _ _ ⟨d, hd, x, rfl⟩)

end
