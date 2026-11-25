-- Prove2me | solution 1 for PositivityTheory.CW.basis_form_sum_of_gain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:46:00.805845+00:00
-- url     : https://prove2.me/submissions/d5a2b446-ade0-4ecc-a5ba-57e07b51af4f

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisSumOfOrthogonality
import Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_phi_zero
import Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_norm_fib
import Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_eig_fib
import Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
namespace PositivityTheory.CW
theorem _root_.solution : A0 → FunctionalCalculusLaws → A12 → BasisSumAsFormValues → A13 := by
  intro hA0 hA11 hA12 hA13a
  unfold A0 FunctionalCalculusLaws A12 BasisSumAsFormValues A13 ForBas ForMod at *
  intro n ε V i1 i2 E hM ι b μ hEB κ hκ c hc
  obtain ⟨-, -, hmono, hadd, -, hconst, -⟩ := hA11 n ε V E hM ι b μ hEB
  obtain ⟨s, x₀, hs, hx₀, hb12⟩ := hA12 n ε V E hM ι b μ hEB κ hκ c hc
  have hA0' := fun w => ((hA0 n ε V E hM).2.2.2 κ hκ w).2.1
  have hK : 0 ≤ x₀ + |κ| + c := by linarith [abs_nonneg κ]
  refine ⟨s, x₀, x₀ + |κ| + c, hs, hK, ?_⟩
  intro R f S T hS hT
  have hTb : 0 ≤ (x₀ + |κ| + c) * ∑ i ∈ T, ‖f (b i)‖ ^ 2 :=
    mul_nonneg hK (Finset.sum_nonneg fun i _ => by positivity)
  rcases le_or_gt R 0 with hR | hR
  · have hSe : ∀ i ∈ S, False := fun i hi => by
      have := (hS i).1 hi
      linarith [hEB.nonneg i]
    rw [Finset.sum_eq_zero (s := S) (f := fun i => phiR s R (μ i) * ‖f (b i)‖ ^ 2)
        (fun i hi => (hSe i hi).elim),
      Finset.sum_eq_zero (s := S) (f := fun i => phiR s R (μ i) *
        (∑ p ∈ nc ε, ‖f ((E p.1 p.2) (b i))‖ ^ 2 - (μ i - κ) * ‖f (b i)‖ ^ 2))
        (fun i hi => (hSe i hi).elim)]
    linarith
  · have hφS : ∀ i ∉ S, phiR s R (μ i) = 0 := fun i hi =>
      FormEigenMonotone.phi_zero hR (not_lt.mp fun h => hi ((hS i).2 h))
    obtain ⟨T', hST', hT'⟩ := hA13a n ε V E hM ι b μ hEB (phiR s R) S hφS
    have key1 := hT' f
    have hstep : ∀ ν ∈ Finset.image μ T',
        (phiR s R ν * (ν - κ + c) - (if ν < x₀ then x₀ + |κ| + c else 0)) *
          ∑ j ∈ T' with μ j = ν, ‖f (b j)‖ ^ 2 ≤
        (beta ε E (fc b μ (phiR s R)) (∑ j ∈ T' with μ j = ν, (starRingEnd ℂ) (f (b j)) • b j)
            (∑ j ∈ T' with μ j = ν, (starRingEnd ℂ) (f (b j)) • b j)).re := by
      intro ν hν
      obtain ⟨j0, -, rfl⟩ := Finset.mem_image.1 hν
      have hEig := FormEigenMonotone.eig_fib hEB.eig (μ j0) (T'.filter fun j => μ j = μ j0)
        (fun j hj => (Finset.mem_filter.1 hj).2) (fun j => (starRingEnd ℂ) (f (b j)))
      beta_reduce at hEig
      have hk := FormEigenMonotone.key (b := b) (μ := μ) hA0' hmono hadd hconst hb12 hc hR (μ j0)
        (hEB.nonneg j0) _ hEig
      rw [FormEigenMonotone.norm_fib hEB.on f] at hk
      linarith
    have hsum1 : ∑ ν ∈ Finset.image μ T', (phiR s R ν * (ν - κ + c) - (if ν < x₀ then x₀ + |κ| + c else 0)) *
          ∑ j ∈ T' with μ j = ν, ‖f (b j)‖ ^ 2
        = ∑ j ∈ T', (phiR s R (μ j) * (μ j - κ + c) - (if μ j < x₀ then x₀ + |κ| + c else 0)) *
          ‖f (b j)‖ ^ 2 := by
      apply Finset.sum_image'
      intro i _
      beta_reduce
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [(Finset.mem_filter.1 hj).2]
    have e := Finset.sum_subset hST' (f := fun j => phiR s R (μ j) * (μ j - κ + c) * ‖f (b j)‖ ^ 2)
      (fun j _ hj => by simp only [hφS j hj, zero_mul])
    have hsplit : ∑ j ∈ T', (phiR s R (μ j) * (μ j - κ + c) - (if μ j < x₀ then x₀ + |κ| + c else 0)) *
          ‖f (b j)‖ ^ 2
        = ∑ j ∈ S, phiR s R (μ j) * (μ j - κ) * ‖f (b j)‖ ^ 2 +
            c * ∑ j ∈ S, phiR s R (μ j) * ‖f (b j)‖ ^ 2
          - ∑ j ∈ T', (if μ j < x₀ then x₀ + |κ| + c else 0) * ‖f (b j)‖ ^ 2 := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      congr 1
      rw [← e, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hTb2 : ∑ j ∈ T', (if μ j < x₀ then x₀ + |κ| + c else 0) * ‖f (b j)‖ ^ 2
        ≤ (x₀ + |κ| + c) * ∑ i ∈ T, ‖f (b i)‖ ^ 2 := by
      rw [Finset.mul_sum]
      calc ∑ j ∈ T', (if μ j < x₀ then x₀ + |κ| + c else 0) * ‖f (b j)‖ ^ 2
          = ∑ j ∈ T' with μ j < x₀, (x₀ + |κ| + c) * ‖f (b j)‖ ^ 2 := by
            rw [Finset.sum_filter]
            exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
        _ ≤ ∑ i ∈ T, (x₀ + |κ| + c) * ‖f (b i)‖ ^ 2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro j hj
              exact (hT j).2 (Finset.mem_filter.1 hj).2
            · intro j _ _
              exact mul_nonneg hK (by positivity)
    have hle := Finset.sum_le_sum hstep
    rw [hsum1, hsplit, ← key1] at hle
    have hR2 : ∑ i ∈ S, phiR s R (μ i) *
          (∑ p ∈ nc ε, ‖f ((E p.1 p.2) (b i))‖ ^ 2 - (μ i - κ) * ‖f (b i)‖ ^ 2)
        = ∑ i ∈ S, phiR s R (μ i) * ∑ p ∈ nc ε, ‖f ((E p.1 p.2) (b i))‖ ^ 2
          - ∑ i ∈ S, phiR s R (μ i) * (μ i - κ) * ‖f (b i)‖ ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hR2]
    linarith
end PositivityTheory.CW
