-- Prove2me | solution 1 for PI.EagonNorthcottZ.sum_cmp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:16:19.479013+00:00
-- url     : https://prove2.me/submissions/62730ac5-144d-46cf-bddf-29f3ef8b5bd0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionPartitionTotal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_LatticeInjective
import Theorems.Thm_PI_EagonNorthcottZ_Ex_inl
import Theorems.Thm_PI_EagonNorthcottZ_Ex_inr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EagonNorthcottZ
open MvPolynomial
namespace PI.EagonNorthcottZ
theorem _root_.solution {D : ℕ} (f : P D) (B : Finset (Fin D →₀ ℕ)) (hB : (Ex D f).support ⊆ B) :
    ∑ β ∈ B, inx (monomial β 1) * cmp β f = f := by
  apply (Ex D).injective
  rw [map_sum]
  have h : ∀ β ∈ B, Ex D (inx (monomial β 1) * cmp β f) = monomial β (coeff β (Ex D f)) := by
    intro β _
    rw [map_mul, inx, cmp, Ex_inl, Ex_inr, map_monomial, map_one, mul_comm, C_mul_monomial, mul_one]
  rw [Finset.sum_congr rfl h]
  conv_rhs => rw [as_sum (Ex D f)]
  symm
  refine Finset.sum_subset hB fun β _ hβ => ?_
  rw [mem_support_iff, not_not] at hβ
  simp [hβ]
end PI.EagonNorthcottZ
