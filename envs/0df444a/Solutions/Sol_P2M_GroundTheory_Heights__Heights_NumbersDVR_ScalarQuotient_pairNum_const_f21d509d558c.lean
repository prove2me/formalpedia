-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_pairNum_const_f21d509d558c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:35:11.027599+00:00
-- url     : https://prove2.me/submissions/a5cd70df-83e6-48c0-b811-1a255265c3e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PScalarQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_sum_classNum_psumExpansion_diag_8be76746319f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_divCycle_support_finite_d90d2125fc12
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_ratDiv_const_4e661b9d7cd3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
theorem _root_.solution (P : Ideal (MRing ι O)) [P.IsPrime]
    (hP : ∀ a : O, a ≠ 0 → (C a : MRing ι O) ∉ P) {ϖ : O} (hϖ : ϖ ≠ 0) (u : Oˣ) (n : ℕ)
    {N : ℕ} (x : Fin N → K → ℤ) (k : ℕ) (Q : List (K → ℤ)) :
    pairNum P x x (fun _ => C ((u : O) * ϖ ^ n)) (fun _ => 1) (psumExpansion N k) Q =
      (k : ℤ) * n * cycEval (fun W => classNum x (psum (Fin N) ℤ (k - 1)) Q W)
        (divCycle P (C ϖ)) := by
  unfold pairNum cycEval
  simp only [ratDiv_const P hP hϖ u n]
  have hfin := divCycle_support_finite P (C ϖ)
  have sub : ∀ h : Ideal (MRing ι O) → ℤ, (∀ W, divCycle P (C ϖ) W = 0 → h W = 0) →
      ∑ᶠ W, h W = ∑ W ∈ hfin.toFinset, h W := by
    intro h hh
    refine finsum_eq_sum_of_support_subset h fun W hW => ?_
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    exact fun hD => hW (hh W hD)
  rw [sub _ (fun W hW => by simp [hW])]
  rw [Finset.sum_congr rfl (fun i _ => sub _ (fun W hW => by simp [hW]))]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [← Finset.mul_sum, sum_classNum_psumExpansion_diag]
  ring
end GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
