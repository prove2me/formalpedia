-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_form_mem_primeSet_5fb772a85b7d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:24:28.560429+00:00
-- url     : https://prove2.me/submissions/752194ea-cc87-4192-944a-af300c71d33d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingDimLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_valIn_change_9fd10f331b07

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
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}
variable (P W : Ideal (MRing ι R)) [P.IsPrime]
variable {P W}
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
theorem _root_.solution (hPW : P ≤ W) {q : Ideal (homLocRing P W)} {s : K → ℕ} {f g : MRing ι R}
    (hf : IsMultiHomog f s) (hg : IsMultiHomog g s) (hgW : g ∉ W)
    (h : ValIn P W q (frac P f / frac P g)) : f ∈ primeSet P W q := by
  intro b g' hg' hg'W
  by_cases hsb : b = s
  · subst hsb
    rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hf]
    exact valIn_change hPW hg hg' hgW hg'W h
  · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b hf hsb, frac_zero, zero_div]
    exact valIn_zero q
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
