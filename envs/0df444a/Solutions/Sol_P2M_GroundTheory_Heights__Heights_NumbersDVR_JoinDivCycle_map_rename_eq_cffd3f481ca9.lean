-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_map_rename_eq_cffd3f481ca9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:35:39.259007+00:00
-- url     : https://prove2.me/submissions/b04c4a02-d40f-4de3-a411-fa237b1301ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinDivCycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_rename_eq_symm_comp_C_67f959fd0079

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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinDivCycle
variable {R : Type} [CommRing R] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
local notation "ψ" => joinPolyEquiv (R := R) (ι := ι)
local notation "ε" => rename (R := R) (liftVar (ι := ι) ptIdx)
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinDivCycle
theorem _root_.solution (I : Ideal (MRing ι R)) :
    I.map ε = (I.map (Polynomial.C : MRing ι R →+* _)).comap (joinPolyEquiv (R := R) (ι := ι)).toRingHom := by
  have h : I.map ε = I.map (ε).toRingHom := rfl
  rw [h, rename_eq_symm_comp_C, ← Ideal.map_map]
  exact Ideal.map_symm _
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinDivCycle
