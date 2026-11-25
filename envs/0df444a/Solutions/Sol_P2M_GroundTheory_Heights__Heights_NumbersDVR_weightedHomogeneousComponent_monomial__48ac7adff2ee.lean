-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_monomial__48ac7adff2ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:52.092471+00:00
-- url     : https://prove2.me/submissions/868f656f-9adb-42d7-afdb-1cfa19e5810a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsReesAlgebraDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpModel

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
variable {σ : Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {M : Type*} [AddCommMonoid M] [DecidableEq M]
    (w : σ → M) (n : M) (d : σ →₀ ℕ) (c : R) :
    weightedHomogeneousComponent w n (monomial d c) =
      if Finsupp.weight w d = n then monomial d c else 0 := by
  ext e
  rw [coeff_weightedHomogeneousComponent]
  by_cases hed : e = d
  · subst hed
    split_ifs <;> simp
  · classical
    split_ifs <;> simp [coeff_monomial, Ne.symm hed]
end GroundTheory.Heights₂.Heights.NumbersDVR
