-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUp_relation_be19b3539eff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:30.363934+00:00
-- url     : https://prove2.me/submissions/715026db-a3d9-4c86-841a-27f725c1544b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_SpanTwoIsPrimeRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_liftForm_4b99591f2332

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) (s g f m : MRing ι R) (e : K → ℕ) :
    liftForm (s * g) * newVar (some none) - liftForm (f * m) * newVar none ∈
      blowUpOf P (blowUpGens s g f m e) := by
  rw [blowUpOf, RingHom.mem_ker]
  simp only [map_sub, map_mul, aeval_blowUpSubst_liftForm, newVar, aeval_X, blowUpSubst, blowUpGens]
  ring
end GroundTheory.Heights₂.Heights.NumbersDVR
