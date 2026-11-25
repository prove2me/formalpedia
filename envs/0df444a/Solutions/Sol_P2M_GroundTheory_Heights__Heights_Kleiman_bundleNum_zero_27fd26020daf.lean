-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_zero_27fd26020daf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:02:47.053129+00:00
-- url     : https://prove2.me/submissions/4e92ad0b-5aa0-4fb7-a2d9-6267d89ba1bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_congr_99101b80b5d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_tensor_129391e5b284
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_tensor_toSubSystem_c7b278ca5880
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistBundle_toSubSystem_c566e0110c12


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (hR : GenericPointSectionInput.Statement.{u, w})
include hR
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {pp : Ideal (Poly k N)} {n : ℕ} (hW : IsSubvar x pp n)
    (L : Fin n → LineBundle k x) (i : Fin n) :
    bundleNum pp (Function.update L i (twistBundle k x 0)) = 0 := by
  have h := bundleNum_tensor hR hW L i (twistBundle k x 0) (twistBundle k x 0)
  have hc : bundleNum pp (Function.update L i ((twistBundle k x 0).tensor (twistBundle k x 0))) =
      bundleNum pp (Function.update L i (twistBundle k x 0)) := by
    refine bundleNum_congr pp fun j => ?_
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self, LineBundle.tensor_toSubSystem, twistBundle_toSubSystem]
      exact twistSys_zero_twist _
    · simp [hj]
  linarith
end GroundTheory.Heights₂.Heights.Kleiman
