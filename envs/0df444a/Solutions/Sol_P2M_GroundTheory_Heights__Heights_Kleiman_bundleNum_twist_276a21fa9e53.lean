-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_twist_276a21fa9e53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:20:20.031301+00:00
-- url     : https://prove2.me/submissions/412a3a6d-eb58-4e71-b675-e4c25ba60ce8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_congr_99101b80b5d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_tensor_129391e5b284
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_zero_27fd26020daf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_tensor_toSubSystem_c7b278ca5880
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistBundle_toSubSystem_c566e0110c12
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_twist_twistSys_37653a5a4181


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
    (L : Fin n → LineBundle k x) (i : Fin n) (m : ℕ) :
    bundleNum pp (Function.update L i (twistBundle k x m)) =
      m * bundleNum pp (Function.update L i (twistBundle k x 1)) := by
  induction m with
  | zero => simpa using bundleNum_zero hR hW L i
  | succ m ih =>
    have hc : bundleNum pp (Function.update L i (twistBundle k x ((m + 1 : ℕ) : ℤ))) =
        bundleNum pp (Function.update L i ((twistBundle k x m).tensor (twistBundle k x 1))) := by
      refine bundleNum_congr pp fun j => ?_
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self, LineBundle.tensor_toSubSystem, twistBundle_toSubSystem]
        rw [twistSys_twist_twistSys]
        push_cast; rfl
      · simp [hj]
    rw [hc, bundleNum_tensor hR hW, ih]
    push_cast; ring
end GroundTheory.Heights₂.Heights.Kleiman
