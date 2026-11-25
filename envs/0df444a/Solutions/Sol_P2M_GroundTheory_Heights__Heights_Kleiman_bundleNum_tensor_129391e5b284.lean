-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_tensor_129391e5b284
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:49:55.70309+00:00
-- url     : https://prove2.me/submissions/03ded0c7-c1cd-4a29-b817-cd32129b51f5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_toSubSystem_update_f5a458ca714d

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
    (L : Fin n → LineBundle k x) (i : Fin n) (Y Y' : LineBundle k x) :
    bundleNum pp (Function.update L i (Y.tensor Y')) =
      bundleNum pp (Function.update L i Y) + bundleNum pp (Function.update L i Y') := by
  unfold bundleNum
  rw [toSubSystem_update, toSubSystem_update, toSubSystem_update]
  exact (hR k Ω N x).2.2.1 n pp L i Y Y' hW
end GroundTheory.Heights₂.Heights.Kleiman
