-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_tpow_1e634deba6a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:32:46.000416+00:00
-- url     : https://prove2.me/submissions/c963f28e-ccb3-40bf-ba87-10f9dd55d04a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_tensor_129391e5b284
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_zero_27fd26020daf

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
    (L : Fin n → LineBundle k x) (i : Fin n) (M : LineBundle k x) (p : ℕ) :
    bundleNum pp (Function.update L i (M.tpow p)) = p * bundleNum pp (Function.update L i M) := by
  induction p with
  | zero => rw [Nat.cast_zero, zero_mul]; exact bundleNum_zero hR hW L i
  | succ p ih =>
    change bundleNum pp (Function.update L i ((M.tpow p).tensor M)) = _
    rw [bundleNum_tensor hR hW, ih]
    push_cast; ring
end GroundTheory.Heights₂.Heights.Kleiman
