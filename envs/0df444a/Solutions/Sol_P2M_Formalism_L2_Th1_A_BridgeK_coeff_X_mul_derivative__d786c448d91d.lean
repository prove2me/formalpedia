-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_A_BridgeK_coeff_X_mul_derivative__d786c448d91d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:02:56.241396+00:00
-- url     : https://prove2.me/submissions/98399584-e315-49f6-966e-6649fd6c1628

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeK
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.BridgeK
open Formalism.L2.Th1.CM
namespace Formalism.L2.Th1.A.BridgeK
theorem _root_.solution {K : Type} [Field K] (f : K⟦X⟧) (n : ℕ) :
    coeff n (X * derivative K f) = (n : K) * coeff n f := by
  cases n with
  | zero => simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring
end Formalism.L2.Th1.A.BridgeK
