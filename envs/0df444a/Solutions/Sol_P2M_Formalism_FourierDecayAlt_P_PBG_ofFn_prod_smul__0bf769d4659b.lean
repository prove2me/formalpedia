-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_PBG_ofFn_prod_smul__0bf769d4659b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:10:06.818858+00:00
-- url     : https://prove2.me/submissions/274a7e77-2c9f-43d8-9fd4-46654e6d4547

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHeadV
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal
variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution : ∀ {n : ℕ} (c : Fin n → ℂ) (X : Fin n → A),
    (List.ofFn fun i => c i • X i).prod = (∏ i, c i) • (List.ofFn X).prod
  | 0, c, X => by simp
  | n + 1, c, X => by
    rw [List.ofFn_succ, List.prod_cons, solution (fun i => c i.succ) (fun i => X i.succ), Fin.prod_univ_succ,
      List.ofFn_succ, List.prod_cons, smul_mul_smul_comm]
end Formalism.FourierDecayAlt.P.PBG
