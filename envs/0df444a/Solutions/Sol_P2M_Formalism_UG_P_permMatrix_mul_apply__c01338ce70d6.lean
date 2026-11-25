-- Prove2me | solution 1 for P2M_Formalism_UG_P_permMatrix_mul_apply__c01338ce70d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:47:34.431003+00:00
-- url     : https://prove2.me/submissions/c11227b1-0b43-4f2e-b2d6-c04d724b1f82

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (π : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (fIwasawaP π * M : Matrix (Fin n) (Fin n) L) i j = M (π i) j := by
  simp [fIwasawaP, Matrix.mul_apply]
end Formalism.UG.P
