-- Prove2me | solution 1 for P2M_Formalism_UG_P_permMatrix_mulVec__7012a139132f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:47:32.922475+00:00
-- url     : https://prove2.me/submissions/bd2032ce-5e63-4e53-9a29-cd8c843c9500

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
theorem _root_.solution (π : Equiv.Perm (Fin n)) (w : Fin n → L) :
    fIwasawaP π *ᵥ w = fun i => w (π i) := by
  funext i
  simp [fIwasawaP, Matrix.mulVec, dotProduct]
end Formalism.UG.P
