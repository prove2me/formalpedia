-- Prove2me | solution 1 for P2M_Formalism_Q3_TypesB_cc_mul__4663f8641e52
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:24.90281+00:00
-- url     : https://prove2.me/submissions/ad48c62c-3bd7-430a-b262-e85fe17e37c2

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.Q3
open Formalism.Q3.TypesB
variable {G : Type*} [CommGroup G] [DecidableEq G] {c : G}
namespace Formalism.Q3.TypesB
theorem _root_.solution (hc : c * c = 1) (g : G) : c * (c * g) = g := by
  rw [← mul_assoc, hc, one_mul]
end Formalism.Q3.TypesB
