-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_L1_rootPoly_monic__823c582ccd94
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:01:25.318198+00:00
-- url     : https://prove2.me/submissions/d77ebc6f-59ff-437d-b04f-5bd60fc08e28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedGcd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {E : Type} [Field E] (xs : Finset E) : (rootPoly xs).Monic :=
  monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x
end ReciprocityTheory.ChartRestriction.L1
