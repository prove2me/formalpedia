-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_hd_comp__b3759ba9d99b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:32:50.506256+00:00
-- url     : https://prove2.me/submissions/75e37714-51f9-48d7-a37a-11cdc37c357d

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Function
universe u
variable {V X Y : Type u} [AddCommGroup V]
namespace ReciprocityTheory.Coh
theorem _root_.solution (n : ℕ) (F : (Fin (n + 1) → Y) → V) (c : X → Y) (x : Fin (n + 2) → X) :
    hd n (fun y => F fun i => c (y i)) x = hd n F (fun i => c (x i)) := rfl
end ReciprocityTheory.Coh
