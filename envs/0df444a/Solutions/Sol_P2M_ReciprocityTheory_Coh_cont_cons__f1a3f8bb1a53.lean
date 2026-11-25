-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_cont_cons__f1a3f8bb1a53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:42.265946+00:00
-- url     : https://prove2.me/submissions/4dfd6b01-5237-41f1-9133-63ff8e54537c

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
theorem _root_.solution {S Y : Type*} [TopologicalSpace S] [TopologicalSpace Y] {m : ℕ} (f : S → Y)
    (g : S → Fin m → Y) (hf : Continuous f) (hg : Continuous g) :
    Continuous fun s => (Fin.cons (f s) (g s) : Fin (m + 1) → Y) := hf.finCons hg
end ReciprocityTheory.Coh
