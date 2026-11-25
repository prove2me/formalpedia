-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.x_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:46:37.522661+00:00
-- url     : https://prove2.me/submissions/b490b15d-1f37-4302-962b-6ff7686f87ba

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {X V W Z : Type u} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]
namespace ReciprocityTheory.Coh.CCA
theorem _root_.solution {n : ℕ} (x : Fin n → X) (a b : Fin n) (h : (a : ℕ) = b) : x a = x b := congrArg x (Fin.ext h)
end ReciprocityTheory.Coh.CCA
