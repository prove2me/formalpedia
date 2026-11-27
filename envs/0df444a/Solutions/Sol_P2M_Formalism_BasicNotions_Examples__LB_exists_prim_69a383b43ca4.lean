-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_exists_prim_69a383b43ca4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:50:57.895827+00:00
-- url     : https://prove2.me/submissions/1648e3b8-0645-4ad0-b8c9-ed439379edd8

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime]
variable (l)
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (N : ℕ) (hN : 0 < N) : ∃ ζ : PadicAlgCl l, IsPrimitiveRoot ζ N := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : PadicAlgCl l) := ⟨by exact_mod_cast hN.ne'⟩
  first
  | exact HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) N
  | exact ⟨_, IsCyclotomicExtension.zeta_spec N (PadicAlgCl l) (PadicAlgCl l)⟩
  | exact ⟨_, IsCyclotomicExtension.zeta_spec ⟨N, hN⟩ (PadicAlgCl l) (PadicAlgCl l)⟩
  | exact IsAlgClosed.exists_primitiveRoot (PadicAlgCl l) N
end Formalism.BasicNotions.Examples₂.LB
