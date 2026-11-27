-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_muHom_injective_69240724cc49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:53:24.971131+00:00
-- url     : https://prove2.me/submissions/0f938842-0f2a-4c39-8fec-da1ae3ff4fa2

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
variable (LL : FinExt l) {N : ℕ} [NeZero N] {ζ : PadicAlgCl l} (hζ : IsPrimitiveRoot ζ N) (hm : ζ ∈ LL.1)
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution : Function.Injective (muHom LL hζ hm) := by
  intro a b h
  have h1 := congrArg (fun u : (↥(OL LL))ˣ => u.val.val.val) h
  have h2 : ζ ^ (Multiplicative.toAdd a).val = ζ ^ (Multiplicative.toAdd b).val := by
    simpa [muHom, powHom, zU, zO] using h1
  have h3 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2
  exact Multiplicative.toAdd.injective (ZMod.val_injective N h3)
end Formalism.BasicNotions.Examples₂.LB
