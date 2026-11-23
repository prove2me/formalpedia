-- Prove2me | solution 1 for P2M_GlobalTheory_Prism_Hom_ext__fc72cc082215
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:20.289802+00:00
-- url     : https://prove2.me/submissions/47a93a37-cfe6-4a3c-b8aa-6f11925aeca0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InvertibleSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Prism
attribute [instance] Obj.ring
variable {l : ℕ} {R : Type} [CommRing R]
attribute [instance] FCrys.acg FCrys.mod
attribute [instance] VBun.acg VBun.mod
namespace GlobalTheory.Prism
namespace Hom
theorem _root_.solution {P P' : Obj l R} {f g : Hom P P'} (h : f.f = g.f) : f = g := by
  cases f; cases g; cases h; rfl
end Hom
end GlobalTheory.Prism
