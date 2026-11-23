-- Prove2me | solution 1 for P2M_GlobalTheory_Prism_Delta_map___of_map___51a3f1233256
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:37.481691+00:00
-- url     : https://prove2.me/submissions/51097083-9cce-4cc4-960d-adca4459ed47

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
namespace Delta
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (D : Delta l A) (D' : Delta l B)
    (htf : ∀ x : B, (l : B) * x = 0 → x = 0) (f : A →+* B) (h : ∀ a, f (D.φ a) = D'.φ (f a)) (a : A) :
    f (D.δ a) = D'.δ (f a) := by
  rw [← sub_eq_zero]; apply htf
  have := h a
  simp only [D.φ_eq, D'.φ_eq, map_add, map_mul, map_pow, map_natCast] at this
  linear_combination this
end Delta
end GlobalTheory.Prism
