-- Prove2me | solution 1 for P2M_GlobalTheory_Prism_Delta___zero_fed7c125f185
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:55.443477+00:00
-- url     : https://prove2.me/submissions/718752fd-ee96-4375-bcbd-82067dd5208b

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
theorem _root_.solution {A : Type} [CommRing A] (D : Delta l A) : D.δ 0 = 0 := by
  have h := D.δ_add 0 0
  have e : ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * (0 : A) ^ k * (0 : A) ^ (l - k) = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [zero_pow (Finset.mem_Ioo.1 hk).1.ne']; simp
  rw [e, add_zero] at h
  linear_combination -h
end Delta
end GlobalTheory.Prism
