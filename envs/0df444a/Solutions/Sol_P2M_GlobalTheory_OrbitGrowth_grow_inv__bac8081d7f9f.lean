-- Prove2me | solution 1 for P2M_GlobalTheory_OrbitGrowth_grow_inv__bac8081d7f9f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:31:51.511362+00:00
-- url     : https://prove2.me/submissions/05684802-ce19-43a7-9c8c-3aa49f1e9941

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply
import Theorems.Thm_P2M_GlobalTheory_OrbitGrowth_mul_apply__1ef562d11778
import Theorems.Thm_GlobalTheory_OrbitGrowth_grow_le
import Theorems.Thm_GlobalTheory_OrbitGrowth_mem_grow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitGrowth
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.OrbitGrowth
theorem _root_.solution {A : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} {c : Module.End ℂ M}
    (hc : ∀ x ∈ W, c x ∈ W) (hcomm : ∀ a ∈ A, c * a = a * c) {x : M} (hx : x ∈ grow A W) :
    c x ∈ grow A W := by
  have h : grow A W ≤ (grow A W).comap c := grow_le.mpr (fun b hb y hy => by
    show c (b y) ∈ grow A W
    rw [← mul_apply', hcomm b hb, mul_apply']
    exact mem_grow hb (hc y hy))
  exact h hx
end GlobalTheory.OrbitGrowth
