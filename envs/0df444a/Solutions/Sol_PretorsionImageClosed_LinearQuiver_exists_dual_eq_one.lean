-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.exists_dual_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:33.813687+00:00
-- url     : https://prove2.me/submissions/c8a404aa-d400-49d6-9ea3-cb0fb9284792

module
public import Definitions.Def_PretorsionImageClosed_Biproducts_Basic
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module k V] {w : V} (hw : w ≠ 0) :
    ∃ ℓ : Module.Dual k V, ℓ w = 1 := by
  obtain ⟨f, hf, -⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (p := (⊥ : Submodule k V))
    (x := w) (by rw [Submodule.mem_bot]; exact hw) inferInstance
  exact ⟨(f w)⁻¹ • f, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]⟩
end PretorsionImageClosed.LinearQuiver
