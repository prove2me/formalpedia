-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.pow_apply_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:55.434231+00:00
-- url     : https://prove2.me/submissions/53e72a3d-eca7-4f30-989c-1e6124b74b8b

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
open ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution {n : ℕ} {φ : GK p K}
    (h : ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → φ ζ = ζ ^ qK p K) (i : ℕ) :
    ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → (φ ^ i) ζ = ζ ^ (qK p K ^ i) := by
  induction i with
  | zero => intro ζ _; simp
  | succ i ih =>
    intro ζ hζ
    rw [pow_succ, AlgEquiv.mul_apply, h ζ hζ, map_pow, ih ζ hζ, ← pow_mul, pow_succ]
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
