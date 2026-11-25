-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.fromVector_comp_toInterval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:12.533953+00:00
-- url     : https://prove2.me/submissions/8f552488-f772-42d8-839f-282bcbc110a6

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
variable (X : Statement.LinRep k n) (i₀ : Fin n) (v : X.obj i₀)
variable {X i₀ v} (d : Fin n)
variable (ℓ : Module.Dual k (X.obj d))
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (hd : ∀ j, d < j → vmap X i₀ v j = 0)
    (hfirst : ∀ i, i < i₀ → IsZero (X.obj i)) (hℓ : ℓ (vmap X i₀ v d) = 1) :
    fromVector d hd ≫ toInterval d ℓ hfirst = 𝟙 _ := by
  ext j : 2
  apply FGModuleCat.hom_ext
  refine LinearMap.ext fun (x : intervalSpace k i₀ d j) => ?_
  apply Subtype.ext
  change (toIntervalLin (i₀ := i₀) d ℓ j (fromVectorLin (v := v) d j x) : k) = (x : k)
  rw [fromVectorLin_apply]
  by_cases hj : i₀ ≤ j ∧ j ≤ d
  · rw [toIntervalLin_apply_of_mem d ℓ hj, map_smul, map_vmap X i₀ v _ hj.1, map_smul, hℓ,
      smul_eq_mul, mul_one]
  · rw [toIntervalLin_apply_of_not_mem d ℓ hj, coe_eq_zero_of_not_mem k hj x]
end PretorsionImageClosed.LinearQuiver
