-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.exists_isU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:43.684404+00:00
-- url     : https://prove2.me/submissions/0d04253f-beb7-4279-818e-8b6c9776a011

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (I : Submodule ℤ (Vsp dim)) (x : Vsp dim) : ∃ u, IsU I x u := by
  let K := IR I
  let f : K →ₗ[ℝ] ℝ :=
    { toFun := fun a => (Hf x (a : Vsp dim)).im
      map_add' := fun a b => by simp only [Submodule.coe_add, Hf_im_add_right]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul, Hf_im_smul_right, smul_eq_mul, RingHom.id_apply] }
  let u : K := (InnerProductSpace.toDual ℝ K).symm (LinearMap.toContinuousLinearMap f)
  refine ⟨(u : Vsp dim), u.2, fun a ha => ?_⟩
  have h1 := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := K) (x := ⟨a, ha⟩)
    (y := LinearMap.toContinuousLinearMap f)
  exact h1
end ReciprocityTheory.ChartRestriction.G.I2
