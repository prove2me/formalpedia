-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.isGen_mulGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:58:24.925435+00:00
-- url     : https://prove2.me/submissions/8f8f7574-5be9-4167-83ba-358520bb39d4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_ts_mulGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open ReciprocityTheory.ChartRestriction.G.Semi.LB
variable {X Y Z : Scheme.{u}}
variable (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.Semi.LB
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : Gen (LinComb L φ ε)) (t' : Gen (LinComb L φ' ε')) (ht : t.IsGen) (ht' : t'.IsGen) :
    (mulGen L φ ε φ' ε' t t').IsGen := by
  refine (isGen_iff L _).2 fun j j' => ?_
  have k₁ := congrArg (res (wchart_inl_le₂ L φ φ' j j'))
    ((isGen_iff L t).1 ht (j ∘ Sum.inl) (j' ∘ Sum.inl))
  have k₂ := congrArg (res (wchart_inr_le₂ L φ φ' j j'))
    ((isGen_iff L t').1 ht' (j ∘ Sum.inr) (j' ∘ Sum.inr))
  simp only [map_mul, res_res] at k₁ k₂
  rw [ts_mulGen, ts_mulGen, lcg_sum]
  simp only [map_mul, res_res]
  rw [k₁, k₂]
  exact mul_mul_mul_comm _ _ _ _
end ReciprocityTheory.ChartRestriction.G.Semi.LB
