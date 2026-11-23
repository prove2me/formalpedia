-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.Canon.canonGen_corr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:02.175591+00:00
-- url     : https://prove2.me/submissions/235aeecd-f488-40bc-9ded-6f41b2dcdc57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_Canon_gW_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_Canon_gW_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out.Canon
variable {X Y : Scheme.{0}} (L : LB X)
variable {L}
variable {K K' : Type} [Fintype K] [Fintype K']
variable (L)
variable {L}
namespace ReciprocityTheory.ChartRestriction.G.Out.Canon
theorem _root_.solution (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X))
    (ε' : K' → ℤ) (hsub : ∀ k, ∃ k', φ' k' = φ k) (t : LB.Gen (LB.LinComb L φ ε)) :
    LB.Gen.Corr L φ ε φ' ε' t (canonGen L φ ε φ' ε' hsub t) := by
  intro j j' _ hj' hjj'
  have hj : jhat φ ε φ' hsub j' = j :=
    funext fun k => (hjj' k _ (hsub k).choose_spec.symm).symm
  have hc : corrU (L := L) φ' ε' j' = 1 := by
    refine Finset.prod_eq_one fun k' _ => ?_
    have hR : R φ' j' (φ' k') ⟨k', rfl⟩ = j' k' :=
      hj' _ _ (⟨k', rfl⟩ : ∃ c, φ' c = φ' k').choose_spec
    refine (congrArg (· ^ ε' k') ((gW_congr rfl rfl hR _
      (lePI (lcle φ' ε' j' k') (lcle φ' ε' j' k'))).trans (gW_self hL _ _ _))).trans ?_
    exact one_zpow _
  subst hj
  exact (res_res' _ _ _).symm.trans (congrArg (res _) ((mul_one _).symm.trans
    (congrArg (fun c => res (wchart_le_jhat φ ε φ' ε' hsub j') (t.s (jhat φ ε φ' hsub j')) * c)
      hc.symm)))
end ReciprocityTheory.ChartRestriction.G.Out.Canon
