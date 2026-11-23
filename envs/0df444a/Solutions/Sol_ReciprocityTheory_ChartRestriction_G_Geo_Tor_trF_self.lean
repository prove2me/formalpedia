-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:45.66765+00:00
-- url     : https://prove2.me/submissions/03ecce9f-43a4-48cb-b99e-92559adb53f5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {M : LB X} (hM : M.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) {j : K → M.ι}
    (hj : r z ∈ LB.wchart M φ j) : trF φ ε r z j j = 1 := by
  have hg : ∀ i, M.g i i = 1 := by
    intro i
    have h1 := hM.g_self i
    have h2 : ∀ g : Γ(X, M.U i ⊓ M.U i)ˣ, g = res (inf_le_left : M.U i ⊓ M.U i ≤ M.U i)
        (res (le_inf le_rfl le_rfl : M.U i ≤ M.U i ⊓ M.U i) g) := by
      intro g
      have e : X.presheaf.map (homOfLE (le_inf le_rfl le_rfl : M.U i ≤ M.U i ⊓ M.U i)).op ≫
          X.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ M.U i ≤ M.U i)).op = 𝟙 _ := by
        rw [← Functor.map_comp]
        exact X.presheaf.map_id _
      ext
      exact (congrArg (fun φ => CommRingCat.Hom.hom φ (g : Γ(X, M.U i ⊓ M.U i))) e).symm
    rw [h2 (M.g i i), h1, map_one]
  simp only [trF, hg, map_one, one_zpow, Finset.prod_const_one]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
