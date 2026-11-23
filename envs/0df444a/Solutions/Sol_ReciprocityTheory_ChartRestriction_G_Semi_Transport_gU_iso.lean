-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Transport.gU_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:49.739522+00:00
-- url     : https://prove2.me/submissions/d7eb878a-1efc-46e2-8d00-b3f6f6d1391f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Transport
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res)
variable {X : Scheme.{0}}
variable {A B C : LB X}
namespace ReciprocityTheory.ChartRestriction.G.Semi.Transport
theorem _root_.solution (w : LB.Iso A B) (hw : w.IsGen) (p p' : B.ι) (q q' : A.ι) (x : X)
    (h : x ∈ A.U q ⊓ B.U p) (h' : x ∈ A.U q' ⊓ B.U p') :
    gU x (le_divU p q h) (w.s (pq p q)) =
      gU x (⟨h.2, h'.2⟩ : x ∈ B.U p ⊓ B.U p') (B.g p p') *
        (gU x (⟨h.1, h'.1⟩ : x ∈ A.U q ⊓ A.U q') (A.g q q'))⁻¹ * gU x (le_divU p' q' h') (w.s (pq p' q')) := by
  have h1 := gU_isGen hw x (le_divU p q h) (le_divU p' q' h')
  have hd := gU_div B A (pq p q) (pq p' q') x (le_divU p q h) (le_divU p' q' h')
  exact h1.trans (congrArg (· * _) hd)
end ReciprocityTheory.ChartRestriction.G.Semi.Transport
