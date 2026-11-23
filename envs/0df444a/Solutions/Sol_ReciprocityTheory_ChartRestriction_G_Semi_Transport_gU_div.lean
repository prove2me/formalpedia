-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Transport.gU_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:21.535518+00:00
-- url     : https://prove2.me/submissions/4cf7fa72-eaaf-4a80-8956-7c1e09672e81

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace ReciprocityTheory.ChartRestriction.G.Semi.Transport
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res)
variable {X : Scheme.{0}}
private theorem gUres_lemma {O O' : X.Opens} (hle : O' ≤ O) (x : X) (hx : x ∈ O')
    (s : Γ(X, O)ˣ) : gU x hx (res hle s) = gU x (hle hx) s :=
  gU_res hle x hx s
section Transport
variable {A B : LB X}
end Transport
section InvComp
variable {A B C : LB X}
end InvComp
end ReciprocityTheory.ChartRestriction.G.Semi.Transport
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Transport
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res)
variable {X : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Semi.Transport
theorem _root_.solution (B A : LB X) (p q : (LB.div B A).ι) (x : X) (hp : x ∈ (LB.div B A).U p)
    (hq : x ∈ (LB.div B A).U q) :
    gU x (⟨hp, hq⟩ : x ∈ (LB.div B A).U p ⊓ (LB.div B A).U q) ((LB.div B A).g p q) =
      gU x (⟨hp.1, hq.1⟩ : x ∈ B.U p.1 ⊓ B.U q.1) (B.g p.1 q.1) *
        (gU x (⟨hp.2, hq.2⟩ : x ∈ A.U p.2 ⊓ A.U q.2) (A.g p.2 q.2))⁻¹ := by
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gUres_lemma _ _ _ _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (gUres_lemma _ _ _ _))))
end ReciprocityTheory.ChartRestriction.G.Semi.Transport
