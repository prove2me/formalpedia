-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Transport.gU_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:48.848813+00:00
-- url     : https://prove2.me/submissions/16c7a941-ec86-4e29-909f-488f0643d42a

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
theorem _root_.solution {L : LB X} (hL : L.IsLB) {i j k : L.ι} (x : X) (hi : x ∈ L.U i) (hj : x ∈ L.U j)
    (hk : x ∈ L.U k) :
    gU x (⟨hi, hj⟩ : x ∈ L.U i ⊓ L.U j) (L.g i j) * gU x (⟨hj, hk⟩ : x ∈ L.U j ⊓ L.U k) (L.g j k) =
      gU x (⟨hi, hk⟩ : x ∈ L.U i ⊓ L.U k) (L.g i k) := by
  have e := congrArg (gU x (⟨⟨hi, hj⟩, hk⟩ : x ∈ L.U i ⊓ L.U j ⊓ L.U k)) (hL.cocycle i j k)
  exact (congrArg₂ (· * ·) (gUres_lemma _ _ _ _) (gUres_lemma _ _ _ _)).symm.trans
    ((map_mul _ _ _).symm.trans (e.trans (gUres_lemma _ _ _ _)))
end ReciprocityTheory.ChartRestriction.G.Semi.Transport
