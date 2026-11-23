-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Transport.gU_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:30.017232+00:00
-- url     : https://prove2.me/submissions/a79f8e81-2924-4eac-ab01-4cd5b787c9ca

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
theorem _root_.solution {L : LB X} (hL : L.IsLB) {i : L.ι} (x : X) (hi : x ∈ L.U i) :
    gU x (⟨hi, hi⟩ : x ∈ L.U i ⊓ L.U i) (L.g i i) = 1 := by
  exact (gUres_lemma _ _ _ _).symm.trans ((congrArg (gU x hi) (hL.g_self i)).trans (map_one _))
end ReciprocityTheory.ChartRestriction.G.Semi.Transport
