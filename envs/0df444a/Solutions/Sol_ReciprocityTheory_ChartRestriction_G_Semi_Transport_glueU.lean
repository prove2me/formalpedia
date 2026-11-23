-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Transport.glueU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:10.891797+00:00
-- url     : https://prove2.me/submissions/0e29858c-92a4-4172-87af-b030bde89cf3

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
theorem _root_.solution {J : Type} (V : X.Opens) (W : J → X.Opens) (hW : ∀ i, W i ≤ V) (hc : V ≤ iSup W)
    (u : ∀ i, Γ(X, W i)ˣ)
    (h : ∀ i j (x : X) (hx : x ∈ W i ⊓ W j), gU x hx.1 (u i) = gU x hx.2 (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, res (hW i) s = u i := by
  have hcomp : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i) =
      res (inf_le_right : W i ⊓ W j ≤ W j) (u j) := by
    intro i j
    apply unit_ext
    intro x hx
    simp only [gUres_lemma]
    exact h i j x hx
  have hcomp' : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i)⁻¹ =
      res (inf_le_right : W i ⊓ W j ≤ W j) (u j)⁻¹ := by
    intro i j
    rw [map_inv, map_inv, hcomp i j]
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => ((u i : Γ(X, W i)ˣ) : Γ(X, W i))) (fun i j => congrArg Units.val (hcomp i j))
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => (((u i)⁻¹ : Γ(X, W i)ˣ) : Γ(X, W i))) (fun i j => congrArg Units.val (hcomp' i j))
  have hst : s * t = 1 := by
    apply X.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
    intro i
    simp only [map_mul, map_one, hs, ht]
    exact (u i).mul_inv
  refine ⟨Units.mkOfMulEqOne (s : Γ(X, V)) t hst, fun i => Units.ext ?_⟩
  exact hs i
end ReciprocityTheory.ChartRestriction.G.Semi.Transport
