-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:10.970978+00:00
-- url     : https://prove2.me/submissions/3ec097b6-0f1d-4a43-899e-854ea84977a0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_div
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
open AlgebraicGeometry CategoryTheory Limits Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
section Germs
end Germs
section Transfer
variable {X Y Z Y' : Scheme.{0}}
private theorem germ_cocycle_lemma_3 {L : LB X} (hL : L.IsLB) (i j k : L.ι) (y : X)
    (hij : y ∈ L.U i ⊓ L.U j) (hjk : y ∈ L.U j ⊓ L.U k) (hik : y ∈ L.U i ⊓ L.U k) :
    gU y hij (L.g i j) * gU y hjk (L.g j k) = gU y hik (L.g i k) := by
  have hm : y ∈ L.U i ⊓ L.U j ⊓ L.U k := ⟨⟨hij.1, hij.2⟩, hjk.2⟩
  have key := congrArg (gU y hm) (hL.cocycle i j k)
  simp only [map_mul, gU_res] at key
  exact key
private theorem germ_self_lemma_4 {L : LB X} (hL : L.IsLB) (i : L.ι) (y : X) (h : y ∈ L.U i ⊓ L.U i) :
    gU y h (L.g i i) = 1 := by
  have hi : y ∈ L.U i := h.1
  have key := congrArg (gU y hi) (hL.g_self i)
  simp only [map_one, gU_res] at key
  exact key
private theorem alg_lemma_8 {G : Type*} [CommGroup G] (ab aa' a'b' ab' b'b bb' : G)
    (h1 : aa' * a'b' = ab') (h2 : ab' * b'b = ab) (h3 : bb' * b'b = 1) :
    ab = aa' * bb'⁻¹ * a'b' := by
  rw [← h2, ← h1, inv_eq_of_mul_eq_one_right h3]
  exact mul_right_comm _ _ _
end Transfer
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
variable {X Y Z Y' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
theorem _root_.solution (L : LB X) (hL : L.IsLB) : ∃ t : LB.Gen (LB.div L L), t.IsGen := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p p' => ?_⟩
  apply unit_ext
  intro y hy
  have ha : y ∈ L.U p.1 := hy.1.1
  have hb : y ∈ L.U p.2 := hy.1.2
  have ha' : y ∈ L.U p'.1 := hy.2.1
  have hb' : y ∈ L.U p'.2 := hy.2.2
  have c1 := germ_cocycle_lemma_3 hL p.1 p'.1 p'.2 y ⟨ha, ha'⟩ ⟨ha', hb'⟩ ⟨ha, hb'⟩
  have c2 := germ_cocycle_lemma_3 hL p.1 p'.2 p.2 y ⟨ha, hb'⟩ ⟨hb', hb⟩ ⟨ha, hb⟩
  have c3 := (germ_cocycle_lemma_3 hL p.2 p'.2 p.2 y ⟨hb, hb'⟩ ⟨hb', hb⟩ ⟨hb, hb⟩).trans
    (germ_self_lemma_4 hL p.2 y ⟨hb, hb⟩)
  exact (gU_res inf_le_left y hy _).trans ((alg_lemma_8 _ _ _ _ _ _ c1 c2 c3).trans
    ((congrArg₂ (· * ·) (germ_div L L p p' y hy) (gU_res inf_le_right y hy _)).symm.trans
      (map_mul (gU y hy) _ _).symm))
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
