-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.exists_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:59:57.689243+00:00
-- url     : https://prove2.me/submissions/bef99910-6611-483d-8766-540843edec0e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenThick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_toW_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_app_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_app_fst_tq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_toW_mul_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
noncomputable section
variable {R : Type} [CommRing R]
variable [IsDomain R]
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] {a : R} (ha : a ≠ 0)
    {J : Ideal R} (hJ : J ≤ Ideal.span {a})
    (V : X.Opens) (x : Γ(X, V)) (hx : (pullback.fst p (tq J)).app V x = 0) :
    ∃ g : Γ(X, V), x = toW p V a * g := by
  classical
  set π := pullback.fst p (tq J)
  let ι := {W : X.affineOpens // (W : X.Opens) ≤ V}
  let U : ι → X.Opens := fun W => W.1
  have hloc : ∀ W : ι, ∃ g : Γ(X, U W), (X.presheaf.map (homOfLE W.2).op).hom x = toW p (U W) a * g := by
    intro W
    have h0 : (π.app (U W)).hom ((X.presheaf.map (homOfLE W.2).op).hom x) = 0 := by
      rw [← app_res, hx, map_zero]
    have hm := Ideal.map_mono hJ ((app_fst_tq p J (U W) W.1.2).2 _ h0)
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hm
    obtain ⟨g, hg⟩ := hm
    exact ⟨g, by rw [← hg, mul_comm]⟩
  choose g hg using hloc
  have hcover : V ≤ iSup U := by
    intro y hy
    obtain ⟨W, hW, hyW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWV⟩, hyW⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U g := by
    intro i j
    show (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (g i) =
      (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (g j)
    rw [← sub_eq_zero]
    apply toW_mul_eq_zero p _ ha
    rw [mul_sub]
    have e1 := congrArg (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (hg i)
    have e2 := congrArg (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (hg j)
    rw [map_mul, toW_res, ← CommRingCat.comp_apply, ← Functor.map_comp] at e1 e2
    rw [sub_eq_zero]
    exact e1.symm.trans e2
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf U V (fun i => homOfLE i.2) hcover g hcompat
  refine ⟨s, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf U V (fun i => homOfLE i.2) hcover
  intro i
  show (X.presheaf.map (homOfLE i.2).op).hom x = (X.presheaf.map (homOfLE i.2).op).hom (toW p V a * (show Γ(X, V) from s))
  rw [hg i, map_mul, toW_res]
  exact congrArg _ (hs i).symm
end ReciprocityTheory.ChartRestriction.G.DVR.TG
