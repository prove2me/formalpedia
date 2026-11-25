-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.ArcWit.uwMove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:20:21.443433+00:00
-- url     : https://prove2.me/submissions/7a7ab267-4ead-4358-9c60-2333c5567c4d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabMapCubical
import Definitions.Def_ReciprocityTheory_AdicCompleteness_IsAdicCompleteComapConstantCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_specOf_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_chartPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_of_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_rigIso_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabMap_cubical


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
set_option maxHeartbeats 1600000
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace ArcWit
theorem _root_.solution (hU : Out.UnifBaseChangeSt) (h5 : Out.Laws5) {Y : Model Xo c β} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : Out.AdmBase R I) {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X} (W W' : ArcWit Y a I f u χ) (ψ : W.t.G ≅ W'.t.G)
    [IsMonHom ψ.hom] (hφ : ψ.hom.left ≫ W'.m.φ = W.m.φ) (hact : ∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) :
    ∃ (bc : W.t.G ≅ (Over.pullback (Out.specOf (RingHom.id R))).obj W'.t.G) (D'' : Out.DegData R I)
      (hD : Out.IsPullDeg (RingHom.id R) W'.P.D.toPre D''.toPre) (U'' : Out.Unif I D'' W'.P.A W.t.G)
      (_ : Module (𝓞 E) D''.toPre.X) (oD : letI := H.starRing; D''.toPre.OAct (𝓞 E)),
      IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)) = ψ.hom.left ∧
      U''.LG = W.P.U.LG ∧
      U''.gen.hom.left ≫ W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) =
        pullback.fst W.t.G.hom (Out.jK R) ≫ ψ.hom.left ∧
      Out.IsPullUnif (RingHom.id R) hD bc W'.P.U U'' ∧
      (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧
      (letI := H.starRing; ∀ x, oD.onB.act x ≫ hD.e.hom =
        hD.e.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.P.oD.onB.act x)) ∧
      (letI := H.starRing; U''.toUnifPre.OLinear (𝓞 E) oD W'.P.oA W.t.act.toRingAct) ∧
      (letI := H.starRing; TraceFormTwistIso D''.toPre oD H.w0) := by
  let _ := H.starRing
  have hs := specOf_id R
  have gp₁ : IsGrpPullback W.t.G W'.t.G (Out.specOf (RingHom.id R)) ψ.hom.left :=
    (isGrpPullback_of_iso ψ).congr hs.symm rfl
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso gp₁ (isGrpPullback_pullback W'.t.G (Out.specOf (RingHom.id R)))
  have gpG : IsGrpPullback W'.P.A.A W'.t.G (Out.jK R) (W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R)) := by
    have := W'.P.U.gen_hom
    have : IsMonHom W'.P.U.gen.symm.hom := by show IsMonHom W'.P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso W'.P.U.gen.symm).comp (isGrpPullback_pullback W'.t.G (Out.jK R))).congr
      (Category.id_comp _) rfl
  have gp₂ : IsGrpPullback ((Over.pullback (Out.jK R)).obj W.t.G) W'.t.G (Out.jK R)
      (pullback.fst W.t.G.hom (Out.jK R) ≫ ψ.hom.left) :=
    ((isGrpPullback_pullback W.t.G (Out.jK R)).comp (isGrpPullback_of_iso ψ)).congr (Category.comp_id _) rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp₂ gpG
  have hgi : W'.P.U.gen.inv.left ≫ W'.P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (W'.P.A.L.pull eA.hom.left) (W'.P.U.LG.L.pull (pullback.fst W.t.G.hom (Out.jK R) ≫ bc.hom.left ≫
      pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)))) :=
    LBIso.chartPull (h := eA.hom.left ≫ W'.P.U.gen.inv.left)
      (chartPullSame W'.P.A.L (fun _ => eA.hom.left) (fun _ => W'.P.U.gen.hom.left) _ _ fun _ => by
        rw [Category.assoc, hgi, Category.comp_id])
      (chartPullSame W'.P.U.LG.L _ (fun _ => pullback.fst W'.t.G.hom (Out.jK R)) _ _ fun _ => by
        rw [hbc, ← heA]; simp only [Category.assoc]) W'.P.U.ext
  obtain ⟨wL', he', gL, rL⟩ := rigIso_congr W'.P.bundle (CubeMap.ofHom ψ.hom) (sabMap_cubical W.m W'.m ψ hφ) hbc
    (e := Out.specOf (RingHom.id R)) hs
  obtain ⟨Wo, hWo, hψW⟩ := h5.psiOnExists R I hR W'.P.D
  have hgen : (Out.specOf (RingHom.id R)).base (genericPoint (Spec (CommRingCat.of R))) ∈ Wo := by
    rw [hs]; exact hWo
  have hI : I.map (RingHom.id R) ≤ I := by rw [Ideal.map_id]
  obtain ⟨D'', hD, U'', hLG, hgenU, hPU⟩ := hU R R I I hR hR (RingHom.id R) hI W'.P.D W'.P.A W'.t.G W'.t.semi W'.P.U
    Wo hψW hgen W.t.G bc mbc W'.P.A rfl eA mE wA W.t.PP wL' he' gL rL
  have hbcact : ∀ x, W.t.act.toRingAct.act x ≫ bc.hom =
      bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.toRingAct.act x) := by
    intro x
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have a₂ : ((Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x)).left ≫
          pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)) = pullback.fst _ _ ≫ (W'.t.act.act x).left :=
        pullback.lift_fst _ _ _
      show (W.t.act.act x ≫ bc.hom).left ≫ _ =
        (bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x)).left ≫ _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, hbc, ← Category.assoc, hbc,
        ← Over.comp_left, hact, Over.comp_left]
    · exact (Over.w (W.t.act.act x ≫ bc.hom)).trans
        (Over.w (bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x))).symm
  have actA : ∀ x, (W'.P.oA.act x).left ≫ W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) =
      W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) ≫ (W'.t.act.act x).left := by
    intro x
    have e : W'.P.oA.act x ≫ W'.P.U.gen.inv = W'.P.U.gen.inv ≫ (Over.pullback (Out.jK R)).map (W'.t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (W'.P.lin.ext x)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have extA : ∀ x, (Over.pullback (Out.jK R)).map (W.t.act.toRingAct.act x) ≫ U''.gen.hom =
      U''.gen.hom ≫ W'.P.oA.act x := by
    intro x
    rw [hgenU]
    apply Over.OverMorphism.ext
    apply gpG.1.hom_ext
    · have a₁ : ((Over.pullback (Out.jK R)).map (W.t.act.act x)).left ≫ pullback.fst W.t.G.hom (Out.jK R) =
          pullback.fst W.t.G.hom (Out.jK R) ≫ (W.t.act.act x).left := pullback.lift_fst _ _ _
      have a₃ : (W.t.act.act x).left ≫ ψ.hom.left = ψ.hom.left ≫ (W'.t.act.act x).left := by
        rw [← Over.comp_left, hact, Over.comp_left]
      show ((Over.pullback (Out.jK R)).map (W.t.act.act x) ≫ eA.hom).left ≫ _ = (eA.hom ≫ W'.P.oA.act x).left ≫ _
      rw [Over.comp_left, Category.assoc, heA, ← Category.assoc, a₁, Category.assoc, a₃, Over.comp_left,
        Category.assoc, actA, reassoc_of% heA]
    · rw [Over.w, Over.w]
  obtain ⟨mod'', oD'', xl, el, lin'', w0''⟩ := h5.oLinBaseChange R R I I hR hR (RingHom.id R) W'.P.D W'.P.A W'.t.G W'.P.U
    W.t.G bc mbc W'.P.A D'' hD U'' hPU (𝓞 E) W'.P.oD W'.P.oA W'.t.act.toRingAct W'.P.lin W.t.act.toRingAct hbcact
    W'.P.oA extA
  refine ⟨bc, D'', hD, U'', mod'', oD'', mbc, hbc, hLG.trans W.P.bundle.symm, ?_, hPU, xl, el, lin'', w0'' H.w0 W'.P.w0⟩
  rw [hgenU]; exact heA
end ArcWit
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
