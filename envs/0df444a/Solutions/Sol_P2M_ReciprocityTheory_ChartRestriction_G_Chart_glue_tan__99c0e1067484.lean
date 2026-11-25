-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Chart_glue_tan__99c0e1067484
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:48:36.239375+00:00
-- url     : https://prove2.me/submissions/eaaba8c8-ba76-440e-bfaa-cadb657b3066

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Theorems.Thm_Bl_FirstBlockLemmaK_goal1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_glue_tan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
section Wrap
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] {s : S} (C : Chart (Gs G s))
  [Algebra.FinitePresentation (Localization.Away s) Γ((Gs G s).left, C.U)]
  {A : Type} [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A] [IsScalarTower S (Localization.Away s) A]
  {A' : Type} [CommRing A'] [Algebra S A'] [Algebra (Localization.Away s) A'] [IsScalarTower S (Localization.Away s) A']
  [Algebra A A'] [IsScalarTower (Localization.Away s) A A'] [IsScalarTower S A A']
  (M : Submonoid (Localization.Away s)) [IsLocalization (Algebra.algebraMapSubmonoid A M) A']
end Wrap
section Scale
variable {S : Type} [CommRing S]
private theorem dualMapS_fst' {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A']
    (j : A →ₐ[S] A') (y : DualNumber A) : (dualMapS j y).fst = j y.fst := by
  simp [dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]
private theorem dualMapS_snd' {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A']
    (j : A →ₐ[S] A') (y : DualNumber A) : (dualMapS j y).snd = j y.snd := by
  simp [dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]
variable {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
end Scale
section Over
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
end Over
end ReciprocityTheory.ChartRestriction.G.Chart
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    (w : ∀ k, sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G) (hw : ∀ k, TanS (w k))
    (hQ : ∀ k l, spMap (dualMapS (qL (s k) (s l))) ≫ w k = spMap (dualMapS (qR (s k) (s l))) ≫ w l) :
    ∃ v : sp (R₀ := S) (DualNumber S) ⟶ G, TanS v ∧
      ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v = w k := by
  refine glue_tan s hs w hw ?_
  intro k l T α β hαβ
  have hin : ∀ x : S, α (TrivSqZeroExt.inl (algebraMap S (Localization.Away (s k)) x)) =
      β (TrivSqZeroExt.inl (algebraMap S (Localization.Away (s l)) x)) := by
    intro x
    have h1 := RingHom.congr_fun hαβ (TrivSqZeroExt.inl x)
    simpa [dAway, dualMapR] using h1
  have heps : α (TrivSqZeroExt.inr 1) = β (TrivSqZeroExt.inr 1) := by
    have h1 := RingHom.congr_fun hαβ (TrivSqZeroExt.inr 1)
    simpa [dAway, dualMapR] using h1
  have hu : IsUnit (α (TrivSqZeroExt.inl (algebraMap S (Localization.Away (s k)) (s l)))) := by
    rw [hin]
    exact (IsLocalization.Away.algebraMap_isUnit (s l)).map (β.comp (TrivSqZeroExt.inlHom _ _))
  obtain ⟨g0, hg0⟩ : ∃ g0 : Qv (s k) (s l) →+* T, ∀ a,
      g0 (algebraMap (Localization.Away (s k)) (Qv (s k) (s l)) a) = α (TrivSqZeroExt.inl a) :=
    ⟨IsLocalization.Away.lift _ (g := α.comp (TrivSqZeroExt.inlHom _ _)) hu,
      fun a => IsLocalization.Away.lift_eq _ (g := α.comp (TrivSqZeroExt.inlHom _ _)) hu a⟩
  have he2 : α (TrivSqZeroExt.inr 1) * α (TrivSqZeroExt.inr 1) = 0 := by
    rw [← map_mul]; simp
  obtain ⟨gm, hgm⟩ : ∃ gm : DualNumber (Qv (s k) (s l)) →+* T, ∀ x,
      gm x = g0 x.fst + g0 x.snd * α (TrivSqZeroExt.inr 1) :=
    ⟨{ toFun := fun x => g0 x.fst + g0 x.snd * α (TrivSqZeroExt.inr 1)
       map_one' := by simp
       map_mul' := fun x y => by
         simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul,
           op_smul_eq_mul, map_add, map_mul]
         linear_combination (-(g0 x.snd * g0 y.snd)) * he2
       map_zero' := by simp
       map_add' := fun x y => by
         simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add]
         ring }, fun _ => rfl⟩
  have hdec : ∀ {R : Type} [CommRing R] (x : DualNumber R),
      x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inl x.snd * TrivSqZeroExt.inr 1 := by
    intro R _ x
    ext <;> simp
  have hR : g0.comp (qR (s k) (s l)).toRingHom = β.comp (TrivSqZeroExt.inlHom _ _) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (s l))
    ext x
    show g0 (qR (s k) (s l) (algebraMap S _ x)) = β (TrivSqZeroExt.inl (algebraMap S _ x))
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply S (Localization.Away (s k)) (Qv (s k) (s l)),
      hg0, hin]
  have hR' : ∀ a, g0 (qR (s k) (s l) a) = β (TrivSqZeroExt.inl a) := fun a => RingHom.congr_fun hR a
  have hα : α = gm.comp (dualMapS (qL (s k) (s l))).toRingHom := by
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, hgm]
    conv_lhs => rw [hdec x]
    rw [map_add, map_mul]
    simp [dualMapS_fst', dualMapS_snd', hg0]
  have hβ : β = gm.comp (dualMapS (qR (s k) (s l))).toRingHom := by
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, hgm]
    conv_lhs => rw [hdec x]
    rw [map_add, map_mul]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dualMapS_fst', dualMapS_snd', hR', heps]
  have hk := congrArg (fun f => f.left) (hQ k l)
  simp only [Over.comp_left, spMap, Over.homMk_left] at hk
  rw [hα, hβ, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc, hk]
end ReciprocityTheory.ChartRestriction.G.Chart
