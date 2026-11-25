-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.pmaps_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:48.003195+00:00
-- url     : https://prove2.me/submissions/124f41ef-82be-4767-b9af-1a7e2f75e17a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


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
set_option maxHeartbeats 1600000
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {g : R →+* R'} {D : Out.DegPre R}
    {D' : Out.DegPre R'} (hD : Out.IsPullDeg g D D') (F : Type) [Field F] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F]
    (hj : Out.jFK (R := R') F ≫ Out.jK R' ≫ spMap g = Out.jFK (R := R) F ≫ Out.jK R) (x : D'.X) :
    PMaps hD.w (K := PUnit) (fun _ => Out.jFK (R := R') F ≫ D'.xK x) (fun _ => Out.jFK (R := R) F ≫ D.xK (hD.xe x))
      (fun _ => -1) (LB.pullGen _ _ _ (D'.psi x) (Out.jFK (R := R') F))
      (LB.pullGen _ _ _ (D.psi (hD.xe x)) (Out.jFK (R := R) F)) (𝟙 _) := by
  intro Z r z p q hp hq
  obtain ⟨b, hb, hcorr⟩ := hD.psi_pr x
  set Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (Out.specOf g) with hΦ
  have hx : D'.xK x ≫ Φ = Out.jK R' ≫ Out.specOf g ≫ (D.c (hD.xe x)).left := by
    rw [← hD.c_pr x, ← Category.assoc]; rfl
  have hpt : Out.jFK (R := R') F ≫ D'.xK x ≫ Φ = Out.jFK (R := R) F ≫ D.xK (hD.xe x) := by
    rw [hx, ← Category.assoc (Out.jK R'), ← Category.assoc, ← Category.assoc (Out.jFK F)]
    exact (congrArg (· ≫ (D.c (hD.xe x)).left) ((Category.assoc _ _ _).trans hj)).trans (Category.assoc _ _ _)

  have hW : Out.jFK (R := R) F ≫ Out.jK R = (Out.jFK (R := R') F ≫ hD.g) ≫ hD.W.ι := by
    rw [Category.assoc, hD.g_comm]; exact hj.symm
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : Sp F ⟶ (Out.jK R ⁻¹ᵁ hD.W).toScheme, lam ≫ (Out.jK R ⁻¹ᵁ hD.W).ι = Out.jFK (R := R) F ∧
      lam ≫ (Out.jK R ∣_ hD.W) = Out.jFK (R := R') F ≫ hD.g :=
    ⟨(isPullback_morphismRestrict (Out.jK R) hD.W).lift _ _ hW.symm,
      (isPullback_morphismRestrict (Out.jK R) hD.W).lift_snd _ _ _,
      (isPullback_morphismRestrict (Out.jK R) hD.W).lift_fst _ _ _⟩
  have mp : Φ (D'.xK x (Out.jFK (R := R') F (r z))) ∈ D.P.L.U (p PUnit.unit) := hp PUnit.unit
  have mq : D'.xK x (Out.jFK (R := R') F (r z)) ∈ D'.P.L.U (q PUnit.unit) := hq PUnit.unit
  have mp' : D.xK (hD.xe x) (Out.jFK (R := R) F (r z)) ∈ D.P.L.U (p PUnit.unit) :=
    (congrArg (fun h => h (r z) ∈ D.P.L.U (p PUnit.unit)) hpt).mp mp
  have cW : hD.g ≫ (toUnit (Out.TW hD.W) ≫ D.c (hD.xe x)).left = D'.xK x ≫ Φ := by
    rw [hx, ← Category.assoc (Out.jK R'), ← hD.g_comm, Category.assoc]; rfl
  have mW : (toUnit (Out.TW hD.W) ≫ D.c (hD.xe x)).left (hD.g (Out.jFK (R := R') F (r z))) ∈ D.P.L.U (p PUnit.unit) :=
    (congrArg (fun h => h (Out.jFK (R := R') F (r z)) ∈ D.P.L.U (p PUnit.unit)) cW).mpr mp
  have one : ∀ {Y : Scheme.{0}} {B : Scheme.{0}} (M : LB B) (φ : Y ⟶ B) (y : Y) (j : M.ι), φ y ∈ M.U j →
      y ∈ LB.wchart M (fun _ : PUnit => φ) (fun _ => j) := fun M φ y j h => Set.mem_iInter.2 fun _ => h

  have m₁ : (r ≫ Out.jFK (R := R') F) z ∈ D'.xK x ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => p PUnit.unit) ⊓ D'.P.L.U (q PUnit.unit)) :=
    ⟨mem_pull.2 mp, mq⟩
  have e₁ := congrArg (gm (r ≫ Out.jFK (R := R') F) z
    (D'.xK x ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => p PUnit.unit) ⊓ D'.P.L.U (q PUnit.unit))))
    (hb (fun _ => p PUnit.unit) (q PUnit.unit))
  have e₁' := (gm_res _ z _ m₁ _).symm.trans (e₁.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ (D'.xK x) z
      ((D.P.L.pull Φ).U (fun _ => p PUnit.unit) ⊓ D'.P.L.U (q PUnit.unit)) m₁ _))) (gm_res _ z _ m₁ _))))

  have e₂ := (gm_corr D.P.L hcorr (r ≫ Out.jFK (R := R') F) z (p PUnit.unit) (one _ _ _ _ mp) (one _ _ _ _ mW)).trans
    (gm_pullGen D.P.L _ _ _ hD.g (r ≫ Out.jFK (R := R') F) z _ (one _ _ _ _ mW))

  have n₁ : (toUnit (Out.TW hD.W) ≫ D.c (hD.xe x)).left ((Out.jK R ∣_ hD.W) (lam (r z))) ∈ D.P.L.U (p PUnit.unit) :=
    (congrArg (fun h => (toUnit (Out.TW hD.W) ≫ D.c (hD.xe x)).left (h (r z)) ∈ D.P.L.U (p PUnit.unit)) l₂).mpr mW
  have n₂ : D.xK (hD.xe x) ((Out.jK R ⁻¹ᵁ hD.W).ι (lam (r z))) ∈ D.P.L.U (p PUnit.unit) :=
    (congrArg (fun h => D.xK (hD.xe x) (h (r z)) ∈ D.P.L.U (p PUnit.unit)) l₁).mpr mp'
  have e₃ := (gm_pullGen D.P.L _ _ _ (Out.jK R ∣_ hD.W) (r ≫ lam) z _ (one _ _ _ _ n₁)).symm.trans
    ((gm_corr D.P.L (hD.psiW.psi_eq (hD.xe x)) (r ≫ lam) z (p PUnit.unit) (one _ _ _ _ n₁) (one _ _ _ _ n₂)).trans
      (gm_pullGen D.P.L _ _ _ (Out.jK R ⁻¹ᵁ hD.W).ι (r ≫ lam) z _ (one _ _ _ _ n₂)))
  rw [Category.assoc, l₂, Category.assoc, l₁, ← Category.assoc] at e₃
  rw [Category.comp_id, Fintype.prod_unique]
  refine (gm_pullGen D.P.L (fun _ : PUnit => D.xK (hD.xe x)) _ (D.psi (hD.xe x)) (Out.jFK (R := R) F) r z p
    (Set.mem_iInter.2 fun _ => mp')).trans ?_
  refine e₃.symm.trans (e₂.symm.trans (e₁'.trans (congrArg₂ (· * ·) ?_ ?_)))
  · rw [Category.assoc]; rfl
  · exact (gm_pullGen D'.P.L _ _ _ (Out.jFK (R := R') F) r z _ (one _ _ _ _ mq)).symm
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
