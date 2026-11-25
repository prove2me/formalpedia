-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.qkPullExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:04:51.699299+00:00
-- url     : https://prove2.me/submissions/070efd29-6d63-402b-b912-74532e96d67f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_of_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cub_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cPoint_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubeMap_comp_proj_three
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_hom_ext_triple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isAdd_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isIota_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isZero_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mul_left_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pmaps_psi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'}
set_option maxHeartbeats 2000000
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (hG : GlobalFnsSt) : QkPullExistsSt := by
  intro R R' _ _ _ _ φ D D' hD F _ _ _ hF k p'
  have gp := pull_grp hD
  have hw := (isGen_iff hD.w).1 hD.w_gen
  have hj : jFK (R := R') F ≫ jK R' ≫ spMap φ = jFK (R := R) F ≫ jK R :=
    ((congrArg (jFK (R := R') F ≫ ·) (spMap_comp φ _).symm).trans (spMap_comp _ _).symm).trans
      ((congrArg spMap (RingHom.ext fun r => (hF r).symm)).trans (spMap_comp _ _))
  have hT : (TF (R := R') F).hom ≫ spMap φ = (TF (R := R) F).hom := (Category.assoc _ _ _).trans hj
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  let β : (TF (R := R') F ⟶ D'.P.A) → (TF (R := R) F ⟶ D.P.A) := fun x =>
    Over.homMk (x.left ≫ Φ) ((Over.w (pushPt gp.1.w x)).trans hT)
  have βm : ∀ x y, β (x * y) = β x * β y := fun x y => Over.OverMorphism.ext
    ((gp.2 _ x y _ _ rfl rfl).symm.trans (mul_left_congr hT (pushPt gp.1.w x) (pushPt gp.1.w y) (β x) (β y) rfl rfl))
  have β1 : β 1 = 1 := mul_eq_left.1 ((βm 1 1).symm.trans (congrArg β (_root_.mul_one 1)))
  have βc : ∀ χ, β (cP D' _ χ) = cP D _ (hD.xe χ) := fun χ => Over.OverMorphism.ext (by
    show ((TF (R := R') F).hom ≫ (D'.c χ).left) ≫ Φ = (TF (R := R) F).hom ≫ (D.c (hD.xe χ)).left
    rw [Category.assoc, hD.c_pr, ← Category.assoc]
    exact congrArg (· ≫ _) hT)
  let Ω : ∀ (y : Sp F) (_ : (Sp F ⟶ D.P.A.left) → D.P.L.ι) (_ : (Sp F ⟶ D'.P.A.left) → D'.P.L.ι),
      (TF (R := R') F ⟶ D'.P.A) → ((Sp F).presheaf.stalk y)ˣ := fun y J J' x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)
  have cub : ∀ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' → ∀ a b c : TF (R := R') F ⟶ D'.P.A,
      thS D y J (β a) (β b) (β c) =
        Ω y J J' (a * b * c) * (Ω y J J' (a * b))⁻¹ * (Ω y J J' (a * c))⁻¹ * (Ω y J J' (b * c))⁻¹ * Ω y J J' a *
          Ω y J J' b * Ω y J J' c * (Ω y J J' 1)⁻¹ * thS D' y J' a b c := by
    intro y J J' hJ hJ' a b c
    have e := cub_pull hG hD (T' := TF (R := R') F) hJ hJ' a b c
    have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (β a) (lift (β b) (β c))).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => gw hD.w q y (J (q ≫ Φ)) (J' q))) rfl)
  have good' : ∀ y : Sp F, ∃ J', Good D'.P.L y J' := fun y => by
    choose I hI using fun χ : Sp F ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
    exact ⟨I, hI⟩
  have gφ : ∀ (b : TF (R := R') F ⟶ D'.P.A) χ i, DegPre.gtφ D' F b χ i ≫ Φ = DegPre.gtφ D F (β b) (hD.xe χ) i := by
    intro b χ i
    fin_cases i
    · exact congrArg (fun q => q.left) ((βm (cP D' _ χ) b).trans (congrArg (· * β b) (βc χ)))
    · exact congrArg (fun q => q.left) (βc χ)
    · rfl
    · exact congrArg (fun q => q.left) β1
  have ex : ∀ g' : GtPtF D' F, ∃ g : GtPtF D F, g.b = β g'.b ∧ ∀ χ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' →
      vS (g.s (hD.xe χ)) y J = (Ω y J J' (cP D' _ χ * g'.b))⁻¹ * Ω y J J' (cP D' _ χ) * Ω y J J' g'.b *
        (Ω y J J' 1)⁻¹ * vS (g'.s χ) y J' := by
    intro g'
    choose t ht hv using fun χ => exists_up hw D.P.isLB D'.P.isLB (g'.s χ) (g'.isGen χ)
    have vt : ∀ χ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' → vS (t χ) y J =
        (Ω y J J' (cP D' _ χ * g'.b))⁻¹ * Ω y J J' (cP D' _ χ) * Ω y J J' g'.b * (Ω y J J' 1)⁻¹ *
          vS (g'.s χ) y J' := fun χ y J J' hJ hJ' => by
      refine (hv χ _ (𝟙 _) y _ _ (hJ.mem _ _) (hJ'.mem _ _)).trans (congrArg₂ (· * ·) ?_ rfl)
      refine Eq.trans ?_ (prod_gt g'.b χ (fun q => gw hD.w q y (J (q ≫ Φ)) (J' q)))
      simp only [pw, Category.id_comp]; rfl
    obtain ⟨g, hb, hg⟩ := exists_gt (β g'.b) (fun χ => t (hD.xe.symm χ)) (fun χ => ht _) (fun χ U _ h =>
        Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.gtε i)
          ((gφ g'.b _ i).trans (by rw [AddEquiv.apply_symm_apply]))) (fun y J hJ => by
        obtain ⟨J', hJ'⟩ := good' y
        have z : vS (g'.s 0) y J' = 1 := (val_corr hJ' g'.s_zero _).trans (val_one _)
        show vS (t (hD.xe.symm 0)) y J = 1
        rw [map_zero, vt 0 y J J' hJ hJ', cPoint_zero, _root_.one_mul, z]
        simp [mul_comm]) (fun χ χ' y J hJ => by
        obtain ⟨J', hJ'⟩ := good' y
        obtain ⟨χ, rfl⟩ := hD.xe.surjective χ
        obtain ⟨χ', rfl⟩ := hD.xe.surjective χ'
        have e₀ := gt_mul (𝟙 (TF (R := R') F)) hJ' g' χ χ'
        rw [Category.id_comp] at e₀
        have e : vS (g'.s (χ + χ')) y J' * thS D' y J' (cP D' _ χ) (cP D' _ χ') g'.b = vS (g'.s χ) y J' * vS (g'.s χ') y J' := e₀
        show vS (t (hD.xe.symm (hD.xe χ + hD.xe χ'))) y J * thS D y J (cP D _ (hD.xe χ)) (cP D _ (hD.xe χ')) (β g'.b) =
          vS (t (hD.xe.symm (hD.xe χ))) y J * vS (t (hD.xe.symm (hD.xe χ'))) y J
        rw [← map_add, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, ← βc, ← βc,
          cub y J J' hJ hJ', vt _ y J J' hJ hJ', vt _ y J J' hJ hJ', vt _ y J J' hJ hJ', cPoint_add]
        apply Additive.ofMul.injective
        have e' := congrArg Additive.ofMul e
        simp only [ofMul_mul, ofMul_inv] at e' ⊢
        linear_combination (norm := abel) e')
    refine ⟨g, hb, fun χ y J J' hJ hJ' => (hg _ y J hJ).trans ?_⟩
    show vS (t (hD.xe.symm (hD.xe χ))) y J = _
    rw [AddEquiv.symm_apply_apply]; exact vt χ y J J' hJ hJ'
  choose up hb hv using ex
  have add : ∀ g g' g'' : GtPtF D' F, g.IsAdd g' g'' → (up g).IsAdd (up g') (up g'') := fun g g' g'' h => by
    obtain ⟨b₁, v₁⟩ := (isAdd_iff _ _ _).1 h
    refine (isAdd_iff _ _ _).2 ⟨by rw [hb, hb, hb, b₁, βm], fun χ y J hJ => ?_⟩
    obtain ⟨J', hJ'⟩ := good' y
    obtain ⟨χ, rfl⟩ := hD.xe.surjective χ
    have e : vS (g''.s χ) y J' * thS D' y J' (cP D' _ χ) g.b g'.b = vS (g.s χ) y J' * vS (g'.s χ) y J' := v₁ χ y J' hJ'
    show vS ((up g'').s (hD.xe χ)) y J * thS D y J (cP D _ (hD.xe χ)) (up g).b (up g').b =
      vS ((up g).s (hD.xe χ)) y J * vS ((up g').s (hD.xe χ)) y J
    have c := cub y J J' hJ hJ' (cP D' _ χ) g.b g'.b
    rw [_root_.mul_assoc (cP D' _ χ), ← b₁] at c
    rw [hv _ _ y J J' hJ hJ', hv _ _ y J J' hJ hJ', hv _ _ y J J' hJ hJ', hb, hb, ← βc, c]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  have vψ : ∀ χ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' →
      vK (D.psi (hD.xe χ)) y J = (Ω y J J' (cP D' _ χ))⁻¹ * vK (D'.psi χ) y J' := fun χ y J J' hJ hJ' => by
    have a₁ : jFK (R := R') F ≫ D'.xK χ = (cP D' (TF (R := R') F) χ).left := (Category.assoc _ _ _).symm
    have a₂ : jFK (R := R) F ≫ D.xK (hD.xe χ) = (cP D' (TF (R := R') F) χ).left ≫ Φ :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun q => q.left) (βc χ).symm)
    have e := pmaps_psi hD F hj χ _ (𝟙 _) y (fun _ => J ((cP D' (TF (R := R') F) χ).left ≫ Φ))
      (fun _ => J' (cP D' (TF (R := R') F) χ).left) (fun _ => by rw [a₁]; exact hJ _) (fun _ => by rw [a₁]; exact hJ' _)
    rw [Fintype.prod_unique, zpow_neg_one, Category.id_comp, Category.id_comp] at e
    refine (val_pull hJ _ _ _).symm.trans ((val_of _ _ y J _ (fun _ => by rw [Category.id_comp, a₂])).trans (e.trans
      (congrArg₂ (· * ·) (by rw [a₁]) ((val_of _ _ y J' _ (fun _ => by rw [Category.id_comp, a₁])).symm.trans
        (val_pull hJ' _ _ _)))))
  have vρ : ∀ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' →
      vK D.rigK y J = Ω y J J' 1 * vK D'.rigK y J' := fun y J J' hJ hJ' => by
    have pm := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le Φ (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
    have a₁ : (TF (R := R') F).hom ≫ eSec D'.P.A = (1 : TF (R := R') F ⟶ D'.P.A).left := rfl
    have a₂ : (TF (R := R) F).hom ≫ eSec D.P.A = (1 : TF (R := R') F ⟶ D'.P.A).left ≫ Φ :=
      congrArg (fun q => q.left) β1.symm
    have e := pm _ (TF (R := R') F).hom y (fun _ => J ((1 : TF (R := R') F ⟶ D'.P.A).left ≫ Φ))
      (fun _ => J' (1 : TF (R := R') F ⟶ D'.P.A).left) (fun _ => hJ _) (fun _ => hJ' _)
    rw [Fintype.prod_unique, zpow_one, hT] at e
    have b₁ : (𝟙 _ ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left = (TF (R := R) F).hom := by rw [Category.id_comp]; rfl
    have b₂ : (𝟙 _ ≫ jFK (R := R') F) ≫ (toUnit (TK R')).left = (TF (R := R') F).hom := by rw [Category.id_comp]; rfl
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
    rw [b₁, b₂]
    exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans e
  have vτ : ∀ {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) F] (D : DegPre R) (a b : D.X) (y : Sp F) J,
      Good D.P.L y J → vK (D.tau a b) y J =
      vK (D.psi (a + b)) y J * (vK (D.psi a) y J)⁻¹ * (vK (D.psi b) y J)⁻¹ * (vK D.rigK y J)⁻¹ := fun D a b y J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  obtain ⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩ := p'.eq
  obtain ⟨ιb, ιv⟩ := (isIota_iff _ _).1 hι
  refine ⟨⟨hD.xe p'.y, up p'.g, up h, ⟨fun i => up (gs i), ?_, fun i => add _ _ _ (gst i), congrArg up gl⟩,
    (isIota_iff _ _).2 ⟨by rw [hb, ιb, βc], fun χ y J hJ => ?_⟩⟩, (hD.xe.symm_apply_apply _).symm,
    (congrArg (fun q => q.left) (hb p'.g)).symm, fun χ => ?_⟩
  · obtain ⟨z₁, z₂⟩ := (isZero_iff _).1 g₀
    refine (isZero_iff _).2 ⟨by rw [hb, z₁, β1], fun χ y J hJ => ?_⟩
    obtain ⟨J', hJ'⟩ := good' y
    obtain ⟨χ, rfl⟩ := hD.xe.surjective χ
    have z₃ : vS ((gs 0).s χ) y J' = 1 := z₂ _ y J' hJ'
    show vS ((up (gs 0)).s (hD.xe χ)) y J = 1
    rw [hv _ _ y J J' hJ hJ', z₃, z₁, _root_.mul_one]
    simp
  · obtain ⟨J', hJ'⟩ := good' y
    obtain ⟨χ, rfl⟩ := hD.xe.surjective χ
    have ι₁ : vS (h.s χ) y J' = vK (D'.tau p'.y χ) y J' := ιv _ y J' hJ'
    show vS ((up h).s (hD.xe χ)) y J = vK (D.tau (hD.xe p'.y) (hD.xe χ)) y J
    rw [hv _ _ y J J' hJ hJ', ι₁, ιb, vτ D _ _ y J hJ, vτ D' _ _ y J' hJ', ← map_add, vψ _ y J J' hJ hJ',
      vψ _ y J J' hJ hJ', vψ _ y J J' hJ hJ', vρ y J J' hJ hJ', cPoint_add, mul_comm (cP D' _ χ)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have hψ : ∀ i, DegPre.gtφ D' F p'.g.b χ i ≫ Φ = 𝟙 _ ≫ DegPre.gtφ D F (up p'.g).b (hD.xe χ) i := fun i => by
      rw [Category.id_comp, hb]; exact gφ _ _ i
    exact ⟨hψ, maps_of_good hw D.P.isLB D'.P.isLB _ (p'.g.isGen χ) _ ((up p'.g).isGen _) hψ fun y J J' hJ hJ' =>
      (hv p'.g χ y J J' hJ hJ').trans (congrArg₂ (· * ·)
        (prod_gt p'.g.b χ (fun r => gw hD.w r y (J (r ≫ Φ)) (J' r))).symm rfl)⟩
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
