-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:11:36.374183+00:00
-- url     : https://prove2.me/submissions/d97838c3-56df-4aca-ad07-f16232682cb4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_closure_eq_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_range
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_top
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__comp_88757af08841
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_ValAt_valAt__ne_zero_iff_2a770214a5a4
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_ValAt_valAt__res_9bf5469fe96a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
variable {g : ℕ} {X Y : Scheme.{0}} (f : Y ⟶ X) (u : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y))
  (he : ∀ z, e z ≫ f = u)
set_option maxHeartbeats 800000
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (hol : IsHolFam e) (V : (pullback f u).Opens) (φ : Γ(pullback f u, V))
    (z0 : Fin g → ℂ) (hz0 : ⊤ ≤ vtfLift f u e he z0 ⁻¹ᵁ V) :
    ∃ N : Set (Fin g → ℂ), IsOpen N ∧ z0 ∈ N ∧ (∀ z ∈ N, ⊤ ≤ vtfLift f u e he z ⁻¹ᵁ V) ∧
      DifferentiableOn ℂ (fun z => valAt' (vtfLift f u e he z) V φ) N := by
  classical
  obtain ⟨W, hW, huW, -⟩ := exists_isAffineOpen_mem_and_subset (x := u cpt) (U := ⊤) trivial
  have hfy : e z0 cpt ∈ f ⁻¹ᵁ W := by
    show f (e z0 cpt) ∈ W
    rw [← Scheme.Hom.comp_apply, he]
    exact huW
  obtain ⟨U, hU, hyU, hUW⟩ := exists_isAffineOpen_mem_and_subset hfy
  have : IsAffine U := hU
  have : IsAffine W := hW
  have hUr : Set.range (U.ι ≫ f) ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact hUW y.2
  let fU : U.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι (U.ι ≫ f) hUr
  let uW : Sp ℂ ⟶ W.toScheme := IsOpenImmersion.lift W.ι u (vtf_range u W (top_le_of_mem huW))
  have hSU : IsOpen {z | ⊤ ≤ e z ⁻¹ᵁ U} := (hol U 0).1
  have h0U : ⊤ ≤ e z0 ⁻¹ᵁ U := top_le_of_mem hyU
  let eU : (Fin g → ℂ) → (Sp ℂ ⟶ U.toScheme) := fun z =>
    if h : ⊤ ≤ e z ⁻¹ᵁ U then IsOpenImmersion.lift U.ι (e z) (vtf_range (e z) U h)
    else IsOpenImmersion.lift U.ι (e z0) (vtf_range (e z0) U h0U)
  have heU : ∀ z, ⊤ ≤ e z ⁻¹ᵁ U → eU z ≫ U.ι = e z := fun z h => by
    simp only [eU, dif_pos h, IsOpenImmersion.lift_fac]
  have heU' : ∀ z, eU z ≫ fU = uW := fun z => by
    rw [← cancel_mono W.ι]
    simp only [fU, uW, Category.assoc, IsOpenImmersion.lift_fac]
    by_cases h : ⊤ ≤ e z ⁻¹ᵁ U
    · rw [← Category.assoc, heU z h, he]
    · simp only [eU, dif_neg h, IsOpenImmersion.lift_fac_assoc, he]
  have hpb : IsPullback (pullback.fst fU uW) (pullback.snd fU uW) fU uW := IsPullback.of_hasPullback fU uW
  have hgen := vtf_closure_eq_top (isPushout_appTop_of_isPullback hpb)
  have hw' : (pullback.fst fU uW ≫ U.ι) ≫ f = pullback.snd fU uW ≫ u := by
    rw [Category.assoc, ← IsOpenImmersion.lift_fac W.ι (U.ι ≫ f) hUr, ← Category.assoc, pullback.condition,
      Category.assoc, IsOpenImmersion.lift_fac]
  let ι' : pullback fU uW ⟶ pullback f u := pullback.lift (pullback.fst fU uW ≫ U.ι) (pullback.snd fU uW) hw'
  let pP : (Fin g → ℂ) → (Sp ℂ ⟶ pullback fU uW) := fun z =>
    pullback.lift (eU z) (𝟙 _) (by rw [heU' z, Category.id_comp])
  have hpP : ∀ z, ⊤ ≤ e z ⁻¹ᵁ U → pP z ≫ ι' = vtfLift f u e he z := fun z h => by
    apply pullback.hom_ext
    · change pullback.lift (eU z) (𝟙 _) _ ≫ pullback.lift (pullback.fst fU uW ≫ U.ι) (pullback.snd fU uW) hw' ≫
        pullback.fst f u = pullback.lift (e z) (𝟙 _) _ ≫ pullback.fst f u
      rw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, heU z h]
    · change pullback.lift (eU z) (𝟙 _) _ ≫ pullback.lift (pullback.fst fU uW ≫ U.ι) (pullback.snd fU uW) hw' ≫
        pullback.snd f u = pullback.lift (e z) (𝟙 _) _ ≫ pullback.snd f u
      rw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
  have hUimg : U ≤ U.ι ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have hfst : ∀ b : Γ(U.toScheme, ⊤), DifferentiableOn ℂ
      (fun z => valAt' (pP z) ⊤ ((pullback.fst fU uW).appTop.hom b)) {z | ⊤ ≤ e z ⁻¹ᵁ U} := by
    intro b
    obtain ⟨b', rfl⟩ : ∃ b', (U.ι.appIso ⊤).hom.hom b' = b :=
      ⟨(U.ι.appIso ⊤).inv.hom b, by exact congrArg (fun q => q.hom b) (U.ι.appIso ⊤).inv_hom_id⟩
    have key : ∀ z, ⊤ ≤ e z ⁻¹ᵁ U →
        valAt' (pP z) ⊤ ((pullback.fst fU uW).appTop.hom ((U.ι.appIso ⊤).hom.hom b')) =
          valAt' (e z) (U.ι ''ᵁ ⊤) b' := by
      intro z hz
      have e1 : valAt' (pP z) ⊤ ((pullback.fst fU uW).appTop.hom ((U.ι.appIso ⊤).hom.hom b')) =
          valAt' (pP z ≫ pullback.fst fU uW) ⊤ ((U.ι.appIso ⊤).hom.hom b') := by
        exact valAt'_comp (pP z) (pullback.fst fU uW) ⊤ _
      have e2 : pP z ≫ pullback.fst fU uW = eU z := pullback.lift_fst _ _ _
      rw [e1, e2, Scheme.Hom.appIso_hom', Scheme.Hom.appLE, CommRingCat.comp_apply,
        valAt'_res _ _ (vtf_top _), valAt'_comp, heU z hz]
    refine ((hol _ b').2.mono fun z hz => ?_).congr fun z hz => key z hz
    exact top_le_of_mem (hUimg (vtf_mem hz))
  have hsnd : ∀ c : Γ(Sp ℂ, ⊤), DifferentiableOn ℂ
      (fun z => valAt' (pP z) ⊤ ((pullback.snd fU uW).appTop.hom c)) {z | ⊤ ≤ e z ⁻¹ᵁ U} := by
    intro c
    refine (differentiableOn_const (valAt' (𝟙 (Sp ℂ)) ⊤ c)).congr fun z _ => ?_
    have e1 : valAt' (pP z) ⊤ ((pullback.snd fU uW).appTop.hom c) =
        valAt' (pP z ≫ pullback.snd fU uW) ⊤ c := by
      exact valAt'_comp (pP z) (pullback.snd fU uW) ⊤ _
    have e2 : pP z ≫ pullback.snd fU uW = 𝟙 _ := pullback.lift_snd _ _ _
    rw [e1, e2]
  have hv : ∀ (x : Sp ℂ ⟶ pullback fU uW) (a : Γ(pullback fU uW, ⊤)),
      valHom x ⊤ (vtf_top x) a = valAt' x ⊤ a := fun _ _ => rfl
  have hall : ∀ a : Γ(pullback fU uW, ⊤), DifferentiableOn ℂ (fun z => valAt' (pP z) ⊤ a)
      {z | ⊤ ≤ e z ⁻¹ᵁ U} := by
    intro a
    have ha : a ∈ Subring.closure (Set.range (pullback.fst fU uW).appTop.hom ∪
        Set.range (pullback.snd fU uW).appTop.hom) := by
      rw [hgen]; exact Subring.mem_top a
    induction ha using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨c, rfl⟩
      · exact hfst b
      · exact hsnd c
    | zero => exact (differentiableOn_const 0).congr fun z _ => (hv _ _).symm.trans (map_zero _)
    | one => exact (differentiableOn_const 1).congr fun z _ => (hv _ _).symm.trans (map_one _)
    | add x y _ _ hx hy =>
      exact (hx.add hy).congr fun z _ => (hv _ _).symm.trans (map_add _ _ _)
    | neg x _ hx => exact hx.neg.congr fun z _ => (hv _ _).symm.trans (map_neg _ _)
    | mul x y _ _ hx hy =>
      exact (hx.mul hy).congr fun z _ => (hv _ _).symm.trans (map_mul _ _ _)
  have hz0' : pP z0 cpt ∈ ι' ⁻¹ᵁ V := by
    show ι' (pP z0 cpt) ∈ V
    rw [← Scheme.Hom.comp_apply, hpP z0 h0U]
    exact vtf_mem hz0
  obtain ⟨h, hle, hmem⟩ := (isAffineOpen_top (pullback fU uW)).exists_basicOpen_le ⟨pP z0 cpt, hz0'⟩ trivial
  haveI := (isAffineOpen_top (pullback fU uW)).isLocalization_basicOpen h
  let ψ : Γ(pullback fU uW, (pullback fU uW).basicOpen h) :=
    ((pullback fU uW).presheaf.map (homOfLE hle).op).hom ((ι'.app V).hom φ)
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) ψ
  dsimp only at hs
  obtain ⟨n, hn⟩ := s.2
  have hpow : ∀ z, valAt' (pP z) ⊤ (h ^ n) = valAt' (pP z) ⊤ h ^ n := fun z =>
    (hv _ _).symm.trans ((map_pow _ _ _).trans (congrArg (· ^ n) (hv _ _)))
  have hal : ∀ q : Γ(pullback fU uW, ⊤), algebraMap Γ(pullback fU uW, ⊤)
      Γ(pullback fU uW, (pullback fU uW).basicOpen h) q =
      ((pullback fU uW).presheaf.map (homOfLE ((pullback fU uW).basicOpen_le h)).op).hom q := fun _ => rfl
  let N : Set (Fin g → ℂ) := {z | ⊤ ≤ e z ⁻¹ᵁ U} ∩ (fun z => valAt' (pP z) ⊤ h) ⁻¹' {0}ᶜ
  have hN : IsOpen N := (hall h).continuousOn.isOpen_inter_preimage hSU isOpen_compl_singleton
  have hD : ∀ z ∈ N, ⊤ ≤ pP z ⁻¹ᵁ (pullback fU uW).basicOpen h := fun z hz =>
    top_le_of_mem ((valAt'_ne_zero_iff (pP z) ⊤ (vtf_top _) h cpt).1 hz.2)
  have hVz : ∀ z ∈ N, ⊤ ≤ vtfLift f u e he z ⁻¹ᵁ V := fun z hz => by
    apply top_le_of_mem
    rw [← hpP z hz.1, Scheme.Hom.comp_apply]
    exact hle (vtf_mem (hD z hz))
  have hval : ∀ z ∈ N, valAt' (vtfLift f u e he z) V φ =
      valAt' (pP z) ⊤ a * (valAt' (pP z) ⊤ (h ^ n))⁻¹ := by
    intro z hz
    have hne : valAt' (pP z) ⊤ h ≠ 0 := hz.2
    have e1 : valAt' (vtfLift f u e he z) V φ = valAt' (pP z) _ ψ := by
      rw [← hpP z hz.1, ← valAt'_comp]
      exact (valAt'_res _ hle (hD z hz) _).symm
    have e3 : valAt' (pP z) _ ψ * valAt' (pP z) ⊤ (h ^ n) = valAt' (pP z) ⊤ a := by
      have e2 := congrArg (valHom (pP z) _ (hD z hz)) hs
      rw [map_mul] at e2
      have ra : valHom (pP z) _ (hD z hz) (algebraMap Γ(pullback fU uW, ⊤) _ a) = valAt' (pP z) ⊤ a := by
        exact valAt'_res (pP z) ((pullback fU uW).basicOpen_le h) (hD z hz) a
      have rs : valHom (pP z) _ (hD z hz) (algebraMap Γ(pullback fU uW, ⊤) _ (s : Γ(pullback fU uW, ⊤))) =
          valAt' (pP z) ⊤ (h ^ n) := by
        rw [← hn]
        exact valAt'_res (pP z) ((pullback fU uW).basicOpen_le h) (hD z hz) _
      rw [ra, rs] at e2
      exact e2
    rw [e1, eq_mul_inv_iff_mul_eq₀ (by rw [hpow]; exact pow_ne_zero _ hne), e3]
  refine ⟨N, hN, ⟨h0U, ?_⟩, hVz, ?_⟩
  · exact (valAt'_ne_zero_iff (pP z0) ⊤ (vtf_top _) h cpt).2 hmem
  · refine (((hall a).mono Set.inter_subset_left).mul (((hall (h ^ n)).mono Set.inter_subset_left).inv
      fun z hz => ?_)).congr fun z hz => hval z hz
    rw [hpow]
    exact pow_ne_zero _ hz.2
end ReciprocityTheory.ChartRestriction.G.PullbackSections
