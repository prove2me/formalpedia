-- Prove2me | solution 1 for Rep.exists_comp_eq_or_exists_map_delta_ne_zero_of_devissage
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/511132ae-ed6a-5f68-b90b-cc9039a8232f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_comp_eq_or_exists_map_delta_ne_zero_of_devissage

set_option autoImplicit false
set_option maxHeartbeats 3200000
open CategoryTheory

theorem solution
    {G : Type} [Group G] [Fintype G] (C : Rep ℤ G)
    (p : ℕ) [Fact p.Prime]
    {SB : ShortComplex (Rep ℤ G)} (hSB : SB.ShortExact) (hB₁ : ∀ b : SB.X₃, p • b = 0)

    {R_B P_B : Rep ℤ G} (f_B : R_B ⟶ P_B) (g_B : P_B ⟶ SB.X₁) (w_B : f_B ≫ g_B = 0)
    (hT_B : (ShortComplex.mk f_B g_B w_B).ShortExact)
    {R_I P_I : Rep ℤ G} (f_I : R_I ⟶ P_I) (g_I : P_I ⟶ SB.X₂) (w_I : f_I ≫ g_I = 0)
    (hT_I : (ShortComplex.mk f_I g_I w_I).ShortExact)
    {R₁ P₁ : Rep ℤ G} (f₁ : R₁ ⟶ P₁) (g₁ : P₁ ⟶ SB.X₃) (w₁ : f₁ ≫ g₁ = 0)
    (hT₁ : (ShortComplex.mk f₁ g₁ w₁).ShortExact)

    (ιR : R_B ⟶ R_I) (ιP : P_B ⟶ P_I) (sq₁ : f_B ≫ ιP = ιR ≫ f_I) (sq₂ : g_B ≫ SB.f = ιP ≫ g_I)
    (ρR : R_I ⟶ R₁) (ρP : P_I ⟶ P₁) (sq₃ : f_I ≫ ρP = ρR ≫ f₁) (sq₄ : g_I ≫ SB.g = ρP ≫ g₁)

    (hker : ∀ φ : R_B ⟶ C,
      (∀ y : groupCohomology SB.X₁ 1,
        (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hT_B 1 2 rfl).hom y) = 0) →
      ∃ (ψ : R_I ⟶ C) (χ : P_B ⟶ C), φ = ιR ≫ ψ + f_B ≫ χ)

    (hmid : ∀ ψ : R_I ⟶ C,
      (∃ χ : P_I ⟶ C, ψ = f_I ≫ χ) ∨
      (∃ y : groupCohomology SB.X₂ 1,
        (groupCohomology.map (MonoidHom.id G) ψ 2).hom ((groupCohomology.δ hT_I 1 2 rfl).hom y) ≠ 0))

    (hsurj : ∀ θ : groupCohomology SB.X₃ 1 →+ groupCohomology C 2,
      ∃ ϑ : R₁ ⟶ C, ∀ y : groupCohomology SB.X₃ 1,
        (groupCohomology.map (MonoidHom.id G) ϑ 2).hom ((groupCohomology.δ hT₁ 1 2 rfl).hom y) = θ y)
    (φ : R_B ⟶ C) :
    (∃ χ : P_B ⟶ C, φ = f_B ≫ χ) ∨
    (∃ y : groupCohomology SB.X₁ 1,
      (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hT_B 1 2 rfl).hom y) ≠ 0) := by
  classical

  by_cases hdet : ∃ y : groupCohomology SB.X₁ 1,
      (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hT_B 1 2 rfl).hom y) ≠ 0
  · exact Or.inr hdet
  left
  push Not at hdet

  have hmap_comp : ∀ {X Y Z : Rep ℤ G} (a : X ⟶ Y) (b : Y ⟶ Z) (n : ℕ) (x : groupCohomology X n),
      (groupCohomology.map (MonoidHom.id G) (a ≫ b) n).hom x =
        (groupCohomology.map (MonoidHom.id G) b n).hom ((groupCohomology.map (MonoidHom.id G) a n).hom x) := by
    intro X Y Z a b n x
    rw [groupCohomology.map_id_comp, ModuleCat.comp_apply]
  have hmap_sub : ∀ {X Y : Rep ℤ G} (a b : X ⟶ Y) (n : ℕ) (x : groupCohomology X n),
      (groupCohomology.map (MonoidHom.id G) (a - b) n).hom x =
        (groupCohomology.map (MonoidHom.id G) a n).hom x - (groupCohomology.map (MonoidHom.id G) b n).hom x := by
    intro X Y a b n x
    have h : groupCohomology.map (MonoidHom.id G) (a - b) n =
        groupCohomology.map (MonoidHom.id G) a n - groupCohomology.map (MonoidHom.id G) b n := by
      change HomologicalComplex.homologyMap ((groupCohomology.cochainsFunctor ℤ G).map (a - b)) n =
        HomologicalComplex.homologyMap ((groupCohomology.cochainsFunctor ℤ G).map a) n -
          HomologicalComplex.homologyMap ((groupCohomology.cochainsFunctor ℤ G).map b) n
      rw [Functor.map_sub, HomologicalComplex.homologyMap_sub]
    rw [h]
    rfl

  have hnatι : ∀ y : groupCohomology SB.X₁ 1,
      (groupCohomology.δ hT_I 1 2 rfl).hom ((groupCohomology.map (MonoidHom.id G) SB.f 1).hom y) =
        (groupCohomology.map (MonoidHom.id G) ιR 2).hom ((groupCohomology.δ hT_B 1 2 rfl).hom y) := by
    intro y
    let ψ : ShortComplex.mk f_B g_B w_B ⟶ ShortComplex.mk f_I g_I w_I :=
      { τ₁ := ιR, τ₂ := ιP, τ₃ := SB.f, comm₁₂ := sq₁.symm, comm₂₃ := sq₂.symm }
    have h := HomologicalComplex.HomologySequence.δ_naturality
      ((groupCohomology.cochainsFunctor ℤ G).mapShortComplex.map ψ)
      (groupCohomology.map_cochainsFunctor_shortExact hT_B) (groupCohomology.map_cochainsFunctor_shortExact hT_I) 1 2 rfl
    have h' := congrArg (fun f => (ModuleCat.Hom.hom f) y) h
    exact h'.symm
  have hnatρ : ∀ y : groupCohomology SB.X₂ 1,
      (groupCohomology.δ hT₁ 1 2 rfl).hom ((groupCohomology.map (MonoidHom.id G) SB.g 1).hom y) =
        (groupCohomology.map (MonoidHom.id G) ρR 2).hom ((groupCohomology.δ hT_I 1 2 rfl).hom y) := by
    intro y
    let ψ : ShortComplex.mk f_I g_I w_I ⟶ ShortComplex.mk f₁ g₁ w₁ :=
      { τ₁ := ρR, τ₂ := ρP, τ₃ := SB.g, comm₁₂ := sq₃.symm, comm₂₃ := sq₄.symm }
    have h := HomologicalComplex.HomologySequence.δ_naturality
      ((groupCohomology.cochainsFunctor ℤ G).mapShortComplex.map ψ)
      (groupCohomology.map_cochainsFunctor_shortExact hT_I) (groupCohomology.map_cochainsFunctor_shortExact hT₁) 1 2 rfl
    have h' := congrArg (fun f => (ModuleCat.Hom.hom f) y) h
    exact h'.symm

  have hδf : ∀ y : groupCohomology SB.X₁ 1,
      (groupCohomology.map (MonoidHom.id G) f_B 2).hom ((groupCohomology.δ hT_B 1 2 rfl).hom y) = 0 := by
    intro y
    have h := (groupCohomology.map_cochainsFunctor_shortExact hT_B).δ_comp 1 2 rfl
    have h' := congrArg (fun f => (ModuleCat.Hom.hom f) y) h
    simp only [ModuleCat.comp_apply] at h' ⊢
    exact h'

  obtain ⟨ψ, χ, hφ⟩ := hker φ hdet

  set a₁ : groupCohomology SB.X₂ 1 →ₗ[ℤ] groupCohomology C 2 :=
    (groupCohomology.map (MonoidHom.id G) ψ 2).hom ∘ₗ (groupCohomology.δ hT_I 1 2 rfl).hom with ha₁
  have ha₁ι : ∀ y : groupCohomology SB.X₁ 1, a₁ ((groupCohomology.map (MonoidHom.id G) SB.f 1).hom y) = 0 := by
    intro y
    simp only [ha₁, LinearMap.coe_comp, Function.comp_apply]
    rw [hnatι, ← hmap_comp]
    have hιψ : ιR ≫ ψ = φ - f_B ≫ χ := by rw [hφ]; abel
    rw [hιψ, hmap_sub, hdet y, hmap_comp, hδf, map_zero, sub_zero]

  set ρs : groupCohomology SB.X₂ 1 →ₗ[ℤ] groupCohomology SB.X₃ 1 := (groupCohomology.map (MonoidHom.id G) SB.g 1).hom with hρs
  have hexact : LinearMap.range (groupCohomology.map (MonoidHom.id G) SB.f 1).hom = LinearMap.ker ρs := by
    have h := groupCohomology.mapShortComplex₂_exact hSB 1
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
    exact h
  have hker_le : LinearMap.ker ρs ≤ LinearMap.ker a₁ := by
    intro x hx
    rw [← hexact] at hx
    obtain ⟨y, rfl⟩ := hx
    exact ha₁ι y

  have hwd : ∀ x x' : groupCohomology SB.X₂ 1, ρs x = ρs x' → a₁ x = a₁ x' := by
    intro x x' h
    have hmem : x - x' ∈ LinearMap.ker ρs := by
      rw [LinearMap.mem_ker, map_sub, h, sub_self]
    have h0 := hker_le hmem
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h0
    exact h0
  let lift : ∀ w : groupCohomology SB.X₃ 1, w ∈ LinearMap.range ρs → groupCohomology SB.X₂ 1 :=
    fun w hw => Classical.choose hw
  have hlift : ∀ (w : groupCohomology SB.X₃ 1) (hw : w ∈ LinearMap.range ρs), ρs (lift w hw) = w :=
    fun w hw => Classical.choose_spec hw

  have hp : p.Prime := Fact.out
  have hVp : ∀ z : groupCohomology SB.X₃ 1, p • z = 0 := by
    intro z
    refine groupCohomology_induction_on z (fun c => ?_)
    rw [← map_nsmul]
    have hc : p • c = 0 := by
      apply (ModuleCat.mono_iff_injective (groupCohomology.iCocycles SB.X₃ 1)).1 inferInstance
      rw [map_nsmul, map_zero]
      funext g
      rw [Pi.smul_apply, Pi.zero_apply]
      exact hB₁ _
    rw [hc, map_zero]
  letI : Module (ZMod p) (groupCohomology SB.X₃ 1) := AddCommGroup.zmodModule hVp

  obtain ⟨pr, hprmem, hprid⟩ : ∃ pr : groupCohomology SB.X₃ 1 →+ groupCohomology SB.X₃ 1,
      (∀ v, pr v ∈ LinearMap.range ρs) ∧ (∀ v, v ∈ LinearMap.range ρs → pr v = v) := by
    let W : Submodule (ZMod p) (groupCohomology SB.X₃ 1) :=
      AddSubgroup.toZModSubmodule p (LinearMap.range ρs).toAddSubgroup
    have hWmem : ∀ x : groupCohomology SB.X₃ 1, x ∈ W ↔ x ∈ LinearMap.range ρs := fun x =>
      Iff.trans (AddSubgroup.mem_toZModSubmodule p) (Submodule.mem_toAddSubgroup _)
    obtain ⟨W', hWW'⟩ := Submodule.exists_isCompl W
    refine ⟨(W.subtype ∘ₗ Submodule.projectionOnto W W' hWW').toAddMonoidHom, fun v => ?_, fun v hv => ?_⟩
    · exact (hWmem _).1 (Submodule.projectionOnto W W' hWW' v).2
    · have := Submodule.projectionOnto_apply_left hWW' ⟨v, (hWmem v).2 hv⟩
      exact congrArg Subtype.val this
  let θ : groupCohomology SB.X₃ 1 →+ groupCohomology C 2 :=
    { toFun := fun v => a₁ (lift _ (hprmem v))
      map_zero' := by
        have h0 : lift _ (hprmem 0) ∈ LinearMap.ker ρs := by
          rw [LinearMap.mem_ker, hlift, map_zero]
        have := hker_le h0
        rwa [LinearMap.mem_ker] at this
      map_add' := fun v w => by
        rw [← map_add]
        apply hwd
        rw [hlift, map_add ρs, hlift, hlift, map_add] }
  have hθ : ∀ x : groupCohomology SB.X₂ 1, θ (ρs x) = a₁ x := by
    intro x
    change a₁ (lift _ (hprmem (ρs x))) = a₁ x
    apply hwd
    rw [hlift, hprid _ (LinearMap.mem_range_self ρs x)]

  obtain ⟨ϑ, hϑ⟩ := hsurj θ

  set ψ' : R_I ⟶ C := ψ - ρR ≫ ϑ with hψ'def
  have hψ' : ∀ y : groupCohomology SB.X₂ 1,
      (groupCohomology.map (MonoidHom.id G) ψ' 2).hom ((groupCohomology.δ hT_I 1 2 rfl).hom y) = 0 := by
    intro y
    rw [hψ'def, hmap_sub, hmap_comp, ← hnatρ, hϑ, hθ]
    simp only [ha₁, LinearMap.coe_comp, Function.comp_apply]
    exact sub_self _

  obtain ⟨χ'', hχ''⟩ : ∃ χ'' : P_I ⟶ C, ψ' = f_I ≫ χ'' := by
    rcases hmid ψ' with h | ⟨y, hy⟩
    · exact h
    · exact absurd (hψ' y) hy

  haveI : Mono f₁ := hT₁.mono_f
  have hz : (ιP ≫ ρP) ≫ (ShortComplex.mk f₁ g₁ w₁).g = 0 := by
    change (ιP ≫ ρP) ≫ g₁ = 0
    rw [Category.assoc, ← sq₄, ← Category.assoc, ← sq₂, Category.assoc, SB.zero, Limits.comp_zero]
  let h : P_B ⟶ R₁ := hT₁.exact.lift (ιP ≫ ρP) hz
  have hh : h ≫ f₁ = ιP ≫ ρP := hT₁.exact.lift_f (ιP ≫ ρP) hz
  have hιρ : ιR ≫ ρR = f_B ≫ h := by
    rw [← cancel_mono f₁, Category.assoc, Category.assoc, ← sq₃, ← Category.assoc, ← sq₁, Category.assoc, hh]

  refine ⟨ιP ≫ χ'' + h ≫ ϑ + χ, ?_⟩
  have hψeq : ψ = f_I ≫ χ'' + ρR ≫ ϑ := by rw [← hχ'', hψ'def]; abel
  rw [hφ, hψeq, Preadditive.comp_add, Preadditive.comp_add, Preadditive.comp_add, ← Category.assoc, ← sq₁,
    Category.assoc, ← Category.assoc ιR ρR, hιρ, Category.assoc]

end S_Rep_exists_comp_eq_or_exists_map_delta_ne_zero_of_devissage
end P2MW
export P2MW.S_Rep_exists_comp_eq_or_exists_map_delta_ne_zero_of_devissage (solution)
