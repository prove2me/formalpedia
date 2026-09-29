-- Prove2me | solution 1 for Rep.tateDelta_comp_tateDelta_eq_neg_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/48371939-9789-59de-b598-2b516317c64a

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_tateDelta_comp_tateDelta_eq_neg_of_hom

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

section Coh
open groupCohomology

namespace P2mS26GC

variable {k G : Type u} [CommRing k] [Group G]

theorem d_iCocycles (A : Rep.{u} k G) (n : ℕ) (x : cocycles A n) :
    (inhomogeneousCochains.d A n).hom ((iCocycles A n).hom x) = 0 := by
  have := congrArg (fun φ => φ.hom x) ((inhomogeneousCochains A).iCycles_d n (n + 1))
  simpa [ModuleCat.hom_comp] using this

theorem d_d_apply (A : Rep.{u} k G) (n : ℕ) (x : (Fin n → G) → A) :
    (inhomogeneousCochains.d A (n + 1)).hom ((inhomogeneousCochains.d A n).hom x) = 0 := by
  have := congrArg (fun φ => φ.hom x) (inhomogeneousCochains.d_comp_d (A := A) (n := n))
  simpa [ModuleCat.hom_comp] using this

theorem π_surjective (A : Rep.{u} k G) (n : ℕ) : Function.Surjective (groupCohomology.π A n).hom :=
  (ModuleCat.epi_iff_surjective ((inhomogeneousCochains A).homologyπ n)).1 inferInstance

theorem iCocycles_injective (A : Rep.{u} k G) (n : ℕ) : Function.Injective (iCocycles A n).hom :=
  (ModuleCat.mono_iff_injective (iCocycles A n)).1 inferInstance

theorem i_cocyclesMk {A : Rep.{u} k G} {n : ℕ} (x : (Fin n → G) → A) (h) :
    (iCocycles A n).hom (cocyclesMk x h) = x :=
  iCocycles_mk x h

theorem cochainsMap_id_f_apply {A B : Rep.{u} k G} (φ : A ⟶ B) (n : ℕ) (x : (Fin n → G) → A) (σ : Fin n → G) :
    ((cochainsMap (MonoidHom.id G) φ).f n).hom x σ = φ.hom (x σ) := by
  rw [cochainsMap_f_hom]
  rfl

theorem hom_d_apply {A B : Rep.{u} k G} (φ : A ⟶ B) (n : ℕ) (x : (Fin n → G) → A) (τ : Fin (n + 1) → G) :
    φ.hom ((inhomogeneousCochains.d A n).hom x τ) = (inhomogeneousCochains.d B n).hom (fun σ => φ.hom (x σ)) τ := by
  simp only [inhomogeneousCochains.d_hom_apply, map_add, map_sum, map_smul, Rep.hom_comm_apply]

theorem g_f_apply (S : ShortComplex (Rep.{u} k G)) (a : S.X₁) : S.g.hom (S.f.hom a) = 0 := by
  rw [← Rep.comp_apply, S.zero]
  rfl

theorem f_injective {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) : Function.Injective S.f.hom :=
  (Rep.mono_iff_injective S.f).1 hS.mono_f

theorem exists_lift {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) (n : ℕ) (z : (Fin n → G) → S.X₃) :
    ∃ y : (Fin n → G) → S.X₂, ∀ τ, S.g.hom (y τ) = z τ := by
  haveI := hS.epi_g
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective _).1 (cochainsMap_id_f_map_epi S.g n) z
  exact ⟨y, fun τ => by rw [← cochainsMap_id_f_apply S.g n y τ]; exact congrFun hy τ⟩

theorem exists_preimage {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) (v : S.X₂) (hv : S.g.hom v = 0) :
    ∃ u : S.X₁, S.f.hom u = v := by
  have h : LinearMap.range S.f.hom.toLinearMap = LinearMap.ker S.g.hom.toLinearMap :=
    (hS.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  have hv' : v ∈ LinearMap.range S.f.hom.toLinearMap := by
    rw [h]
    exact hv
  obtain ⟨u, hu⟩ := hv'
  exact ⟨u, hu⟩

theorem exchange {A A' B B' : Rep.{u} k G} (f : A ⟶ A') (g : B ⟶ B') (t : (A ⊗ B : Rep.{u} k G)) :
    (A' ◁ g).hom ((f ▷ B).hom t) = (f ▷ B').hom ((A ◁ g).hom t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add t t' ht ht' => simp only [map_add, ht, ht']

theorem sq_f {S T : ShortComplex (Rep.{u} k G)} (τ : S ⟶ T) (t : S.X₁) : τ.τ₂.hom (S.f.hom t) = T.f.hom (τ.τ₁.hom t) := by
  have := congrArg (fun φ => φ.hom t) τ.comm₁₂
  simpa [Rep.comp_apply] using this.symm

theorem sq_g {S T : ShortComplex (Rep.{u} k G)} (τ : S ⟶ T) (t : S.X₂) : τ.τ₃.hom (S.g.hom t) = T.g.hom (τ.τ₂.hom t) := by
  have := congrArg (fun φ => φ.hom t) τ.comm₂₃
  simpa [Rep.comp_apply] using this.symm

end P2mS26GC

namespace P2mS26GC

variable {k G : Type u} [CommRing k] [Group G]

theorem coh_chase {R₁ R₂ R₃ : ShortComplex (Rep.{u} k G)}
    (hR₁ : R₁.ShortExact) (hR₂ : R₂.ShortExact) (hR₃ : R₃.ShortExact) (α : R₁ ⟶ R₂) (β : R₂ ⟶ R₃)
    (h₁ : α.τ₁ ≫ β.τ₁ = 0) (h₂ : α.τ₂ ≫ β.τ₂ = 0) (h₃ : α.τ₃ ≫ β.τ₃ = 0)
    (hC₁ : (ShortComplex.mk α.τ₁ β.τ₁ h₁).ShortExact) (hC₂ : (ShortComplex.mk α.τ₂ β.τ₂ h₂).ShortExact)
    (hC₃ : (ShortComplex.mk α.τ₃ β.τ₃ h₃).ShortExact)
    (i : ℕ) (c : groupCohomology (R₃.X₃) i) :
    (groupCohomology.δ hC₁ (i + 1) (i + 2) rfl).hom ((groupCohomology.δ hR₃ i (i + 1) rfl).hom c)
      = -((groupCohomology.δ hR₁ (i + 1) (i + 2) rfl).hom ((groupCohomology.δ hC₃ i (i + 1) rfl).hom c)) := by
  obtain ⟨c₀, rfl⟩ := π_surjective (R₃.X₃) i c
  have hc : (inhomogeneousCochains.d (R₃.X₃) i).hom ((iCocycles _ i).hom c₀) = 0 := d_iCocycles _ _ c₀
  have hπ : (groupCohomology.π (R₃.X₃) i).hom c₀
      = (groupCohomology.π (R₃.X₃) i).hom (cocyclesMk ((iCocycles _ i).hom c₀) hc) :=
    congrArg _ (iCocycles_injective _ _ (i_cocyclesMk _ _).symm)

  have ex : ∃ x : (Fin i → G) → R₃.X₂, ∀ τ, (R₃.g).hom (x τ)
      = (iCocycles (R₃.X₃) i).hom c₀ τ := exists_lift hR₃ i ((iCocycles (R₃.X₃) i).hom c₀)
  obtain ⟨x, hx⟩ := ex
  have em : ∃ m : (Fin i → G) → R₂.X₂, ∀ τ, (β.τ₂).hom (m τ) = x τ :=
    exists_lift hC₂ i x
  obtain ⟨m, hm⟩ := em
  let u : (Fin i → G) → R₂.X₃ := fun τ => (R₂.g).hom (m τ)
  have hu : ∀ τ, (β.τ₃).hom (u τ) = (iCocycles (R₃.X₃) i).hom c₀ τ := fun τ => by
    show (β.τ₃).hom ((R₂.g).hom (m τ)) = _
    rw [sq_g β, hm τ, hx τ]

  have hgdx : ∀ τ, (R₃.g).hom ((inhomogeneousCochains.d (R₃.X₂) i).hom x τ) = 0 := fun τ => by
    rw [hom_d_apply (R₃.g), show (fun σ => (R₃.g).hom (x σ)) = (iCocycles (R₃.X₃) i).hom c₀
      from funext hx]
    exact congrFun hc τ
  have ey : ∀ τ, ∃ u : R₃.X₁, (R₃.f).hom u
      = (inhomogeneousCochains.d (R₃.X₂) i).hom x τ := fun τ => exists_preimage hR₃ _ (hgdx τ)
  choose y hy using ey
  have hdy : (inhomogeneousCochains.d (R₃.X₁) (i + 1)).hom y = 0 := by
    funext τ
    apply f_injective hR₃
    show (R₃.f).hom _ = (R₃.f).hom 0
    rw [hom_d_apply (R₃.f), show (fun σ => (R₃.f).hom (y σ))
      = (inhomogeneousCochains.d (R₃.X₂) i).hom x from funext hy, d_d_apply, map_zero]
    rfl

  have ey' : ∃ y' : (Fin (i + 1) → G) → R₂.X₁, ∀ τ, (β.τ₁).hom (y' τ) = y τ :=
    exists_lift hC₁ (i + 1) y
  obtain ⟨y', hy'⟩ := ey'

  have hker₂ : ∀ τ, (β.τ₂).hom ((inhomogeneousCochains.d (R₂.X₂) i).hom m τ
      - (R₂.f).hom (y' τ)) = 0 := fun τ => by
    rw [map_sub, hom_d_apply (β.τ₂), show (fun σ => (β.τ₂).hom (m σ)) = x from funext hm, sq_f β, hy' τ,
      hy τ, sub_self]
  have ev' : ∀ τ, ∃ u : R₁.X₂, (α.τ₂).hom u
      = (inhomogeneousCochains.d (R₂.X₂) i).hom m τ - (R₂.f).hom (y' τ) :=
    fun τ => exists_preimage hC₂ _ (hker₂ τ)
  choose v' hv' using ev'
  let v : (Fin (i + 1) → G) → R₁.X₃ := fun τ => (R₁.g).hom (v' τ)
  have hv : ∀ τ, (α.τ₃).hom (v τ) = (inhomogeneousCochains.d (R₂.X₃) i).hom u τ := fun τ => by
    show (α.τ₃).hom ((R₁.g).hom (v' τ)) = _
    rw [sq_g α, hv' τ, map_sub, hom_d_apply (R₂.g),
      show (R₂.g).hom ((R₂.f).hom (y' τ)) = 0 from g_f_apply (R₂) (y' τ), sub_zero]
  have hdv : (inhomogeneousCochains.d (R₁.X₃) (i + 1)).hom v = 0 := by
    funext τ
    apply f_injective hC₃
    show (α.τ₃).hom _ = (α.τ₃).hom 0
    rw [hom_d_apply (α.τ₃), show (fun σ => (α.τ₃).hom (v σ))
      = (inhomogeneousCochains.d (R₂.X₃) i).hom u from funext hv, d_d_apply, map_zero]
    rfl

  have hker₁ : ∀ τ, (β.τ₁).hom ((inhomogeneousCochains.d (R₂.X₁) (i + 1)).hom y' τ) = 0 := fun τ => by
    rw [hom_d_apply (β.τ₁), show (fun σ => (β.τ₁).hom (y' σ)) = y from funext hy']
    exact congrFun hdy τ
  have ez : ∀ τ, ∃ u : R₁.X₁, (α.τ₁).hom u
      = (inhomogeneousCochains.d (R₂.X₁) (i + 1)).hom y' τ := fun τ => exists_preimage hC₁ _ (hker₁ τ)
  choose z hz using ez

  have hker₃ : ∀ τ, (R₁.g).hom ((inhomogeneousCochains.d (R₁.X₂) (i + 1)).hom v' τ) = 0 := fun τ => by
    rw [hom_d_apply (R₁.g)]
    exact congrFun hdv τ
  have ew : ∀ τ, ∃ u : R₁.X₁, (R₁.f).hom u
      = (inhomogeneousCochains.d (R₁.X₂) (i + 1)).hom v' τ := fun τ => exists_preimage hR₁ _ (hker₃ τ)
  choose w hw using ew

  have hzw : ∀ τ, z τ + w τ = 0 := fun τ => by
    apply f_injective hC₁
    apply f_injective hR₂
    show (R₂.f).hom ((α.τ₁).hom (z τ + w τ)) = (R₂.f).hom ((α.τ₁).hom 0)
    have e1 : (R₂.f).hom ((α.τ₁).hom (z τ))
        = (inhomogeneousCochains.d (R₂.X₂) (i + 1)).hom (fun σ => (R₂.f).hom (y' σ)) τ := by
      rw [hz τ, hom_d_apply]
    have e2 : (R₂.f).hom ((α.τ₁).hom (w τ))
        = -(inhomogeneousCochains.d (R₂.X₂) (i + 1)).hom (fun σ => (R₂.f).hom (y' σ)) τ := by
      rw [← sq_f α, hw τ, hom_d_apply (α.τ₂), show (fun σ => (α.τ₂).hom (v' σ))
        = (inhomogeneousCochains.d (R₂.X₂) i).hom m - fun σ => (R₂.f).hom (y' σ) from funext hv',
        map_sub, Pi.sub_apply, d_d_apply, Pi.zero_apply, zero_sub]
    rw [map_add, map_add, e1, e2, add_neg_cancel, map_zero, map_zero]

  have Hy : (R₃).f.hom ∘ y = (inhomogeneousCochains (R₃).X₂).d i (i + 1) x := by
    rw [inhomogeneousCochains.d_def]; exact funext hy
  have Hz : (ShortComplex.mk α.τ₁ β.τ₁ h₁).f.hom ∘ z = (inhomogeneousCochains (ShortComplex.mk α.τ₁ β.τ₁ h₁).X₂).d (i + 1) (i + 2) y' := by
    rw [inhomogeneousCochains.d_def]; exact funext hz
  have Hv : (ShortComplex.mk α.τ₃ β.τ₃ h₃).f.hom ∘ v = (inhomogeneousCochains (ShortComplex.mk α.τ₃ β.τ₃ h₃).X₂).d i (i + 1) u := by
    rw [inhomogeneousCochains.d_def]; exact funext hv
  have Hw : (R₁).f.hom ∘ w = (inhomogeneousCochains (R₁).X₂).d (i + 1) (i + 2) v' := by
    rw [inhomogeneousCochains.d_def]; exact funext hw
  have keyR : (groupCohomology.δ hR₃ i (i + 1) rfl).hom ((groupCohomology.π (R₃.X₃) i).hom
      (cocyclesMk ((iCocycles _ i).hom c₀) hc))
      = (groupCohomology.π (R₃.X₁) (i + 1)).hom (cocyclesMkOfCompEqD hR₃ Hy) :=
    groupCohomology.δ_apply hR₃ rfl ((iCocycles (R₃.X₃) i).hom c₀)
      (by rw [inhomogeneousCochains.d_def]; exact hc) x (funext fun τ => (cochainsMap_id_f_apply _ i x τ).trans (hx τ)) y Hy
  have keyC : (groupCohomology.δ hC₁ (i + 1) (i + 2) rfl).hom ((groupCohomology.π (R₃.X₁) (i + 1)).hom
      (cocyclesMkOfCompEqD hR₃ Hy))
      = (groupCohomology.π (R₁.X₁) (i + 2)).hom (cocyclesMkOfCompEqD hC₁ Hz) :=
    groupCohomology.δ_apply hC₁ rfl y (by rw [inhomogeneousCochains.d_def]; exact hdy) y'
      (funext fun τ => (cochainsMap_id_f_apply _ (i + 1) y' τ).trans (hy' τ)) z Hz
  have keyC' : (groupCohomology.δ hC₃ i (i + 1) rfl).hom ((groupCohomology.π (R₃.X₃) i).hom
      (cocyclesMk ((iCocycles _ i).hom c₀) hc))
      = (groupCohomology.π (R₁.X₃) (i + 1)).hom (cocyclesMkOfCompEqD hC₃ Hv) :=
    groupCohomology.δ_apply hC₃ rfl ((iCocycles (R₃.X₃) i).hom c₀)
      (by rw [inhomogeneousCochains.d_def]; exact hc) u (funext fun τ => (cochainsMap_id_f_apply _ i u τ).trans (hu τ)) v Hv
  have keyR' : (groupCohomology.δ hR₁ (i + 1) (i + 2) rfl).hom ((groupCohomology.π (R₁.X₃) (i + 1)).hom
      (cocyclesMkOfCompEqD hC₃ Hv))
      = (groupCohomology.π (R₁.X₁) (i + 2)).hom (cocyclesMkOfCompEqD hR₁ Hw) :=
    groupCohomology.δ_apply hR₁ rfl v (by rw [inhomogeneousCochains.d_def]; exact hdv) v'
      (funext fun τ => cochainsMap_id_f_apply _ (i + 1) v' τ) w Hw

  have hdz : (inhomogeneousCochains.d (R₁.X₁) (i + 2)).hom z = 0 := by
    funext τ
    apply f_injective hC₁
    show (α.τ₁).hom _ = (α.τ₁).hom 0
    rw [hom_d_apply (α.τ₁), show (fun σ => (α.τ₁).hom (z σ))
      = (inhomogeneousCochains.d (R₂.X₁) (i + 1)).hom y' from funext hz, d_d_apply, map_zero]
    rfl
  have hdw : (inhomogeneousCochains.d (R₁.X₁) (i + 2)).hom w = 0 := by
    funext τ
    apply f_injective hR₁
    show (R₁.f).hom _ = (R₁.f).hom 0
    rw [hom_d_apply (R₁.f), show (fun σ => (R₁.f).hom (w σ))
      = (inhomogeneousCochains.d (R₁.X₂) (i + 1)).hom v' from funext hw, d_d_apply, map_zero]
    rfl
  have e : cocyclesMk (A := R₁.X₁) z hdz + cocyclesMk (A := R₁.X₁) w hdw = 0 :=
    iCocycles_injective (R₁.X₁) (i + 2) (by
      rw [map_add, map_zero, i_cocyclesMk, i_cocyclesMk]
      exact funext hzw)
  rw [hπ, keyR, keyC, keyC', keyR']
  show (groupCohomology.π (R₁.X₁) (i + 2)).hom (cocyclesMk (A := R₁.X₁) z hdz)
    = -((groupCohomology.π (R₁.X₁) (i + 2)).hom (cocyclesMk (A := R₁.X₁) w hdw))
  rw [eq_neg_of_add_eq_zero_left e, map_neg]

end P2mS26GC

end Coh

namespace P2mS26GH
open groupHomology Finsupp

variable {k G : Type u} [CommRing k] [Group G]

noncomputable abbrev mR {A B : Rep.{u} k G} (φ : A ⟶ B) (n : ℕ) : ((Fin n → G) →₀ A) →ₗ[k] ((Fin n → G) →₀ B) :=
  Finsupp.mapRange.linearMap φ.hom.toLinearMap

theorem mR_apply {A B : Rep.{u} k G} (φ : A ⟶ B) (n : ℕ) (t : (Fin n → G) →₀ A) (a : Fin n → G) :
    mR φ n t a = φ.hom (t a) := by
  simp [mR, Finsupp.mapRange.linearMap_apply]

theorem g_f_apply (S : ShortComplex (Rep.{u} k G)) (a : S.X₁) : S.g.hom (S.f.hom a) = 0 := by
  rw [← Rep.comp_apply, S.zero]
  rfl

theorem f_injective {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) : Function.Injective S.f.hom :=
  (Rep.mono_iff_injective S.f).1 hS.mono_f

theorem mR_injective {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) (n : ℕ) : Function.Injective (mR S.f n) :=
  fun s t h => Finsupp.ext fun a => f_injective hS (by
    have := congrArg (fun r => r a) h
    simpa [mR_apply] using this)

theorem exists_lift {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) (n : ℕ) (z : (Fin n → G) →₀ S.X₃) :
    ∃ y : (Fin n → G) →₀ S.X₂, mR S.g n y = z := by
  obtain ⟨y, hy⟩ := Finsupp.mapRange_surjective _ (map_zero S.g.hom.toLinearMap)
    ((Rep.epi_iff_surjective S.g).1 hS.epi_g) z
  exact ⟨y, by rw [mR, Finsupp.mapRange.linearMap_apply]; exact hy⟩

theorem exists_preimage {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) (n : ℕ) (t : (Fin n → G) →₀ S.X₂)
    (ht : mR S.g n t = 0) : ∃ s : (Fin n → G) →₀ S.X₁, mR S.f n s = t := by
  have h1 : LinearMap.range S.f.hom.toLinearMap = LinearMap.ker S.g.hom.toLinearMap :=
    (hS.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  have : t ∈ LinearMap.range (mR S.f n) := by
    rw [mR, Finsupp.range_mapRange_linearMap _ (LinearMap.ker_eq_bot.2 (f_injective hS)) _, h1,
      ← Finsupp.ker_mapRange]
    exact ht
  exact this

theorem mR_exchange {A A' B B' : Rep.{u} k G} (f : A ⟶ A') (g : B ⟶ B') (n : ℕ)
    (t : (Fin n → G) →₀ (A ⊗ B : Rep.{u} k G)) :
    mR (A' ◁ g) n (mR (f ▷ B) n t) = mR (f ▷ B') n (mR (A ◁ g) n t) := by
  refine Finsupp.ext fun a => ?_
  rw [mR_apply, mR_apply, mR_apply, mR_apply]
  induction t a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add t t' ht ht' => simp only [map_add, ht, ht']

theorem d_mR {A B : Rep.{u} k G} (φ : A ⟶ B) (n : ℕ) (t : (Fin (n + 1) → G) →₀ A) :
    (inhomogeneousChains.d B n).hom (mR φ (n + 1) t) = mR φ n ((inhomogeneousChains.d A n).hom t) := by
  have := congrArg (fun ψ => ψ.hom t) ((chainsMap (MonoidHom.id G) φ).comm (n + 1) n)
  rw [inhomogeneousChains.d_def, inhomogeneousChains.d_def] at this
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, chainsMap_id_f_hom_eq_mapRange] at this
  exact this

theorem d_d_apply (A : Rep.{u} k G) (n : ℕ) (x : (Fin (n + 2) → G) →₀ A) :
    (inhomogeneousChains.d A n).hom ((inhomogeneousChains.d A (n + 1)).hom x) = 0 := by
  have := congrArg (fun φ => φ.hom x) (inhomogeneousChains.d_comp_d (A := A) (n := n))
  simpa [ModuleCat.hom_comp] using this

theorem d_iCycles (A : Rep.{u} k G) (n : ℕ) (x : cycles A (n + 1)) :
    (inhomogeneousChains.d A n).hom ((iCycles A (n + 1)).hom x) = 0 := by
  have := congrArg (fun φ => φ.hom x) ((inhomogeneousChains A).iCycles_d (n + 1) n)
  simpa [ModuleCat.hom_comp] using this

theorem π_surjective (A : Rep.{u} k G) (n : ℕ) : Function.Surjective (groupHomology.π A n).hom :=
  (ModuleCat.epi_iff_surjective ((inhomogeneousChains A).homologyπ n)).1 inferInstance

theorem iCycles_injective (A : Rep.{u} k G) (n : ℕ) : Function.Injective (iCycles A n).hom :=
  (ModuleCat.mono_iff_injective (iCycles A n)).1 inferInstance

theorem i_cyclesMk {A : Rep.{u} k G} (m n : ℕ) (h : (ComplexShape.down ℕ).next m = n)
    (f : (Fin m → G) →₀ A) (hf) : (iCycles A m).hom (cyclesMk m n h f hf) = f :=
  iCycles_mk h f hf

theorem mR_sq_f {S T : ShortComplex (Rep.{u} k G)} (τ : S ⟶ T) (n : ℕ) (t : (Fin n → G) →₀ S.X₁) :
    mR τ.τ₂ n (mR S.f n t) = mR T.f n (mR τ.τ₁ n t) := by
  refine Finsupp.ext fun a => ?_
  rw [mR_apply, mR_apply, mR_apply, mR_apply]
  have := congrArg (fun φ => φ.hom (t a)) τ.comm₁₂
  simpa [Rep.comp_apply] using this.symm

theorem mR_sq_g {S T : ShortComplex (Rep.{u} k G)} (τ : S ⟶ T) (n : ℕ) (t : (Fin n → G) →₀ S.X₂) :
    mR τ.τ₃ n (mR S.g n t) = mR T.g n (mR τ.τ₂ n t) := by
  refine Finsupp.ext fun a => ?_
  rw [mR_apply, mR_apply, mR_apply, mR_apply]
  have := congrArg (fun φ => φ.hom (t a)) τ.comm₂₃
  simpa [Rep.comp_apply] using this.symm

end P2mS26GH

namespace P2mS26GH
open groupHomology Finsupp

variable {k G : Type u} [CommRing k] [Group G]

theorem hom_chase {R₁ R₂ R₃ : ShortComplex (Rep.{u} k G)}
    (hR₁ : R₁.ShortExact) (hR₂ : R₂.ShortExact) (hR₃ : R₃.ShortExact) (α : R₁ ⟶ R₂) (β : R₂ ⟶ R₃)
    (h₁ : α.τ₁ ≫ β.τ₁ = 0) (h₂ : α.τ₂ ≫ β.τ₂ = 0) (h₃ : α.τ₃ ≫ β.τ₃ = 0)
    (hC₁ : (ShortComplex.mk α.τ₁ β.τ₁ h₁).ShortExact) (hC₂ : (ShortComplex.mk α.τ₂ β.τ₂ h₂).ShortExact)
    (hC₃ : (ShortComplex.mk α.τ₃ β.τ₃ h₃).ShortExact)
    (i : ℕ) (c : groupHomology (R₃.X₃) (i + 2)) :
    (groupHomology.δ hC₁ (i + 1) i rfl).hom ((groupHomology.δ hR₃ (i + 2) (i + 1) rfl).hom c)
      = -((groupHomology.δ hR₁ (i + 1) i rfl).hom ((groupHomology.δ hC₃ (i + 2) (i + 1) rfl).hom c)) := by
  obtain ⟨c₀, rfl⟩ := π_surjective (R₃.X₃) (i + 2) c
  have hc : (inhomogeneousChains.d (R₃.X₃) (i + 1)).hom ((iCycles _ (i + 2)).hom c₀) = 0 := d_iCycles _ _ c₀
  have hc' : (inhomogeneousChains (R₃.X₃)).d (i + 2) (i + 1) ((iCycles _ (i + 2)).hom c₀) = 0 := by
    rw [inhomogeneousChains.d_def]; exact hc
  have hπ : (groupHomology.π (R₃.X₃) (i + 2)).hom c₀
      = (groupHomology.π (R₃.X₃) (i + 2)).hom (cyclesMk (i + 2) (i + 1) (by simp) ((iCycles _ (i + 2)).hom c₀) hc') :=
    congrArg _ (iCycles_injective _ _ (i_cyclesMk _ _ _ _ _).symm)

  have ex : ∃ x : (Fin (i + 2) → G) →₀ R₃.X₂, mR (R₃.g) (i + 2) x
      = (iCycles (R₃.X₃) (i + 2)).hom c₀ := exists_lift hR₃ (i + 2) _
  obtain ⟨x, hx⟩ := ex
  have em : ∃ m : (Fin (i + 2) → G) →₀ R₂.X₂, mR (β.τ₂) (i + 2) m = x :=
    exists_lift hC₂ (i + 2) x
  obtain ⟨m, hm⟩ := em
  let u : (Fin (i + 2) → G) →₀ R₂.X₃ := mR (R₂.g) (i + 2) m
  have hu : mR (β.τ₃) (i + 2) u = (iCycles (R₃.X₃) (i + 2)).hom c₀ := by
    show mR (β.τ₃) (i + 2) (mR (R₂.g) (i + 2) m) = _
    rw [mR_sq_g β, hm, hx]

  have hgdx : mR (R₃.g) (i + 1) ((inhomogeneousChains.d (R₃.X₂) (i + 1)).hom x) = 0 := by
    rw [← d_mR, hx, hc]
  have ey : ∃ y : (Fin (i + 1) → G) →₀ R₃.X₁, mR (R₃.f) (i + 1) y
      = (inhomogeneousChains.d (R₃.X₂) (i + 1)).hom x := exists_preimage hR₃ (i + 1) _ hgdx
  obtain ⟨y, hy⟩ := ey
  have hdy : (inhomogeneousChains.d (R₃.X₁) i).hom y = 0 := by
    apply mR_injective hR₃ i
    show mR (R₃.f) i _ = mR (R₃.f) i 0
    rw [← d_mR, hy, d_d_apply, map_zero]

  have ey' : ∃ y' : (Fin (i + 1) → G) →₀ R₂.X₁, mR (β.τ₁) (i + 1) y' = y :=
    exists_lift hC₁ (i + 1) y
  obtain ⟨y', hy'⟩ := ey'

  have hker₂ : mR (β.τ₂) (i + 1) ((inhomogeneousChains.d (R₂.X₂) (i + 1)).hom m
      - mR (R₂.f) (i + 1) y') = 0 := by
    rw [map_sub, ← d_mR, hm, mR_sq_f β, hy', hy, sub_self]
  have ev' : ∃ v' : (Fin (i + 1) → G) →₀ R₁.X₂, mR (α.τ₂) (i + 1) v'
      = (inhomogeneousChains.d (R₂.X₂) (i + 1)).hom m - mR (R₂.f) (i + 1) y' :=
    exists_preimage hC₂ (i + 1) _ hker₂
  obtain ⟨v', hv'⟩ := ev'
  let v : (Fin (i + 1) → G) →₀ R₁.X₃ := mR (R₁.g) (i + 1) v'
  have hv : mR (α.τ₃) (i + 1) v = (inhomogeneousChains.d (R₂.X₃) (i + 1)).hom u := by
    show mR (α.τ₃) (i + 1) (mR (R₁.g) (i + 1) v') = (inhomogeneousChains.d (R₂.X₃) (i + 1)).hom
      (mR (R₂.g) (i + 2) m)
    rw [mR_sq_g α, hv', map_sub, d_mR,
      show mR (R₂.g) (i + 1) (mR (R₂.f) (i + 1) y') = 0 from by
        refine Finsupp.ext fun a => ?_
        rw [mR_apply, mR_apply]
        exact g_f_apply (R₂) (y' a), sub_zero]
  have hdv : (inhomogeneousChains.d (R₁.X₃) i).hom v = 0 := by
    apply mR_injective hC₃ i
    show mR (α.τ₃) i _ = mR (α.τ₃) i 0
    rw [← d_mR, hv, d_d_apply, map_zero]

  have hker₁ : mR (β.τ₁) i ((inhomogeneousChains.d (R₂.X₁) i).hom y') = 0 := by
    rw [← d_mR, hy', hdy]
  have ez : ∃ z : (Fin i → G) →₀ R₁.X₁, mR (α.τ₁) i z
      = (inhomogeneousChains.d (R₂.X₁) i).hom y' := exists_preimage hC₁ i _ hker₁
  obtain ⟨z, hz⟩ := ez

  have hker₃ : mR (R₁.g) i ((inhomogeneousChains.d (R₁.X₂) i).hom v') = 0 := by
    rw [← d_mR]
    exact hdv
  have ew : ∃ w : (Fin i → G) →₀ R₁.X₁, mR (R₁.f) i w
      = (inhomogeneousChains.d (R₁.X₂) i).hom v' := exists_preimage hR₁ i _ hker₃
  obtain ⟨w, hw⟩ := ew

  have hzw : z + w = 0 := by
    apply mR_injective hC₁ i
    apply mR_injective hR₂ i
    show mR (R₂.f) i (mR (α.τ₁) i (z + w)) = mR (R₂.f) i (mR (α.τ₁) i 0)
    rw [map_add, map_add, map_zero, map_zero, hz, ← mR_sq_f α, hw, ← d_mR, ← d_mR, hv',
      map_sub, add_sub_cancel, d_d_apply]

  have Hx : ((chainsMap (MonoidHom.id G) (R₃).g).f (i + 2)).hom x
      = (iCycles (R₃.X₃) (i + 2)).hom c₀ := by
    rw [chainsMap_id_f_hom_eq_mapRange]; exact hx
  have Hy : mR (R₃.f) (i + 1) y = (inhomogeneousChains (R₃).X₂).d (i + 2) (i + 1) x := by
    rw [inhomogeneousChains.d_def]; exact hy
  have Hdy : (inhomogeneousChains (ShortComplex.mk α.τ₁ β.τ₁ h₁).X₃).d (i + 1) i y = 0 := by
    rw [inhomogeneousChains.d_def]; exact hdy
  have Hy' : ((chainsMap (MonoidHom.id G) (ShortComplex.mk α.τ₁ β.τ₁ h₁).g).f (i + 1)).hom y' = y := by
    rw [chainsMap_id_f_hom_eq_mapRange]; exact hy'
  have Hz : mR (α.τ₁) i z = (inhomogeneousChains (ShortComplex.mk α.τ₁ β.τ₁ h₁).X₂).d (i + 1) i y' := by
    rw [inhomogeneousChains.d_def]; exact hz
  have Hu : ((chainsMap (MonoidHom.id G) (ShortComplex.mk α.τ₃ β.τ₃ h₃).g).f (i + 2)).hom u
      = (iCycles (R₃.X₃) (i + 2)).hom c₀ := by
    rw [chainsMap_id_f_hom_eq_mapRange]; exact hu
  have Hv : mR (α.τ₃) (i + 1) v = (inhomogeneousChains (ShortComplex.mk α.τ₃ β.τ₃ h₃).X₂).d (i + 2) (i + 1) u := by
    rw [inhomogeneousChains.d_def]; exact hv
  have Hdv : (inhomogeneousChains (R₁).X₃).d (i + 1) i v = 0 := by
    rw [inhomogeneousChains.d_def]; exact hdv
  have Hv' : ((chainsMap (MonoidHom.id G) (R₁).g).f (i + 1)).hom v' = v := by
    rw [chainsMap_id_f_hom_eq_mapRange]
  have Hw : mR (R₁.f) i w = (inhomogeneousChains (R₁).X₂).d (i + 1) i v' := by
    rw [inhomogeneousChains.d_def]; exact hw
  have keyR : (groupHomology.δ hR₃ (i + 2) (i + 1) rfl).hom ((groupHomology.π (R₃.X₃) (i + 2)).hom
      (cyclesMk (i + 2) (i + 1) (by simp) ((iCycles _ (i + 2)).hom c₀) hc'))
      = (groupHomology.π (R₃.X₁) (i + 1)).hom (cyclesMkOfCompEqD hR₃ Hy) :=
    groupHomology.δ_apply hR₃ rfl _ hc' x Hx y Hy
  have keyC : (groupHomology.δ hC₁ (i + 1) i rfl).hom ((groupHomology.π (R₃.X₁) (i + 1)).hom
      (cyclesMkOfCompEqD hR₃ Hy))
      = (groupHomology.π (R₁.X₁) i).hom (cyclesMkOfCompEqD hC₁ Hz) :=
    groupHomology.δ_apply hC₁ rfl y Hdy y' Hy' z Hz
  have keyC' : (groupHomology.δ hC₃ (i + 2) (i + 1) rfl).hom ((groupHomology.π (R₃.X₃) (i + 2)).hom
      (cyclesMk (i + 2) (i + 1) (by simp) ((iCycles _ (i + 2)).hom c₀) hc'))
      = (groupHomology.π (R₁.X₃) (i + 1)).hom (cyclesMkOfCompEqD hC₃ Hv) :=
    groupHomology.δ_apply hC₃ rfl _ hc' u Hu v Hv
  have keyR' : (groupHomology.δ hR₁ (i + 1) i rfl).hom ((groupHomology.π (R₁.X₃) (i + 1)).hom
      (cyclesMkOfCompEqD hC₃ Hv))
      = (groupHomology.π (R₁.X₁) i).hom (cyclesMkOfCompEqD hR₁ Hw) :=
    groupHomology.δ_apply hR₁ rfl v Hdv v' Hv' w Hw

  have hcyc : ∀ (t : (Fin i → G) →₀ R₁.X₁),
      (∀ (j : ℕ) (hj : j + 1 = i), (inhomogeneousChains (R₁.X₁)).d i j t = 0) →
      (inhomogeneousChains (R₁.X₁)).d i ((ComplexShape.down ℕ).next i) t = 0 := by
    intro t ht
    by_cases hij : (ComplexShape.down ℕ).next i + 1 = i
    · exact ht _ hij
    · rw [(inhomogeneousChains (R₁.X₁)).shape _ _ hij]
      rfl
  have hdz : (inhomogeneousChains (R₁.X₁)).d i ((ComplexShape.down ℕ).next i) z = 0 := by
    refine hcyc z fun j hj => ?_
    subst hj
    rw [inhomogeneousChains.d_def]
    apply mR_injective hC₁ j
    show mR (α.τ₁) j _ = mR (α.τ₁) j 0
    rw [← d_mR, hz, d_d_apply, map_zero]
  have hdw : (inhomogeneousChains (R₁.X₁)).d i ((ComplexShape.down ℕ).next i) w = 0 := by
    refine hcyc w fun j hj => ?_
    subst hj
    rw [inhomogeneousChains.d_def]
    apply mR_injective hR₁ j
    show mR (R₁.f) j _ = mR (R₁.f) j 0
    rw [← d_mR, hw, d_d_apply, map_zero]
  have e : cyclesMk (A := R₁.X₁) i _ rfl z hdz + cyclesMk (A := R₁.X₁) i _ rfl w hdw = 0 :=
    iCycles_injective (R₁.X₁) i (by
      rw [map_add, map_zero, i_cyclesMk, i_cyclesMk]
      exact hzw)
  rw [hπ, keyR, keyC, keyC', keyR']
  show (groupHomology.π (R₁.X₁) i).hom (cyclesMk (A := R₁.X₁) i _ rfl z hdz)
    = -((groupHomology.π (R₁.X₁) i).hom (cyclesMk (A := R₁.X₁) i _ rfl w hdw))
  rw [eq_neg_of_add_eq_zero_left e, map_neg]

end P2mS26GH

namespace P2mS26GS
open groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

theorem g_f_apply (S : ShortComplex (Rep.{u} k G)) (a : S.X₁) : S.g.hom (S.f.hom a) = 0 := by
  rw [← Rep.comp_apply, S.zero]
  rfl

theorem f_injective {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) : Function.Injective S.f.hom :=
  (Rep.mono_iff_injective S.f).1 hS.mono_f

theorem g_surjective {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) : Function.Surjective S.g.hom :=
  (Rep.epi_iff_surjective S.g).1 hS.epi_g

theorem exists_preimage {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) (v : S.X₂) (hv : S.g.hom v = 0) :
    ∃ u : S.X₁, S.f.hom u = v := by
  have h : LinearMap.range S.f.hom.toLinearMap = LinearMap.ker S.g.hom.toLinearMap :=
    (hS.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  have hv' : v ∈ LinearMap.range S.f.hom.toLinearMap := by
    rw [h]
    exact hv
  obtain ⟨u, hu⟩ := hv'
  exact ⟨u, hu⟩

theorem exchange {A A' B B' : Rep.{u} k G} (f : A ⟶ A') (g : B ⟶ B') (t : (A ⊗ B : Rep.{u} k G)) :
    (A' ◁ g).hom ((f ▷ B).hom t) = (f ▷ B').hom ((A ◁ g).hom t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add t t' ht ht' => simp only [map_add, ht, ht']

theorem sq_f {S T : ShortComplex (Rep.{u} k G)} (τ : S ⟶ T) (t : S.X₁) : τ.τ₂.hom (S.f.hom t) = T.f.hom (τ.τ₁.hom t) := by
  have := congrArg (fun φ => φ.hom t) τ.comm₁₂
  simpa [Rep.comp_apply] using this.symm

theorem sq_g {S T : ShortComplex (Rep.{u} k G)} (τ : S ⟶ T) (t : S.X₂) : τ.τ₃.hom (S.g.hom t) = T.g.hom (τ.τ₂.hom t) := by
  have := congrArg (fun φ => φ.hom t) τ.comm₂₃
  simpa [Rep.comp_apply] using this.symm

variable [Fintype G]

theorem seam_neg1 {R₁ R₂ R₃ : ShortComplex (Rep.{u} k G)}
    (hR₁ : R₁.ShortExact) (hR₂ : R₂.ShortExact) (hR₃ : R₃.ShortExact) (α : R₁ ⟶ R₂) (β : R₂ ⟶ R₃)
    (h₁ : α.τ₁ ≫ β.τ₁ = 0) (h₂ : α.τ₂ ≫ β.τ₂ = 0) (h₃ : α.τ₃ ≫ β.τ₃ = 0)
    (hC₁ : (ShortComplex.mk α.τ₁ β.τ₁ h₁).ShortExact) (hC₂ : (ShortComplex.mk α.τ₂ β.τ₂ h₂).ShortExact)
    (hC₃ : (ShortComplex.mk α.τ₃ β.τ₃ h₃).ShortExact)
    (c : R₃.X₃.tateHneg1) :
    Rep.tateδ₀ hC₁ (Rep.tateδneg1 hR₃ c) = -(Rep.tateδ₀ hR₁ (Rep.tateδneg1 hC₃ c)) := by

  obtain ⟨c₁, hc₁⟩ := Submodule.Quotient.mk_surjective _ (c : R₃.X₃.ρ.Coinvariants)
  have hN : R₃.X₃.ρ.norm c₁ = 0 := by
    have h2 := c.2
    rw [LinearMap.mem_ker, ← hc₁] at h2
    exact congrArg Subtype.val h2
  have ex₂ : ∃ x₂ : R₃.X₂, (R₃.g).hom x₂ = c₁ := g_surjective hR₃ c₁
  obtain ⟨x₂, hx₂⟩ := ex₂
  have em : ∃ m : R₂.X₂, (β.τ₂).hom m = x₂ := g_surjective hC₂ x₂
  obtain ⟨m, hm⟩ := em

  have hb : R₃.X₃.ρ.norm ((R₃.g).hom ((β.τ₂).hom m)) = 0 := by
    rw [hm, hx₂, hN]
  have hb' : R₃.X₃.ρ.norm ((β.τ₃).hom ((R₂.g).hom m)) = 0 := by
    rw [sq_g β, hm, hx₂, hN]
  have hcR : c = Rep.seamθ (R₃) ⟨(β.τ₂).hom m, hb⟩ := by
    apply Subtype.ext
    rw [Rep.coe_seamθ_apply, ← hc₁]
    show _ = Representation.Coinvariants.mk _ ((R₃.g).hom ((β.τ₂).hom m))
    rw [hm, hx₂]
    rfl
  have hcC : c = Rep.seamθ (ShortComplex.mk α.τ₃ β.τ₃ h₃) ⟨(R₂.g).hom m, hb'⟩ := by
    apply Subtype.ext
    rw [Rep.coe_seamθ_apply, ← hc₁]
    show _ = Representation.Coinvariants.mk _ ((β.τ₃).hom ((R₂.g).hom m))
    rw [sq_g β, hm, hx₂]
    rfl

  have hNm : ∀ h : G, R₂.X₂.ρ h (R₂.X₂.ρ.norm m)
      = R₂.X₂.ρ.norm m := fun h =>
    (Representation.mem_invariants _ _).1 (Representation.norm_apply_mem_invariants _ _) h

  let aR : R₃.X₁.ρ.invariants :=
    ⟨Rep.seamψ hR₃ ⟨(β.τ₂).hom m, hb⟩, Rep.seamψ_mem_invariants hR₃ _⟩
  have haR : (R₃.f).hom (aR : R₃.X₁)
      = R₃.X₂.ρ.norm ((β.τ₂).hom m) := Rep.f_seamψ hR₃ _

  have ey : ∃ y : R₂.X₁, (β.τ₁).hom y = aR :=
    g_surjective hC₁ (aR : R₃.X₁)
  obtain ⟨y, hy⟩ := ey

  have hker : (β.τ₂).hom (R₂.X₂.ρ.norm m - (R₂.f).hom y) = 0 := by
    rw [map_sub, Rep.hom_norm_apply, sq_f β, hy, haR, sub_self]
  have ey₂ : ∃ y₂ : R₁.X₂, (α.τ₂).hom y₂
      = R₂.X₂.ρ.norm m - (R₂.f).hom y := exists_preimage hC₂ _ hker
  obtain ⟨y₂, hy₂⟩ := ey₂

  have ha'eq : (α.τ₃).hom ((R₁.g).hom y₂)
      = R₂.X₃.ρ.norm ((R₂.g).hom m) := by
    rw [sq_g α, hy₂, map_sub, Rep.hom_norm_apply,
      show (R₂.g).hom ((R₂.f).hom y) = 0 from g_f_apply (R₂) y, sub_zero]
  have ha'inv : (R₁.g).hom y₂ ∈ R₁.X₃.ρ.invariants := by
    rw [Representation.mem_invariants]
    intro h
    apply f_injective hC₃
    show (α.τ₃).hom _ = (α.τ₃).hom _
    rw [Rep.hom_comm_apply, ha'eq]
    exact (Representation.mem_invariants _ _).1 (Representation.norm_apply_mem_invariants _ _) h
  let aC : R₁.X₃.ρ.invariants := ⟨(R₁.g).hom y₂, ha'inv⟩

  have h1R : Rep.tateδneg1 hR₃ c = Submodule.Quotient.mk aR := by
    rw [hcR]
    exact Rep.tateδneg1_mk hR₃ _ hb aR haR
  have h1C : Rep.tateδneg1 hC₃ c = Submodule.Quotient.mk aC := by
    rw [hcC]
    exact Rep.tateδneg1_mk hC₃ _ hb' aC ha'eq

  have ex : ∀ h : G, ∃ t : R₁.X₁, (α.τ₁).hom t
      = R₂.X₁.ρ h y - y := fun h => exists_preimage hC₁ _ (by
    show (β.τ₁).hom (R₂.X₁.ρ h y - y) = 0
    rw [map_sub, Rep.hom_comm_apply, hy, sub_eq_zero]
    exact (Representation.mem_invariants _ _).1 aR.2 h)
  choose x hx using ex
  have ex' : ∀ h : G, ∃ t : R₁.X₁, (R₁.f).hom t
      = R₁.X₂.ρ h y₂ - y₂ := fun h => exists_preimage hR₁ _ (by
    show (R₁.g).hom (R₁.X₂.ρ h y₂ - y₂) = 0
    rw [map_sub, Rep.hom_comm_apply, sub_eq_zero]
    exact (Representation.mem_invariants _ _).1 ha'inv h)
  choose x' hx' using ex'

  have hxx : ∀ h, x h + x' h = 0 := fun h => by
    apply f_injective hC₁
    apply f_injective hR₂
    show (R₂.f).hom ((α.τ₁).hom (x h + x' h)) = (R₂.f).hom ((α.τ₁).hom 0)
    rw [map_add, map_add, hx h, ← sq_f α (x' h), hx' h, map_sub, map_sub, Rep.hom_comm_apply,
      Rep.hom_comm_apply (α.τ₂), hy₂, map_zero, map_zero, map_sub, hNm h]
    abel

  have hL : Rep.tateδ₀ hC₁ (Rep.tateδneg1 hR₃ c)
      = groupCohomology.H1π (R₁.X₁) ⟨x, groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ hC₁ (funext hx)⟩ := by
    rw [h1R]
    exact groupCohomology.δ₀_apply hC₁ aR y hy x (funext hx)
  have hR' : Rep.tateδ₀ hR₁ (Rep.tateδneg1 hC₃ c)
      = groupCohomology.H1π (R₁.X₁) ⟨x', groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ hR₁ (funext hx')⟩ := by
    rw [h1C]
    exact groupCohomology.δ₀_apply hR₁ aC y₂ rfl x' (funext hx')
  rw [hL, hR']
  have e : (⟨x, groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ hC₁ (funext hx)⟩ : groupCohomology.cocycles₁ (R₁.X₁))
      = -⟨x', groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ hR₁ (funext hx')⟩ :=
    Subtype.ext (funext fun h => eq_neg_of_add_eq_zero_left (hxx h))
  exact (congrArg (groupCohomology.H1π (R₁.X₁)).hom e).trans (map_neg _ _)

end P2mS26GS

namespace P2mS26GS
open groupHomology Finsupp

variable {k G : Type u} [CommRing k] [Group G]

theorem d₁₀_mapRange {A B : Rep.{u} k G} (φ : A ⟶ B) (t : G →₀ A) :
    (d₁₀ B).hom (mapRange.linearMap φ.hom.toLinearMap t) = φ.hom ((d₁₀ A).hom t) := by
  induction t using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single g a =>
    rw [mapRange.linearMap_apply, mapRange_single]
    show (d₁₀ B).hom (single g (φ.hom a)) = φ.hom ((d₁₀ A).hom (single g a))
    rw [show (d₁₀ B).hom (single g (φ.hom a)) = B.ρ g⁻¹ (φ.hom a) - φ.hom a from d₁₀_single (A := B) g (φ.hom a),
      show (d₁₀ A).hom (single g a) = A.ρ g⁻¹ a - a from d₁₀_single (A := A) g a, map_sub, Rep.hom_comm_apply]

variable [Fintype G]

theorem norm_d₁₀ (A : Rep.{u} k G) (t : G →₀ A) : A.ρ.norm ((d₁₀ A).hom t) = 0 :=
  Rep.norm_eq_zero_of_mem_coinvariantsKer A (by
    rw [← range_d₁₀_eq_coinvariantsKer]
    exact ⟨t, rfl⟩)

theorem seam_neg2 {R₁ R₂ R₃ : ShortComplex (Rep.{u} k G)}
    (hR₁ : R₁.ShortExact) (hR₂ : R₂.ShortExact) (hR₃ : R₃.ShortExact) (α : R₁ ⟶ R₂) (β : R₂ ⟶ R₃)
    (h₁ : α.τ₁ ≫ β.τ₁ = 0) (h₂ : α.τ₂ ≫ β.τ₂ = 0) (h₃ : α.τ₃ ≫ β.τ₃ = 0)
    (hC₁ : (ShortComplex.mk α.τ₁ β.τ₁ h₁).ShortExact) (hC₂ : (ShortComplex.mk α.τ₂ β.τ₂ h₂).ShortExact)
    (hC₃ : (ShortComplex.mk α.τ₃ β.τ₃ h₃).ShortExact)
    (c : groupHomology (R₃.X₃) 1) :
    Rep.tateδneg1 hC₁ (Rep.tateδneg2 hR₃ c) = -(Rep.tateδneg1 hR₁ (Rep.tateδneg2 hC₃ c)) := by
  induction c using groupHomology.H1_induction_on with
  | h γ =>

  obtain ⟨ν, hν0⟩ := Finsupp.mapRange_surjective _ (map_zero (R₃.g).hom.toLinearMap) (g_surjective hR₃) γ.1
  obtain ⟨μ, hμ0⟩ := Finsupp.mapRange_surjective _ (map_zero (β.τ₂).hom.toLinearMap) (g_surjective hC₂) ν
  have hν : mapRange.linearMap (R₃.g).hom.toLinearMap (mapRange.linearMap (β.τ₂).hom.toLinearMap μ)
      = γ.1 := by
    rw [mapRange.linearMap_apply, mapRange.linearMap_apply, hμ0, hν0]
  have hν' : mapRange.linearMap (β.τ₃).hom.toLinearMap (mapRange.linearMap (R₂.g).hom.toLinearMap μ)
      = γ.1 := by
    rw [← hν]
    refine Finsupp.ext fun a => ?_
    simp only [mapRange.linearMap_apply, mapRange_apply]
    exact sq_g β (μ a)

  let dμ : R₂.X₂ := (d₁₀ (R₂.X₂)).hom μ
  have hgd : (R₃.g).hom ((β.τ₂).hom dμ) = 0 := by
    show (R₃.g).hom ((β.τ₂).hom ((d₁₀ (R₂.X₂)).hom μ)) = 0
    rw [← d₁₀_mapRange (β.τ₂), ← d₁₀_mapRange (R₃.g), hν]
    exact γ.2

  obtain ⟨t, ht0⟩ := exists_preimage hR₃ _ hgd
  have ht : (R₃.f).hom t = (β.τ₂).hom dμ := ht0
  obtain ⟨b₀, hb₀0⟩ := g_surjective hC₁ t
  have hb₀ : (β.τ₁).hom b₀ = t := hb₀0
  have hker : (β.τ₂).hom (dμ - (R₂.f).hom b₀) = 0 := by
    rw [map_sub, sq_f β, hb₀, ht, sub_self]
  obtain ⟨b₂, hb₂0⟩ := exists_preimage hC₂ _ hker
  have hb₂ : (α.τ₂).hom b₂ = dμ - (R₂.f).hom b₀ := hb₂0
  have ht' : (α.τ₃).hom ((R₁.g).hom b₂)
      = (R₂.g).hom dμ := by
    rw [sq_g α, hb₂, map_sub, show (R₂.g).hom ((R₂.f).hom b₀) = 0 from
      g_f_apply (R₂) b₀, sub_zero]

  have hδR : (groupHomology.δ hR₃ 1 0 rfl).hom ((groupHomology.H1π (R₃.X₃)).hom γ)
      = (groupHomology.H0π (R₃.X₁)).hom t :=
    groupHomology.δ₀_apply hR₃ γ (mapRange.linearMap (β.τ₂).hom.toLinearMap μ) hν t
      (by
        show (R₃.f).hom t = (d₁₀ (R₃.X₂)).hom (mapRange.linearMap (β.τ₂).hom.toLinearMap μ)
        rw [ht, d₁₀_mapRange])
  have hδC : (groupHomology.δ hC₃ 1 0 rfl).hom ((groupHomology.H1π (R₃.X₃)).hom γ)
      = (groupHomology.H0π (R₁.X₃)).hom ((R₁.g).hom b₂) :=
    groupHomology.δ₀_apply hC₃ γ (mapRange.linearMap (R₂.g).hom.toLinearMap μ) hν' _
      (by
        show (α.τ₃).hom ((R₁.g).hom b₂)
          = (d₁₀ (R₂.X₃)).hom (mapRange.linearMap (R₂.g).hom.toLinearMap μ)
        rw [ht', d₁₀_mapRange])

  have hsR : (Rep.tateδneg2 hR₃ ((groupHomology.H1π (R₃.X₃)).hom γ)).1
      = Representation.Coinvariants.mk _ t := by
    rw [Rep.coe_tateδneg2_apply]
    show (groupHomology.H0Iso (R₃.X₁)).hom.hom ((groupHomology.δ hR₃ 1 0 rfl).hom _) = _
    rw [hδR]
    exact groupHomology.H0π_comp_H0Iso_hom_apply _ _
  have hsC : (Rep.tateδneg2 hC₃ ((groupHomology.H1π (R₃.X₃)).hom γ)).1
      = Representation.Coinvariants.mk _ ((R₁.g).hom b₂) := by
    rw [Rep.coe_tateδneg2_apply]
    show (groupHomology.H0Iso (R₁.X₃)).hom.hom ((groupHomology.δ hC₃ 1 0 rfl).hom _) = _
    rw [hδC]
    exact groupHomology.H0π_comp_H0Iso_hom_apply _ _

  have hNb₀ : R₃.X₁.ρ.norm ((β.τ₁).hom b₀) = 0 := by
    have h2 := (Rep.tateδneg2 hR₃ ((groupHomology.H1π (R₃.X₃)).hom γ)).2
    rw [LinearMap.mem_ker, hsR] at h2
    rw [hb₀]
    exact congrArg Subtype.val h2
  have hNb₂ : R₁.X₃.ρ.norm ((R₁.g).hom b₂) = 0 := by
    have h2 := (Rep.tateδneg2 hC₃ ((groupHomology.H1π (R₃.X₃)).hom γ)).2
    rw [LinearMap.mem_ker, hsC] at h2
    exact congrArg Subtype.val h2
  have hθR : Rep.tateδneg2 hR₃ ((groupHomology.H1π (R₃.X₃)).hom γ)
      = Rep.seamθ (ShortComplex.mk α.τ₁ β.τ₁ h₁) ⟨b₀, hNb₀⟩ := by
    apply Subtype.ext
    rw [hsR, Rep.coe_seamθ_apply]
    show _ = Representation.Coinvariants.mk _ ((β.τ₁).hom b₀)
    rw [hb₀]
  have hθC : Rep.tateδneg2 hC₃ ((groupHomology.H1π (R₃.X₃)).hom γ)
      = Rep.seamθ (R₁) ⟨b₂, hNb₂⟩ := by
    apply Subtype.ext
    rw [hsC, Rep.coe_seamθ_apply]

  let aR : R₁.X₁.ρ.invariants :=
    ⟨Rep.seamψ hC₁ ⟨b₀, hNb₀⟩, Rep.seamψ_mem_invariants hC₁ _⟩
  have haR : (α.τ₁).hom (aR : R₁.X₁) = R₂.X₁.ρ.norm b₀ :=
    Rep.f_seamψ hC₁ _
  let aC : R₁.X₁.ρ.invariants :=
    ⟨Rep.seamψ hR₁ ⟨b₂, hNb₂⟩, Rep.seamψ_mem_invariants hR₁ _⟩
  have haC : (R₁.f).hom (aC : R₁.X₁) = R₁.X₂.ρ.norm b₂ :=
    Rep.f_seamψ hR₁ _
  have h1R : Rep.tateδneg1 hC₁ (Rep.tateδneg2 hR₃ ((groupHomology.H1π (R₃.X₃)).hom γ))
      = Submodule.Quotient.mk aR := by
    rw [hθR]
    exact Rep.tateδneg1_mk hC₁ b₀ hNb₀ aR haR
  have h1C : Rep.tateδneg1 hR₁ (Rep.tateδneg2 hC₃ ((groupHomology.H1π (R₃.X₃)).hom γ))
      = Submodule.Quotient.mk aC := by
    rw [hθC]
    exact Rep.tateδneg1_mk hR₁ b₂ hNb₂ aC haC

  have haa : (aR : R₁.X₁) + aC = 0 := by
    apply f_injective hC₁
    apply f_injective hR₂
    show (R₂.f).hom ((α.τ₁).hom ((aR : R₁.X₁) + aC))
      = (R₂.f).hom ((α.τ₁).hom 0)
    rw [map_add, map_add, haR, ← sq_f α, haC, Rep.hom_norm_apply, Rep.hom_norm_apply, hb₂,
      ← map_add, add_sub_cancel, norm_d₁₀, map_zero, map_zero]
  show Rep.tateδneg1 hC₁ (Rep.tateδneg2 hR₃ ((groupHomology.H1π (R₃.X₃)).hom γ))
    = -(Rep.tateδneg1 hR₁ (Rep.tateδneg2 hC₃ ((groupHomology.H1π (R₃.X₃)).hom γ)))
  rw [h1R, h1C]
  have e : aR = -aC := Subtype.ext (eq_neg_of_add_eq_zero_left haa)
  exact (congrArg (Submodule.Quotient.mk (p := LinearMap.range R₁.X₁.ρ.normBar)) e).trans
    (Submodule.Quotient.mk_neg _)

end P2mS26GS

namespace P2mS26GG

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] {R₁ R₂ R₃ : ShortComplex (Rep.{u} k G)}
  (hR₁ : R₁.ShortExact) (hR₂ : R₂.ShortExact) (hR₃ : R₃.ShortExact) (v : R₁ ⟶ R₂) (w : R₂ ⟶ R₃)
  (h₁ : v.τ₁ ≫ w.τ₁ = 0) (h₂ : v.τ₂ ≫ w.τ₂ = 0) (h₃ : v.τ₃ ≫ w.τ₃ = 0)
  (hC₁ : (ShortComplex.mk v.τ₁ w.τ₁ h₁).ShortExact) (hC₂ : (ShortComplex.mk v.τ₂ w.τ₂ h₂).ShortExact)
  (hC₃ : (ShortComplex.mk v.τ₃ w.τ₃ h₃).ShortExact)
include hR₁ hR₂ hR₃ hC₁ hC₂ hC₃

theorem regime_pos (m : ℕ) :
    Rep.tateδ hR₃ (Int.ofNat (m + 1)) ≫ Rep.tateδ hC₁ (Int.ofNat (m + 1) + 1)
      = -(Rep.tateδ hC₃ (Int.ofNat (m + 1)) ≫ Rep.tateδ hR₁ (Int.ofNat (m + 1) + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact P2mS26GC.coh_chase hR₁ hR₂ hR₃ v w h₁ h₂ h₃ hC₁ hC₂ hC₃ (m + 1) c

theorem regime_zero :
    Rep.tateδ hR₃ (Int.ofNat 0) ≫ Rep.tateδ hC₁ (Int.ofNat 0 + 1)
      = -(Rep.tateδ hC₃ (Int.ofNat 0) ≫ Rep.tateδ hR₁ (Int.ofNat 0 + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact P2mS26GC.coh_chase hR₁ hR₂ hR₃ v w h₁ h₂ h₃ hC₁ hC₂ hC₃ 0 (((groupCohomology.H0Iso R₃.X₃).inv).hom z)

theorem regime_neg_one :
    Rep.tateδ hR₃ (Int.negSucc 0) ≫ Rep.tateδ hC₁ (Int.negSucc 0 + 1)
      = -(Rep.tateδ hC₃ (Int.negSucc 0) ≫ Rep.tateδ hR₁ (Int.negSucc 0 + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact P2mS26GS.seam_neg1 hR₁ hR₂ hR₃ v w h₁ h₂ h₃ hC₁ hC₂ hC₃ c

theorem regime_neg_two :
    Rep.tateδ hR₃ (Int.negSucc 1) ≫ Rep.tateδ hC₁ (Int.negSucc 1 + 1)
      = -(Rep.tateδ hC₃ (Int.negSucc 1) ≫ Rep.tateδ hR₁ (Int.negSucc 1 + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact P2mS26GS.seam_neg2 hR₁ hR₂ hR₃ v w h₁ h₂ h₃ hC₁ hC₂ hC₃ c

theorem regime_neg_three :
    Rep.tateδ hR₃ (Int.negSucc 2) ≫ Rep.tateδ hC₁ (Int.negSucc 2 + 1)
      = -(Rep.tateδ hC₃ (Int.negSucc 2) ≫ Rep.tateδ hR₁ (Int.negSucc 2 + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have h2 : (groupHomology.δ hC₁ 1 0 rfl).hom ((groupHomology.δ hR₃ 2 1 rfl).hom c)
      = -((groupHomology.δ hR₁ 1 0 rfl).hom ((groupHomology.δ hC₃ 2 1 rfl).hom c)) :=
    P2mS26GH.hom_chase hR₁ hR₂ hR₃ v w h₁ h₂ h₃ hC₁ hC₂ hC₃ 0 c
  change Rep.tateδneg2 hC₁ ((groupHomology.δ hR₃ 2 1 rfl).hom c)
    = -(Rep.tateδneg2 hR₁ ((groupHomology.δ hC₃ 2 1 rfl).hom c))
  apply Subtype.ext
  rw [Submodule.coe_neg, Rep.coe_tateδneg2_apply, Rep.coe_tateδneg2_apply]
  change ((groupHomology.H0Iso R₁.X₁).hom).hom ((groupHomology.δ hC₁ 1 0 rfl).hom
      ((groupHomology.δ hR₃ 2 1 rfl).hom c))
    = -(((groupHomology.H0Iso R₁.X₁).hom).hom ((groupHomology.δ hR₁ 1 0 rfl).hom
      ((groupHomology.δ hC₃ 2 1 rfl).hom c)))
  rw [h2]
  exact map_neg ((groupHomology.H0Iso R₁.X₁).hom).hom _

theorem regime_neg (m : ℕ) :
    Rep.tateδ hR₃ (Int.negSucc (m + 3)) ≫ Rep.tateδ hC₁ (Int.negSucc (m + 3) + 1)
      = -(Rep.tateδ hC₃ (Int.negSucc (m + 3)) ≫ Rep.tateδ hR₁ (Int.negSucc (m + 3) + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact P2mS26GH.hom_chase hR₁ hR₂ hR₃ v w h₁ h₂ h₃ hC₁ hC₂ hC₃ (m + 1) c

end P2mS26GG

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {R₁ R₂ R₃ : ShortComplex (Rep.{u} k G)} (hR₁ : R₁.ShortExact) (hR₂ : R₂.ShortExact) (hR₃ : R₃.ShortExact)
    (v : R₁ ⟶ R₂) (w : R₂ ⟶ R₃)
    (h₁ : v.τ₁ ≫ w.τ₁ = 0) (h₂ : v.τ₂ ≫ w.τ₂ = 0) (h₃ : v.τ₃ ≫ w.τ₃ = 0)
    (hC₁ : (ShortComplex.mk v.τ₁ w.τ₁ h₁).ShortExact) (hC₂ : (ShortComplex.mk v.τ₂ w.τ₂ h₂).ShortExact)
    (hC₃ : (ShortComplex.mk v.τ₃ w.τ₃ h₃).ShortExact) (n : ℤ) :
    Rep.tateδ hR₃ n ≫ Rep.tateδ hC₁ (n + 1) = -(Rep.tateδ hC₃ n ≫ Rep.tateδ hR₁ (n + 1)) := by
  match n with
  | Int.ofNat (m + 1) => exact P2mS26GG.regime_pos hR₁ hR₂ hR₃ v w h₁ h₂ h₃ hC₁ hC₂ hC₃ m
  | Int.ofNat 0 => exact P2mS26GG.regime_zero hR₁ hR₂ hR₃ v w h₁ h₂ h₃ hC₁ hC₂ hC₃
  | Int.negSucc 0 => exact P2mS26GG.regime_neg_one hR₁ hR₂ hR₃ v w h₁ h₂ h₃ hC₁ hC₂ hC₃
  | Int.negSucc 1 => exact P2mS26GG.regime_neg_two hR₁ hR₂ hR₃ v w h₁ h₂ h₃ hC₁ hC₂ hC₃
  | Int.negSucc 2 => exact P2mS26GG.regime_neg_three hR₁ hR₂ hR₃ v w h₁ h₂ h₃ hC₁ hC₂ hC₃
  | Int.negSucc (m + 3) => exact P2mS26GG.regime_neg hR₁ hR₂ hR₃ v w h₁ h₂ h₃ hC₁ hC₂ hC₃ m

end S_Rep_tateDelta_comp_tateDelta_eq_neg_of_hom
end P2MW
export P2MW.S_Rep_tateDelta_comp_tateDelta_eq_neg_of_hom (solution)
