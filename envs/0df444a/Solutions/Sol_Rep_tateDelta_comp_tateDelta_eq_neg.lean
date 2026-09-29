-- Prove2me | solution 1 for Rep.tateDelta_comp_tateDelta_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/947ed968-a9af-58d1-98cc-a70cae03f8fd

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_tateDelta_comp_tateDelta_eq_neg

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

section Coh
open groupCohomology

namespace P2mS26AC

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

end P2mS26AC

namespace P2mS26AC

variable {k G : Type u} [CommRing k] [Group G]

theorem coh_chase {X Y : ShortComplex (Rep.{u} k G)}
    (hR₁ : (X.map (tensorRight Y.X₁)).ShortExact) (hR₂ : (X.map (tensorRight Y.X₂)).ShortExact)
    (hR₃ : (X.map (tensorRight Y.X₃)).ShortExact) (hC₁ : (Y.map (tensorLeft X.X₁)).ShortExact)
    (hC₂ : (Y.map (tensorLeft X.X₂)).ShortExact) (hC₃ : (Y.map (tensorLeft X.X₃)).ShortExact)
    (i : ℕ) (c : groupCohomology (X.X₃ ⊗ Y.X₃) i) :
    (groupCohomology.δ hC₁ (i + 1) (i + 2) rfl).hom ((groupCohomology.δ hR₃ i (i + 1) rfl).hom c)
      = -((groupCohomology.δ hR₁ (i + 1) (i + 2) rfl).hom ((groupCohomology.δ hC₃ i (i + 1) rfl).hom c)) := by
  obtain ⟨c₀, rfl⟩ := π_surjective (X.X₃ ⊗ Y.X₃) i c
  have hc : (inhomogeneousCochains.d (X.X₃ ⊗ Y.X₃) i).hom ((iCocycles _ i).hom c₀) = 0 := d_iCocycles _ _ c₀
  have hπ : (groupCohomology.π (X.X₃ ⊗ Y.X₃) i).hom c₀
      = (groupCohomology.π (X.X₃ ⊗ Y.X₃) i).hom (cocyclesMk ((iCocycles _ i).hom c₀) hc) :=
    congrArg _ (iCocycles_injective _ _ (i_cocyclesMk _ _).symm)

  have ex : ∃ x : (Fin i → G) → (X.X₂ ⊗ Y.X₃ : Rep.{u} k G), ∀ τ, (X.g ▷ Y.X₃).hom (x τ)
      = (iCocycles (X.X₃ ⊗ Y.X₃) i).hom c₀ τ := exists_lift hR₃ i ((iCocycles (X.X₃ ⊗ Y.X₃) i).hom c₀)
  obtain ⟨x, hx⟩ := ex
  have em : ∃ m : (Fin i → G) → (X.X₂ ⊗ Y.X₂ : Rep.{u} k G), ∀ τ, (X.X₂ ◁ Y.g).hom (m τ) = x τ :=
    exists_lift hC₂ i x
  obtain ⟨m, hm⟩ := em
  let u : (Fin i → G) → (X.X₃ ⊗ Y.X₂ : Rep.{u} k G) := fun τ => (X.g ▷ Y.X₂).hom (m τ)
  have hu : ∀ τ, (X.X₃ ◁ Y.g).hom (u τ) = (iCocycles (X.X₃ ⊗ Y.X₃) i).hom c₀ τ := fun τ => by
    show (X.X₃ ◁ Y.g).hom ((X.g ▷ Y.X₂).hom (m τ)) = _
    rw [exchange, hm τ, hx τ]

  have hgdx : ∀ τ, (X.g ▷ Y.X₃).hom ((inhomogeneousCochains.d (X.X₂ ⊗ Y.X₃) i).hom x τ) = 0 := fun τ => by
    rw [hom_d_apply (X.g ▷ Y.X₃), show (fun σ => (X.g ▷ Y.X₃).hom (x σ)) = (iCocycles (X.X₃ ⊗ Y.X₃) i).hom c₀
      from funext hx]
    exact congrFun hc τ
  have ey : ∀ τ, ∃ u : (X.X₁ ⊗ Y.X₃ : Rep.{u} k G), (X.f ▷ Y.X₃).hom u
      = (inhomogeneousCochains.d (X.X₂ ⊗ Y.X₃) i).hom x τ := fun τ => exists_preimage hR₃ _ (hgdx τ)
  choose y hy using ey
  have hdy : (inhomogeneousCochains.d (X.X₁ ⊗ Y.X₃) (i + 1)).hom y = 0 := by
    funext τ
    apply f_injective hR₃
    show (X.f ▷ Y.X₃).hom _ = (X.f ▷ Y.X₃).hom 0
    rw [hom_d_apply (X.f ▷ Y.X₃), show (fun σ => (X.f ▷ Y.X₃).hom (y σ))
      = (inhomogeneousCochains.d (X.X₂ ⊗ Y.X₃) i).hom x from funext hy, d_d_apply, map_zero]
    rfl

  have ey' : ∃ y' : (Fin (i + 1) → G) → (X.X₁ ⊗ Y.X₂ : Rep.{u} k G), ∀ τ, (X.X₁ ◁ Y.g).hom (y' τ) = y τ :=
    exists_lift hC₁ (i + 1) y
  obtain ⟨y', hy'⟩ := ey'

  have hker₂ : ∀ τ, (X.X₂ ◁ Y.g).hom ((inhomogeneousCochains.d (X.X₂ ⊗ Y.X₂) i).hom m τ
      - (X.f ▷ Y.X₂).hom (y' τ)) = 0 := fun τ => by
    rw [map_sub, hom_d_apply (X.X₂ ◁ Y.g), show (fun σ => (X.X₂ ◁ Y.g).hom (m σ)) = x from funext hm, exchange, hy' τ,
      hy τ, sub_self]
  have ev' : ∀ τ, ∃ u : (X.X₂ ⊗ Y.X₁ : Rep.{u} k G), (X.X₂ ◁ Y.f).hom u
      = (inhomogeneousCochains.d (X.X₂ ⊗ Y.X₂) i).hom m τ - (X.f ▷ Y.X₂).hom (y' τ) :=
    fun τ => exists_preimage hC₂ _ (hker₂ τ)
  choose v' hv' using ev'
  let v : (Fin (i + 1) → G) → (X.X₃ ⊗ Y.X₁ : Rep.{u} k G) := fun τ => (X.g ▷ Y.X₁).hom (v' τ)
  have hv : ∀ τ, (X.X₃ ◁ Y.f).hom (v τ) = (inhomogeneousCochains.d (X.X₃ ⊗ Y.X₂) i).hom u τ := fun τ => by
    show (X.X₃ ◁ Y.f).hom ((X.g ▷ Y.X₁).hom (v' τ)) = _
    rw [exchange, hv' τ, map_sub, hom_d_apply (X.g ▷ Y.X₂),
      show (X.g ▷ Y.X₂).hom ((X.f ▷ Y.X₂).hom (y' τ)) = 0 from g_f_apply (X.map (tensorRight Y.X₂)) (y' τ), sub_zero]
  have hdv : (inhomogeneousCochains.d (X.X₃ ⊗ Y.X₁) (i + 1)).hom v = 0 := by
    funext τ
    apply f_injective hC₃
    show (X.X₃ ◁ Y.f).hom _ = (X.X₃ ◁ Y.f).hom 0
    rw [hom_d_apply (X.X₃ ◁ Y.f), show (fun σ => (X.X₃ ◁ Y.f).hom (v σ))
      = (inhomogeneousCochains.d (X.X₃ ⊗ Y.X₂) i).hom u from funext hv, d_d_apply, map_zero]
    rfl

  have hker₁ : ∀ τ, (X.X₁ ◁ Y.g).hom ((inhomogeneousCochains.d (X.X₁ ⊗ Y.X₂) (i + 1)).hom y' τ) = 0 := fun τ => by
    rw [hom_d_apply (X.X₁ ◁ Y.g), show (fun σ => (X.X₁ ◁ Y.g).hom (y' σ)) = y from funext hy']
    exact congrFun hdy τ
  have ez : ∀ τ, ∃ u : (X.X₁ ⊗ Y.X₁ : Rep.{u} k G), (X.X₁ ◁ Y.f).hom u
      = (inhomogeneousCochains.d (X.X₁ ⊗ Y.X₂) (i + 1)).hom y' τ := fun τ => exists_preimage hC₁ _ (hker₁ τ)
  choose z hz using ez

  have hker₃ : ∀ τ, (X.g ▷ Y.X₁).hom ((inhomogeneousCochains.d (X.X₂ ⊗ Y.X₁) (i + 1)).hom v' τ) = 0 := fun τ => by
    rw [hom_d_apply (X.g ▷ Y.X₁)]
    exact congrFun hdv τ
  have ew : ∀ τ, ∃ u : (X.X₁ ⊗ Y.X₁ : Rep.{u} k G), (X.f ▷ Y.X₁).hom u
      = (inhomogeneousCochains.d (X.X₂ ⊗ Y.X₁) (i + 1)).hom v' τ := fun τ => exists_preimage hR₁ _ (hker₃ τ)
  choose w hw using ew

  have hzw : ∀ τ, z τ + w τ = 0 := fun τ => by
    apply f_injective hC₁
    apply f_injective hR₂
    show (X.f ▷ Y.X₂).hom ((X.X₁ ◁ Y.f).hom (z τ + w τ)) = (X.f ▷ Y.X₂).hom ((X.X₁ ◁ Y.f).hom 0)
    have e1 : (X.f ▷ Y.X₂).hom ((X.X₁ ◁ Y.f).hom (z τ))
        = (inhomogeneousCochains.d (X.X₂ ⊗ Y.X₂) (i + 1)).hom (fun σ => (X.f ▷ Y.X₂).hom (y' σ)) τ := by
      rw [hz τ, hom_d_apply]
    have e2 : (X.f ▷ Y.X₂).hom ((X.X₁ ◁ Y.f).hom (w τ))
        = -(inhomogeneousCochains.d (X.X₂ ⊗ Y.X₂) (i + 1)).hom (fun σ => (X.f ▷ Y.X₂).hom (y' σ)) τ := by
      rw [← exchange, hw τ, hom_d_apply (X.X₂ ◁ Y.f), show (fun σ => (X.X₂ ◁ Y.f).hom (v' σ))
        = (inhomogeneousCochains.d (X.X₂ ⊗ Y.X₂) i).hom m - fun σ => (X.f ▷ Y.X₂).hom (y' σ) from funext hv',
        map_sub, Pi.sub_apply, d_d_apply, Pi.zero_apply, zero_sub]
    rw [map_add, map_add, e1, e2, add_neg_cancel, map_zero, map_zero]

  have Hy : (X.map (tensorRight Y.X₃)).f.hom ∘ y = (inhomogeneousCochains (X.map (tensorRight Y.X₃)).X₂).d i (i + 1) x := by
    rw [inhomogeneousCochains.d_def]; exact funext hy
  have Hz : (Y.map (tensorLeft X.X₁)).f.hom ∘ z = (inhomogeneousCochains (Y.map (tensorLeft X.X₁)).X₂).d (i + 1) (i + 2) y' := by
    rw [inhomogeneousCochains.d_def]; exact funext hz
  have Hv : (Y.map (tensorLeft X.X₃)).f.hom ∘ v = (inhomogeneousCochains (Y.map (tensorLeft X.X₃)).X₂).d i (i + 1) u := by
    rw [inhomogeneousCochains.d_def]; exact funext hv
  have Hw : (X.map (tensorRight Y.X₁)).f.hom ∘ w = (inhomogeneousCochains (X.map (tensorRight Y.X₁)).X₂).d (i + 1) (i + 2) v' := by
    rw [inhomogeneousCochains.d_def]; exact funext hw
  have keyR : (groupCohomology.δ hR₃ i (i + 1) rfl).hom ((groupCohomology.π (X.X₃ ⊗ Y.X₃) i).hom
      (cocyclesMk ((iCocycles _ i).hom c₀) hc))
      = (groupCohomology.π (X.X₁ ⊗ Y.X₃) (i + 1)).hom (cocyclesMkOfCompEqD hR₃ Hy) :=
    groupCohomology.δ_apply hR₃ rfl ((iCocycles (X.X₃ ⊗ Y.X₃) i).hom c₀)
      (by rw [inhomogeneousCochains.d_def]; exact hc) x (funext fun τ => (cochainsMap_id_f_apply _ i x τ).trans (hx τ)) y Hy
  have keyC : (groupCohomology.δ hC₁ (i + 1) (i + 2) rfl).hom ((groupCohomology.π (X.X₁ ⊗ Y.X₃) (i + 1)).hom
      (cocyclesMkOfCompEqD hR₃ Hy))
      = (groupCohomology.π (X.X₁ ⊗ Y.X₁) (i + 2)).hom (cocyclesMkOfCompEqD hC₁ Hz) :=
    groupCohomology.δ_apply hC₁ rfl y (by rw [inhomogeneousCochains.d_def]; exact hdy) y'
      (funext fun τ => (cochainsMap_id_f_apply _ (i + 1) y' τ).trans (hy' τ)) z Hz
  have keyC' : (groupCohomology.δ hC₃ i (i + 1) rfl).hom ((groupCohomology.π (X.X₃ ⊗ Y.X₃) i).hom
      (cocyclesMk ((iCocycles _ i).hom c₀) hc))
      = (groupCohomology.π (X.X₃ ⊗ Y.X₁) (i + 1)).hom (cocyclesMkOfCompEqD hC₃ Hv) :=
    groupCohomology.δ_apply hC₃ rfl ((iCocycles (X.X₃ ⊗ Y.X₃) i).hom c₀)
      (by rw [inhomogeneousCochains.d_def]; exact hc) u (funext fun τ => (cochainsMap_id_f_apply _ i u τ).trans (hu τ)) v Hv
  have keyR' : (groupCohomology.δ hR₁ (i + 1) (i + 2) rfl).hom ((groupCohomology.π (X.X₃ ⊗ Y.X₁) (i + 1)).hom
      (cocyclesMkOfCompEqD hC₃ Hv))
      = (groupCohomology.π (X.X₁ ⊗ Y.X₁) (i + 2)).hom (cocyclesMkOfCompEqD hR₁ Hw) :=
    groupCohomology.δ_apply hR₁ rfl v (by rw [inhomogeneousCochains.d_def]; exact hdv) v'
      (funext fun τ => cochainsMap_id_f_apply _ (i + 1) v' τ) w Hw

  have hdz : (inhomogeneousCochains.d (X.X₁ ⊗ Y.X₁) (i + 2)).hom z = 0 := by
    funext τ
    apply f_injective hC₁
    show (X.X₁ ◁ Y.f).hom _ = (X.X₁ ◁ Y.f).hom 0
    rw [hom_d_apply (X.X₁ ◁ Y.f), show (fun σ => (X.X₁ ◁ Y.f).hom (z σ))
      = (inhomogeneousCochains.d (X.X₁ ⊗ Y.X₂) (i + 1)).hom y' from funext hz, d_d_apply, map_zero]
    rfl
  have hdw : (inhomogeneousCochains.d (X.X₁ ⊗ Y.X₁) (i + 2)).hom w = 0 := by
    funext τ
    apply f_injective hR₁
    show (X.f ▷ Y.X₁).hom _ = (X.f ▷ Y.X₁).hom 0
    rw [hom_d_apply (X.f ▷ Y.X₁), show (fun σ => (X.f ▷ Y.X₁).hom (w σ))
      = (inhomogeneousCochains.d (X.X₂ ⊗ Y.X₁) (i + 1)).hom v' from funext hw, d_d_apply, map_zero]
    rfl
  have e : cocyclesMk (A := X.X₁ ⊗ Y.X₁) z hdz + cocyclesMk (A := X.X₁ ⊗ Y.X₁) w hdw = 0 :=
    iCocycles_injective (X.X₁ ⊗ Y.X₁) (i + 2) (by
      rw [map_add, map_zero, i_cocyclesMk, i_cocyclesMk]
      exact funext hzw)
  rw [hπ, keyR, keyC, keyC', keyR']
  show (groupCohomology.π (X.X₁ ⊗ Y.X₁) (i + 2)).hom (cocyclesMk (A := X.X₁ ⊗ Y.X₁) z hdz)
    = -((groupCohomology.π (X.X₁ ⊗ Y.X₁) (i + 2)).hom (cocyclesMk (A := X.X₁ ⊗ Y.X₁) w hdw))
  rw [eq_neg_of_add_eq_zero_left e, map_neg]

end P2mS26AC

end Coh

namespace P2mS26AH
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

end P2mS26AH

namespace P2mS26AH
open groupHomology Finsupp

variable {k G : Type u} [CommRing k] [Group G]

theorem hom_chase {X Y : ShortComplex (Rep.{u} k G)}
    (hR₁ : (X.map (tensorRight Y.X₁)).ShortExact) (hR₂ : (X.map (tensorRight Y.X₂)).ShortExact)
    (hR₃ : (X.map (tensorRight Y.X₃)).ShortExact) (hC₁ : (Y.map (tensorLeft X.X₁)).ShortExact)
    (hC₂ : (Y.map (tensorLeft X.X₂)).ShortExact) (hC₃ : (Y.map (tensorLeft X.X₃)).ShortExact)
    (i : ℕ) (c : groupHomology (X.X₃ ⊗ Y.X₃) (i + 2)) :
    (groupHomology.δ hC₁ (i + 1) i rfl).hom ((groupHomology.δ hR₃ (i + 2) (i + 1) rfl).hom c)
      = -((groupHomology.δ hR₁ (i + 1) i rfl).hom ((groupHomology.δ hC₃ (i + 2) (i + 1) rfl).hom c)) := by
  obtain ⟨c₀, rfl⟩ := π_surjective (X.X₃ ⊗ Y.X₃) (i + 2) c
  have hc : (inhomogeneousChains.d (X.X₃ ⊗ Y.X₃) (i + 1)).hom ((iCycles _ (i + 2)).hom c₀) = 0 := d_iCycles _ _ c₀
  have hc' : (inhomogeneousChains (X.X₃ ⊗ Y.X₃)).d (i + 2) (i + 1) ((iCycles _ (i + 2)).hom c₀) = 0 := by
    rw [inhomogeneousChains.d_def]; exact hc
  have hπ : (groupHomology.π (X.X₃ ⊗ Y.X₃) (i + 2)).hom c₀
      = (groupHomology.π (X.X₃ ⊗ Y.X₃) (i + 2)).hom (cyclesMk (i + 2) (i + 1) (by simp) ((iCycles _ (i + 2)).hom c₀) hc') :=
    congrArg _ (iCycles_injective _ _ (i_cyclesMk _ _ _ _ _).symm)

  have ex : ∃ x : (Fin (i + 2) → G) →₀ (X.X₂ ⊗ Y.X₃ : Rep.{u} k G), mR (X.g ▷ Y.X₃) (i + 2) x
      = (iCycles (X.X₃ ⊗ Y.X₃) (i + 2)).hom c₀ := exists_lift hR₃ (i + 2) _
  obtain ⟨x, hx⟩ := ex
  have em : ∃ m : (Fin (i + 2) → G) →₀ (X.X₂ ⊗ Y.X₂ : Rep.{u} k G), mR (X.X₂ ◁ Y.g) (i + 2) m = x :=
    exists_lift hC₂ (i + 2) x
  obtain ⟨m, hm⟩ := em
  let u : (Fin (i + 2) → G) →₀ (X.X₃ ⊗ Y.X₂ : Rep.{u} k G) := mR (X.g ▷ Y.X₂) (i + 2) m
  have hu : mR (X.X₃ ◁ Y.g) (i + 2) u = (iCycles (X.X₃ ⊗ Y.X₃) (i + 2)).hom c₀ := by
    show mR (X.X₃ ◁ Y.g) (i + 2) (mR (X.g ▷ Y.X₂) (i + 2) m) = _
    rw [mR_exchange, hm, hx]

  have hgdx : mR (X.g ▷ Y.X₃) (i + 1) ((inhomogeneousChains.d (X.X₂ ⊗ Y.X₃) (i + 1)).hom x) = 0 := by
    rw [← d_mR, hx, hc]
  have ey : ∃ y : (Fin (i + 1) → G) →₀ (X.X₁ ⊗ Y.X₃ : Rep.{u} k G), mR (X.f ▷ Y.X₃) (i + 1) y
      = (inhomogeneousChains.d (X.X₂ ⊗ Y.X₃) (i + 1)).hom x := exists_preimage hR₃ (i + 1) _ hgdx
  obtain ⟨y, hy⟩ := ey
  have hdy : (inhomogeneousChains.d (X.X₁ ⊗ Y.X₃) i).hom y = 0 := by
    apply mR_injective hR₃ i
    show mR (X.f ▷ Y.X₃) i _ = mR (X.f ▷ Y.X₃) i 0
    rw [← d_mR, hy, d_d_apply, map_zero]

  have ey' : ∃ y' : (Fin (i + 1) → G) →₀ (X.X₁ ⊗ Y.X₂ : Rep.{u} k G), mR (X.X₁ ◁ Y.g) (i + 1) y' = y :=
    exists_lift hC₁ (i + 1) y
  obtain ⟨y', hy'⟩ := ey'

  have hker₂ : mR (X.X₂ ◁ Y.g) (i + 1) ((inhomogeneousChains.d (X.X₂ ⊗ Y.X₂) (i + 1)).hom m
      - mR (X.f ▷ Y.X₂) (i + 1) y') = 0 := by
    rw [map_sub, ← d_mR, hm, mR_exchange, hy', hy, sub_self]
  have ev' : ∃ v' : (Fin (i + 1) → G) →₀ (X.X₂ ⊗ Y.X₁ : Rep.{u} k G), mR (X.X₂ ◁ Y.f) (i + 1) v'
      = (inhomogeneousChains.d (X.X₂ ⊗ Y.X₂) (i + 1)).hom m - mR (X.f ▷ Y.X₂) (i + 1) y' :=
    exists_preimage hC₂ (i + 1) _ hker₂
  obtain ⟨v', hv'⟩ := ev'
  let v : (Fin (i + 1) → G) →₀ (X.X₃ ⊗ Y.X₁ : Rep.{u} k G) := mR (X.g ▷ Y.X₁) (i + 1) v'
  have hv : mR (X.X₃ ◁ Y.f) (i + 1) v = (inhomogeneousChains.d (X.X₃ ⊗ Y.X₂) (i + 1)).hom u := by
    show mR (X.X₃ ◁ Y.f) (i + 1) (mR (X.g ▷ Y.X₁) (i + 1) v') = (inhomogeneousChains.d (X.X₃ ⊗ Y.X₂) (i + 1)).hom
      (mR (X.g ▷ Y.X₂) (i + 2) m)
    rw [mR_exchange, hv', map_sub, d_mR,
      show mR (X.g ▷ Y.X₂) (i + 1) (mR (X.f ▷ Y.X₂) (i + 1) y') = 0 from by
        refine Finsupp.ext fun a => ?_
        rw [mR_apply, mR_apply]
        exact g_f_apply (X.map (tensorRight Y.X₂)) (y' a), sub_zero]
  have hdv : (inhomogeneousChains.d (X.X₃ ⊗ Y.X₁) i).hom v = 0 := by
    apply mR_injective hC₃ i
    show mR (X.X₃ ◁ Y.f) i _ = mR (X.X₃ ◁ Y.f) i 0
    rw [← d_mR, hv, d_d_apply, map_zero]

  have hker₁ : mR (X.X₁ ◁ Y.g) i ((inhomogeneousChains.d (X.X₁ ⊗ Y.X₂) i).hom y') = 0 := by
    rw [← d_mR, hy', hdy]
  have ez : ∃ z : (Fin i → G) →₀ (X.X₁ ⊗ Y.X₁ : Rep.{u} k G), mR (X.X₁ ◁ Y.f) i z
      = (inhomogeneousChains.d (X.X₁ ⊗ Y.X₂) i).hom y' := exists_preimage hC₁ i _ hker₁
  obtain ⟨z, hz⟩ := ez

  have hker₃ : mR (X.g ▷ Y.X₁) i ((inhomogeneousChains.d (X.X₂ ⊗ Y.X₁) i).hom v') = 0 := by
    rw [← d_mR]
    exact hdv
  have ew : ∃ w : (Fin i → G) →₀ (X.X₁ ⊗ Y.X₁ : Rep.{u} k G), mR (X.f ▷ Y.X₁) i w
      = (inhomogeneousChains.d (X.X₂ ⊗ Y.X₁) i).hom v' := exists_preimage hR₁ i _ hker₃
  obtain ⟨w, hw⟩ := ew

  have hzw : z + w = 0 := by
    apply mR_injective hC₁ i
    apply mR_injective hR₂ i
    show mR (X.f ▷ Y.X₂) i (mR (X.X₁ ◁ Y.f) i (z + w)) = mR (X.f ▷ Y.X₂) i (mR (X.X₁ ◁ Y.f) i 0)
    rw [map_add, map_add, map_zero, map_zero, hz, ← mR_exchange X.f Y.f, hw, ← d_mR, ← d_mR, hv',
      map_sub, add_sub_cancel, d_d_apply]

  have Hx : ((chainsMap (MonoidHom.id G) (X.map (tensorRight Y.X₃)).g).f (i + 2)).hom x
      = (iCycles (X.X₃ ⊗ Y.X₃) (i + 2)).hom c₀ := by
    rw [chainsMap_id_f_hom_eq_mapRange]; exact hx
  have Hy : mR (X.f ▷ Y.X₃) (i + 1) y = (inhomogeneousChains (X.map (tensorRight Y.X₃)).X₂).d (i + 2) (i + 1) x := by
    rw [inhomogeneousChains.d_def]; exact hy
  have Hdy : (inhomogeneousChains (Y.map (tensorLeft X.X₁)).X₃).d (i + 1) i y = 0 := by
    rw [inhomogeneousChains.d_def]; exact hdy
  have Hy' : ((chainsMap (MonoidHom.id G) (Y.map (tensorLeft X.X₁)).g).f (i + 1)).hom y' = y := by
    rw [chainsMap_id_f_hom_eq_mapRange]; exact hy'
  have Hz : mR (X.X₁ ◁ Y.f) i z = (inhomogeneousChains (Y.map (tensorLeft X.X₁)).X₂).d (i + 1) i y' := by
    rw [inhomogeneousChains.d_def]; exact hz
  have Hu : ((chainsMap (MonoidHom.id G) (Y.map (tensorLeft X.X₃)).g).f (i + 2)).hom u
      = (iCycles (X.X₃ ⊗ Y.X₃) (i + 2)).hom c₀ := by
    rw [chainsMap_id_f_hom_eq_mapRange]; exact hu
  have Hv : mR (X.X₃ ◁ Y.f) (i + 1) v = (inhomogeneousChains (Y.map (tensorLeft X.X₃)).X₂).d (i + 2) (i + 1) u := by
    rw [inhomogeneousChains.d_def]; exact hv
  have Hdv : (inhomogeneousChains (X.map (tensorRight Y.X₁)).X₃).d (i + 1) i v = 0 := by
    rw [inhomogeneousChains.d_def]; exact hdv
  have Hv' : ((chainsMap (MonoidHom.id G) (X.map (tensorRight Y.X₁)).g).f (i + 1)).hom v' = v := by
    rw [chainsMap_id_f_hom_eq_mapRange]
    rfl
  have Hw : mR (X.f ▷ Y.X₁) i w = (inhomogeneousChains (X.map (tensorRight Y.X₁)).X₂).d (i + 1) i v' := by
    rw [inhomogeneousChains.d_def]; exact hw
  have keyR : (groupHomology.δ hR₃ (i + 2) (i + 1) rfl).hom ((groupHomology.π (X.X₃ ⊗ Y.X₃) (i + 2)).hom
      (cyclesMk (i + 2) (i + 1) (by simp) ((iCycles _ (i + 2)).hom c₀) hc'))
      = (groupHomology.π (X.X₁ ⊗ Y.X₃) (i + 1)).hom (cyclesMkOfCompEqD hR₃ Hy) :=
    groupHomology.δ_apply hR₃ rfl _ hc' x Hx y Hy
  have keyC : (groupHomology.δ hC₁ (i + 1) i rfl).hom ((groupHomology.π (X.X₁ ⊗ Y.X₃) (i + 1)).hom
      (cyclesMkOfCompEqD hR₃ Hy))
      = (groupHomology.π (X.X₁ ⊗ Y.X₁) i).hom (cyclesMkOfCompEqD hC₁ Hz) :=
    groupHomology.δ_apply hC₁ rfl y Hdy y' Hy' z Hz
  have keyC' : (groupHomology.δ hC₃ (i + 2) (i + 1) rfl).hom ((groupHomology.π (X.X₃ ⊗ Y.X₃) (i + 2)).hom
      (cyclesMk (i + 2) (i + 1) (by simp) ((iCycles _ (i + 2)).hom c₀) hc'))
      = (groupHomology.π (X.X₃ ⊗ Y.X₁) (i + 1)).hom (cyclesMkOfCompEqD hC₃ Hv) :=
    groupHomology.δ_apply hC₃ rfl _ hc' u Hu v Hv
  have keyR' : (groupHomology.δ hR₁ (i + 1) i rfl).hom ((groupHomology.π (X.X₃ ⊗ Y.X₁) (i + 1)).hom
      (cyclesMkOfCompEqD hC₃ Hv))
      = (groupHomology.π (X.X₁ ⊗ Y.X₁) i).hom (cyclesMkOfCompEqD hR₁ Hw) :=
    groupHomology.δ_apply hR₁ rfl v Hdv v' Hv' w Hw

  have hcyc : ∀ (t : (Fin i → G) →₀ (X.X₁ ⊗ Y.X₁ : Rep.{u} k G)),
      (∀ (j : ℕ) (hj : j + 1 = i), (inhomogeneousChains (X.X₁ ⊗ Y.X₁)).d i j t = 0) →
      (inhomogeneousChains (X.X₁ ⊗ Y.X₁)).d i ((ComplexShape.down ℕ).next i) t = 0 := by
    intro t ht
    by_cases hij : (ComplexShape.down ℕ).next i + 1 = i
    · exact ht _ hij
    · rw [(inhomogeneousChains (X.X₁ ⊗ Y.X₁)).shape _ _ hij]
      rfl
  have hdz : (inhomogeneousChains (X.X₁ ⊗ Y.X₁)).d i ((ComplexShape.down ℕ).next i) z = 0 := by
    refine hcyc z fun j hj => ?_
    subst hj
    rw [inhomogeneousChains.d_def]
    apply mR_injective hC₁ j
    show mR (X.X₁ ◁ Y.f) j _ = mR (X.X₁ ◁ Y.f) j 0
    rw [← d_mR, hz, d_d_apply, map_zero]
  have hdw : (inhomogeneousChains (X.X₁ ⊗ Y.X₁)).d i ((ComplexShape.down ℕ).next i) w = 0 := by
    refine hcyc w fun j hj => ?_
    subst hj
    rw [inhomogeneousChains.d_def]
    apply mR_injective hR₁ j
    show mR (X.f ▷ Y.X₁) j _ = mR (X.f ▷ Y.X₁) j 0
    rw [← d_mR, hw, d_d_apply, map_zero]
  have e : cyclesMk (A := X.X₁ ⊗ Y.X₁) i _ rfl z hdz + cyclesMk (A := X.X₁ ⊗ Y.X₁) i _ rfl w hdw = 0 :=
    iCycles_injective (X.X₁ ⊗ Y.X₁) i (by
      rw [map_add, map_zero, i_cyclesMk, i_cyclesMk]
      exact hzw)
  rw [hπ, keyR, keyC, keyC', keyR']
  show (groupHomology.π (X.X₁ ⊗ Y.X₁) i).hom (cyclesMk (A := X.X₁ ⊗ Y.X₁) i _ rfl z hdz)
    = -((groupHomology.π (X.X₁ ⊗ Y.X₁) i).hom (cyclesMk (A := X.X₁ ⊗ Y.X₁) i _ rfl w hdw))
  rw [eq_neg_of_add_eq_zero_left e, map_neg]

end P2mS26AH

namespace P2mS26AS
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

variable [Fintype G]

theorem seam_neg1 {X Y : ShortComplex (Rep.{u} k G)}
    (hR₁ : (X.map (tensorRight Y.X₁)).ShortExact) (hR₂ : (X.map (tensorRight Y.X₂)).ShortExact)
    (hR₃ : (X.map (tensorRight Y.X₃)).ShortExact) (hC₁ : (Y.map (tensorLeft X.X₁)).ShortExact)
    (hC₂ : (Y.map (tensorLeft X.X₂)).ShortExact) (hC₃ : (Y.map (tensorLeft X.X₃)).ShortExact)
    (c : (X.X₃ ⊗ Y.X₃ : Rep.{u} k G).tateHneg1) :
    Rep.tateδ₀ hC₁ (Rep.tateδneg1 hR₃ c) = -(Rep.tateδ₀ hR₁ (Rep.tateδneg1 hC₃ c)) := by

  obtain ⟨c₁, hc₁⟩ := Submodule.Quotient.mk_surjective _ (c : (X.X₃ ⊗ Y.X₃ : Rep.{u} k G).ρ.Coinvariants)
  have hN : (X.X₃ ⊗ Y.X₃ : Rep.{u} k G).ρ.norm c₁ = 0 := by
    have h2 := c.2
    rw [LinearMap.mem_ker, ← hc₁] at h2
    exact congrArg Subtype.val h2
  have ex₂ : ∃ x₂ : (X.X₂ ⊗ Y.X₃ : Rep.{u} k G), (X.g ▷ Y.X₃).hom x₂ = c₁ := g_surjective hR₃ c₁
  obtain ⟨x₂, hx₂⟩ := ex₂
  have em : ∃ m : (X.X₂ ⊗ Y.X₂ : Rep.{u} k G), (X.X₂ ◁ Y.g).hom m = x₂ := g_surjective hC₂ x₂
  obtain ⟨m, hm⟩ := em

  have hb : (X.X₃ ⊗ Y.X₃ : Rep.{u} k G).ρ.norm ((X.g ▷ Y.X₃).hom ((X.X₂ ◁ Y.g).hom m)) = 0 := by
    rw [hm, hx₂, hN]
  have hb' : (X.X₃ ⊗ Y.X₃ : Rep.{u} k G).ρ.norm ((X.X₃ ◁ Y.g).hom ((X.g ▷ Y.X₂).hom m)) = 0 := by
    rw [exchange, hm, hx₂, hN]
  have hcR : c = Rep.seamθ (X.map (tensorRight Y.X₃)) ⟨(X.X₂ ◁ Y.g).hom m, hb⟩ := by
    apply Subtype.ext
    rw [Rep.coe_seamθ_apply, ← hc₁]
    show _ = Representation.Coinvariants.mk _ ((X.g ▷ Y.X₃).hom ((X.X₂ ◁ Y.g).hom m))
    rw [hm, hx₂]
    rfl
  have hcC : c = Rep.seamθ (Y.map (tensorLeft X.X₃)) ⟨(X.g ▷ Y.X₂).hom m, hb'⟩ := by
    apply Subtype.ext
    rw [Rep.coe_seamθ_apply, ← hc₁]
    show _ = Representation.Coinvariants.mk _ ((X.X₃ ◁ Y.g).hom ((X.g ▷ Y.X₂).hom m))
    rw [exchange, hm, hx₂]
    rfl

  have hNm : ∀ h : G, (X.X₂ ⊗ Y.X₂ : Rep.{u} k G).ρ h ((X.X₂ ⊗ Y.X₂ : Rep.{u} k G).ρ.norm m)
      = (X.X₂ ⊗ Y.X₂ : Rep.{u} k G).ρ.norm m := fun h =>
    (Representation.mem_invariants _ _).1 (Representation.norm_apply_mem_invariants _ _) h

  let aR : (X.X₁ ⊗ Y.X₃ : Rep.{u} k G).ρ.invariants :=
    ⟨Rep.seamψ hR₃ ⟨(X.X₂ ◁ Y.g).hom m, hb⟩, Rep.seamψ_mem_invariants hR₃ _⟩
  have haR : (X.f ▷ Y.X₃).hom (aR : (X.X₁ ⊗ Y.X₃ : Rep.{u} k G))
      = (X.X₂ ⊗ Y.X₃ : Rep.{u} k G).ρ.norm ((X.X₂ ◁ Y.g).hom m) := Rep.f_seamψ hR₃ _

  have ey : ∃ y : (X.X₁ ⊗ Y.X₂ : Rep.{u} k G), (X.X₁ ◁ Y.g).hom y = aR :=
    g_surjective hC₁ (aR : (X.X₁ ⊗ Y.X₃ : Rep.{u} k G))
  obtain ⟨y, hy⟩ := ey

  have hker : (X.X₂ ◁ Y.g).hom ((X.X₂ ⊗ Y.X₂ : Rep.{u} k G).ρ.norm m - (X.f ▷ Y.X₂).hom y) = 0 := by
    rw [map_sub, Rep.hom_norm_apply, exchange, hy, haR, sub_self]
  have ey₂ : ∃ y₂ : (X.X₂ ⊗ Y.X₁ : Rep.{u} k G), (X.X₂ ◁ Y.f).hom y₂
      = (X.X₂ ⊗ Y.X₂ : Rep.{u} k G).ρ.norm m - (X.f ▷ Y.X₂).hom y := exists_preimage hC₂ _ hker
  obtain ⟨y₂, hy₂⟩ := ey₂

  have ha'eq : (X.X₃ ◁ Y.f).hom ((X.g ▷ Y.X₁).hom y₂)
      = (X.X₃ ⊗ Y.X₂ : Rep.{u} k G).ρ.norm ((X.g ▷ Y.X₂).hom m) := by
    rw [exchange, hy₂, map_sub, Rep.hom_norm_apply,
      show (X.g ▷ Y.X₂).hom ((X.f ▷ Y.X₂).hom y) = 0 from g_f_apply (X.map (tensorRight Y.X₂)) y, sub_zero]
  have ha'inv : (X.g ▷ Y.X₁).hom y₂ ∈ (X.X₃ ⊗ Y.X₁ : Rep.{u} k G).ρ.invariants := by
    rw [Representation.mem_invariants]
    intro h
    apply f_injective hC₃
    show (X.X₃ ◁ Y.f).hom _ = (X.X₃ ◁ Y.f).hom _
    rw [Rep.hom_comm_apply, ha'eq]
    exact (Representation.mem_invariants _ _).1 (Representation.norm_apply_mem_invariants _ _) h
  let aC : (X.X₃ ⊗ Y.X₁ : Rep.{u} k G).ρ.invariants := ⟨(X.g ▷ Y.X₁).hom y₂, ha'inv⟩

  have h1R : Rep.tateδneg1 hR₃ c = Submodule.Quotient.mk aR := by
    rw [hcR]
    exact Rep.tateδneg1_mk hR₃ _ hb aR haR
  have h1C : Rep.tateδneg1 hC₃ c = Submodule.Quotient.mk aC := by
    rw [hcC]
    exact Rep.tateδneg1_mk hC₃ _ hb' aC ha'eq

  have ex : ∀ h : G, ∃ t : (X.X₁ ⊗ Y.X₁ : Rep.{u} k G), (X.X₁ ◁ Y.f).hom t
      = (X.X₁ ⊗ Y.X₂ : Rep.{u} k G).ρ h y - y := fun h => exists_preimage hC₁ _ (by
    show (X.X₁ ◁ Y.g).hom ((X.X₁ ⊗ Y.X₂ : Rep.{u} k G).ρ h y - y) = 0
    rw [map_sub, Rep.hom_comm_apply, hy, sub_eq_zero]
    exact (Representation.mem_invariants _ _).1 aR.2 h)
  choose x hx using ex
  have ex' : ∀ h : G, ∃ t : (X.X₁ ⊗ Y.X₁ : Rep.{u} k G), (X.f ▷ Y.X₁).hom t
      = (X.X₂ ⊗ Y.X₁ : Rep.{u} k G).ρ h y₂ - y₂ := fun h => exists_preimage hR₁ _ (by
    show (X.g ▷ Y.X₁).hom ((X.X₂ ⊗ Y.X₁ : Rep.{u} k G).ρ h y₂ - y₂) = 0
    rw [map_sub, Rep.hom_comm_apply, sub_eq_zero]
    exact (Representation.mem_invariants _ _).1 ha'inv h)
  choose x' hx' using ex'

  have hxx : ∀ h, x h + x' h = 0 := fun h => by
    apply f_injective hC₁
    apply f_injective hR₂
    show (X.f ▷ Y.X₂).hom ((X.X₁ ◁ Y.f).hom (x h + x' h)) = (X.f ▷ Y.X₂).hom ((X.X₁ ◁ Y.f).hom 0)
    rw [map_add, map_add, hx h, ← exchange X.f Y.f (x' h), hx' h, map_sub, map_sub, Rep.hom_comm_apply,
      Rep.hom_comm_apply (X.X₂ ◁ Y.f), hy₂, map_zero, map_zero, map_sub, hNm h]
    abel

  have hL : Rep.tateδ₀ hC₁ (Rep.tateδneg1 hR₃ c)
      = groupCohomology.H1π (X.X₁ ⊗ Y.X₁) ⟨x, groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ hC₁ (funext hx)⟩ := by
    rw [h1R]
    exact groupCohomology.δ₀_apply hC₁ aR y hy x (funext hx)
  have hR' : Rep.tateδ₀ hR₁ (Rep.tateδneg1 hC₃ c)
      = groupCohomology.H1π (X.X₁ ⊗ Y.X₁) ⟨x', groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ hR₁ (funext hx')⟩ := by
    rw [h1C]
    exact groupCohomology.δ₀_apply hR₁ aC y₂ rfl x' (funext hx')
  rw [hL, hR']
  have e : (⟨x, groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ hC₁ (funext hx)⟩ : groupCohomology.cocycles₁ (X.X₁ ⊗ Y.X₁))
      = -⟨x', groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ hR₁ (funext hx')⟩ :=
    Subtype.ext (funext fun h => eq_neg_of_add_eq_zero_left (hxx h))
  exact (congrArg (groupCohomology.H1π (X.X₁ ⊗ Y.X₁)).hom e).trans (map_neg _ _)

end P2mS26AS

namespace P2mS26AS
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

theorem seam_neg2 {X Y : ShortComplex (Rep.{u} k G)}
    (hR₁ : (X.map (tensorRight Y.X₁)).ShortExact) (hR₂ : (X.map (tensorRight Y.X₂)).ShortExact)
    (hR₃ : (X.map (tensorRight Y.X₃)).ShortExact) (hC₁ : (Y.map (tensorLeft X.X₁)).ShortExact)
    (hC₂ : (Y.map (tensorLeft X.X₂)).ShortExact) (hC₃ : (Y.map (tensorLeft X.X₃)).ShortExact)
    (c : groupHomology (X.X₃ ⊗ Y.X₃) 1) :
    Rep.tateδneg1 hC₁ (Rep.tateδneg2 hR₃ c) = -(Rep.tateδneg1 hR₁ (Rep.tateδneg2 hC₃ c)) := by
  induction c using groupHomology.H1_induction_on with
  | h γ =>

  obtain ⟨ν, hν0⟩ := Finsupp.mapRange_surjective _ (map_zero (X.g ▷ Y.X₃).hom.toLinearMap) (g_surjective hR₃) γ.1
  obtain ⟨μ, hμ0⟩ := Finsupp.mapRange_surjective _ (map_zero (X.X₂ ◁ Y.g).hom.toLinearMap) (g_surjective hC₂) ν
  have hν : mapRange.linearMap (X.g ▷ Y.X₃).hom.toLinearMap (mapRange.linearMap (X.X₂ ◁ Y.g).hom.toLinearMap μ)
      = γ.1 := by
    rw [mapRange.linearMap_apply, mapRange.linearMap_apply, hμ0, hν0]
  have hν' : mapRange.linearMap (X.X₃ ◁ Y.g).hom.toLinearMap (mapRange.linearMap (X.g ▷ Y.X₂).hom.toLinearMap μ)
      = γ.1 := by
    rw [← hν]
    refine Finsupp.ext fun a => ?_
    simp only [mapRange.linearMap_apply, mapRange_apply]
    exact exchange X.g Y.g (μ a)

  let dμ : (X.X₂ ⊗ Y.X₂ : Rep.{u} k G) := (d₁₀ (X.X₂ ⊗ Y.X₂)).hom μ
  have hgd : (X.g ▷ Y.X₃).hom ((X.X₂ ◁ Y.g).hom dμ) = 0 := by
    show (X.g ▷ Y.X₃).hom ((X.X₂ ◁ Y.g).hom ((d₁₀ (X.X₂ ⊗ Y.X₂)).hom μ)) = 0
    rw [← d₁₀_mapRange (X.X₂ ◁ Y.g), ← d₁₀_mapRange (X.g ▷ Y.X₃), hν]
    exact γ.2

  obtain ⟨t, ht0⟩ := exists_preimage hR₃ _ hgd
  have ht : (X.f ▷ Y.X₃).hom t = (X.X₂ ◁ Y.g).hom dμ := ht0
  obtain ⟨b₀, hb₀0⟩ := g_surjective hC₁ t
  have hb₀ : (X.X₁ ◁ Y.g).hom b₀ = t := hb₀0
  have hker : (X.X₂ ◁ Y.g).hom (dμ - (X.f ▷ Y.X₂).hom b₀) = 0 := by
    rw [map_sub, exchange, hb₀, ht, sub_self]
  obtain ⟨b₂, hb₂0⟩ := exists_preimage hC₂ _ hker
  have hb₂ : (X.X₂ ◁ Y.f).hom b₂ = dμ - (X.f ▷ Y.X₂).hom b₀ := hb₂0
  have ht' : (X.X₃ ◁ Y.f).hom ((X.g ▷ Y.X₁).hom b₂)
      = (X.g ▷ Y.X₂).hom dμ := by
    rw [exchange, hb₂, map_sub, show (X.g ▷ Y.X₂).hom ((X.f ▷ Y.X₂).hom b₀) = 0 from
      g_f_apply (X.map (tensorRight Y.X₂)) b₀, sub_zero]

  have hδR : (groupHomology.δ hR₃ 1 0 rfl).hom ((groupHomology.H1π (X.X₃ ⊗ Y.X₃)).hom γ)
      = (groupHomology.H0π (X.X₁ ⊗ Y.X₃)).hom t :=
    groupHomology.δ₀_apply hR₃ γ (mapRange.linearMap (X.X₂ ◁ Y.g).hom.toLinearMap μ) hν t
      (by
        show (X.f ▷ Y.X₃).hom t = (d₁₀ (X.X₂ ⊗ Y.X₃)).hom (mapRange.linearMap (X.X₂ ◁ Y.g).hom.toLinearMap μ)
        rw [ht, d₁₀_mapRange])
  have hδC : (groupHomology.δ hC₃ 1 0 rfl).hom ((groupHomology.H1π (X.X₃ ⊗ Y.X₃)).hom γ)
      = (groupHomology.H0π (X.X₃ ⊗ Y.X₁)).hom ((X.g ▷ Y.X₁).hom b₂) :=
    groupHomology.δ₀_apply hC₃ γ (mapRange.linearMap (X.g ▷ Y.X₂).hom.toLinearMap μ) hν' _
      (by
        show (X.X₃ ◁ Y.f).hom ((X.g ▷ Y.X₁).hom b₂)
          = (d₁₀ (X.X₃ ⊗ Y.X₂)).hom (mapRange.linearMap (X.g ▷ Y.X₂).hom.toLinearMap μ)
        rw [ht', d₁₀_mapRange])

  have hsR : (Rep.tateδneg2 hR₃ ((groupHomology.H1π (X.X₃ ⊗ Y.X₃)).hom γ)).1
      = Representation.Coinvariants.mk _ t := by
    rw [Rep.coe_tateδneg2_apply]
    show (groupHomology.H0Iso (X.X₁ ⊗ Y.X₃)).hom.hom ((groupHomology.δ hR₃ 1 0 rfl).hom _) = _
    rw [hδR]
    exact groupHomology.H0π_comp_H0Iso_hom_apply _ _
  have hsC : (Rep.tateδneg2 hC₃ ((groupHomology.H1π (X.X₃ ⊗ Y.X₃)).hom γ)).1
      = Representation.Coinvariants.mk _ ((X.g ▷ Y.X₁).hom b₂) := by
    rw [Rep.coe_tateδneg2_apply]
    show (groupHomology.H0Iso (X.X₃ ⊗ Y.X₁)).hom.hom ((groupHomology.δ hC₃ 1 0 rfl).hom _) = _
    rw [hδC]
    exact groupHomology.H0π_comp_H0Iso_hom_apply _ _

  have hNb₀ : (X.X₁ ⊗ Y.X₃ : Rep.{u} k G).ρ.norm ((X.X₁ ◁ Y.g).hom b₀) = 0 := by
    have h2 := (Rep.tateδneg2 hR₃ ((groupHomology.H1π (X.X₃ ⊗ Y.X₃)).hom γ)).2
    rw [LinearMap.mem_ker, hsR] at h2
    rw [hb₀]
    exact congrArg Subtype.val h2
  have hNb₂ : (X.X₃ ⊗ Y.X₁ : Rep.{u} k G).ρ.norm ((X.g ▷ Y.X₁).hom b₂) = 0 := by
    have h2 := (Rep.tateδneg2 hC₃ ((groupHomology.H1π (X.X₃ ⊗ Y.X₃)).hom γ)).2
    rw [LinearMap.mem_ker, hsC] at h2
    exact congrArg Subtype.val h2
  have hθR : Rep.tateδneg2 hR₃ ((groupHomology.H1π (X.X₃ ⊗ Y.X₃)).hom γ)
      = Rep.seamθ (Y.map (tensorLeft X.X₁)) ⟨b₀, hNb₀⟩ := by
    apply Subtype.ext
    rw [hsR, Rep.coe_seamθ_apply]
    show _ = Representation.Coinvariants.mk _ ((X.X₁ ◁ Y.g).hom b₀)
    rw [hb₀]
    rfl
  have hθC : Rep.tateδneg2 hC₃ ((groupHomology.H1π (X.X₃ ⊗ Y.X₃)).hom γ)
      = Rep.seamθ (X.map (tensorRight Y.X₁)) ⟨b₂, hNb₂⟩ := by
    apply Subtype.ext
    rw [hsC, Rep.coe_seamθ_apply]
    rfl

  let aR : (X.X₁ ⊗ Y.X₁ : Rep.{u} k G).ρ.invariants :=
    ⟨Rep.seamψ hC₁ ⟨b₀, hNb₀⟩, Rep.seamψ_mem_invariants hC₁ _⟩
  have haR : (X.X₁ ◁ Y.f).hom (aR : (X.X₁ ⊗ Y.X₁ : Rep.{u} k G)) = (X.X₁ ⊗ Y.X₂ : Rep.{u} k G).ρ.norm b₀ :=
    Rep.f_seamψ hC₁ _
  let aC : (X.X₁ ⊗ Y.X₁ : Rep.{u} k G).ρ.invariants :=
    ⟨Rep.seamψ hR₁ ⟨b₂, hNb₂⟩, Rep.seamψ_mem_invariants hR₁ _⟩
  have haC : (X.f ▷ Y.X₁).hom (aC : (X.X₁ ⊗ Y.X₁ : Rep.{u} k G)) = (X.X₂ ⊗ Y.X₁ : Rep.{u} k G).ρ.norm b₂ :=
    Rep.f_seamψ hR₁ _
  have h1R : Rep.tateδneg1 hC₁ (Rep.tateδneg2 hR₃ ((groupHomology.H1π (X.X₃ ⊗ Y.X₃)).hom γ))
      = Submodule.Quotient.mk aR := by
    rw [hθR]
    exact Rep.tateδneg1_mk hC₁ b₀ hNb₀ aR haR
  have h1C : Rep.tateδneg1 hR₁ (Rep.tateδneg2 hC₃ ((groupHomology.H1π (X.X₃ ⊗ Y.X₃)).hom γ))
      = Submodule.Quotient.mk aC := by
    rw [hθC]
    exact Rep.tateδneg1_mk hR₁ b₂ hNb₂ aC haC

  have haa : (aR : (X.X₁ ⊗ Y.X₁ : Rep.{u} k G)) + aC = 0 := by
    apply f_injective hC₁
    apply f_injective hR₂
    show (X.f ▷ Y.X₂).hom ((X.X₁ ◁ Y.f).hom ((aR : (X.X₁ ⊗ Y.X₁ : Rep.{u} k G)) + aC))
      = (X.f ▷ Y.X₂).hom ((X.X₁ ◁ Y.f).hom 0)
    rw [map_add, map_add, haR, ← exchange X.f Y.f, haC, Rep.hom_norm_apply, Rep.hom_norm_apply, hb₂,
      ← map_add, add_sub_cancel, norm_d₁₀, map_zero, map_zero]
  show Rep.tateδneg1 hC₁ (Rep.tateδneg2 hR₃ ((groupHomology.H1π (X.X₃ ⊗ Y.X₃)).hom γ))
    = -(Rep.tateδneg1 hR₁ (Rep.tateδneg2 hC₃ ((groupHomology.H1π (X.X₃ ⊗ Y.X₃)).hom γ)))
  rw [h1R, h1C]
  have e : aR = -aC := Subtype.ext (eq_neg_of_add_eq_zero_left haa)
  exact (congrArg (Submodule.Quotient.mk (p := LinearMap.range (X.X₁ ⊗ Y.X₁ : Rep.{u} k G).ρ.normBar)) e).trans
    (Submodule.Quotient.mk_neg _)

end P2mS26AS

namespace P2mS26AG

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] {X Y : ShortComplex (Rep.{u} k G)}
  (hR₁ : (X.map (MonoidalCategory.tensorRight Y.X₁)).ShortExact)
  (hR₂ : (X.map (MonoidalCategory.tensorRight Y.X₂)).ShortExact)
  (hR₃ : (X.map (MonoidalCategory.tensorRight Y.X₃)).ShortExact)
  (hC₁ : (Y.map (MonoidalCategory.tensorLeft X.X₁)).ShortExact)
  (hC₂ : (Y.map (MonoidalCategory.tensorLeft X.X₂)).ShortExact)
  (hC₃ : (Y.map (MonoidalCategory.tensorLeft X.X₃)).ShortExact)
include hR₁ hR₂ hR₃ hC₁ hC₂ hC₃

theorem regime_pos (m : ℕ) :
    Rep.tateδ hR₃ (Int.ofNat (m + 1)) ≫ Rep.tateδ hC₁ (Int.ofNat (m + 1) + 1)
      = -(Rep.tateδ hC₃ (Int.ofNat (m + 1)) ≫ Rep.tateδ hR₁ (Int.ofNat (m + 1) + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact P2mS26AC.coh_chase hR₁ hR₂ hR₃ hC₁ hC₂ hC₃ (m + 1) c

theorem regime_zero :
    Rep.tateδ hR₃ (Int.ofNat 0) ≫ Rep.tateδ hC₁ (Int.ofNat 0 + 1)
      = -(Rep.tateδ hC₃ (Int.ofNat 0) ≫ Rep.tateδ hR₁ (Int.ofNat 0 + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact P2mS26AC.coh_chase hR₁ hR₂ hR₃ hC₁ hC₂ hC₃ 0 (((groupCohomology.H0Iso (X.X₃ ⊗ Y.X₃)).inv).hom z)

theorem regime_neg_one :
    Rep.tateδ hR₃ (Int.negSucc 0) ≫ Rep.tateδ hC₁ (Int.negSucc 0 + 1)
      = -(Rep.tateδ hC₃ (Int.negSucc 0) ≫ Rep.tateδ hR₁ (Int.negSucc 0 + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact P2mS26AS.seam_neg1 hR₁ hR₂ hR₃ hC₁ hC₂ hC₃ c

theorem regime_neg_two :
    Rep.tateδ hR₃ (Int.negSucc 1) ≫ Rep.tateδ hC₁ (Int.negSucc 1 + 1)
      = -(Rep.tateδ hC₃ (Int.negSucc 1) ≫ Rep.tateδ hR₁ (Int.negSucc 1 + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact P2mS26AS.seam_neg2 hR₁ hR₂ hR₃ hC₁ hC₂ hC₃ c

theorem regime_neg_three :
    Rep.tateδ hR₃ (Int.negSucc 2) ≫ Rep.tateδ hC₁ (Int.negSucc 2 + 1)
      = -(Rep.tateδ hC₃ (Int.negSucc 2) ≫ Rep.tateδ hR₁ (Int.negSucc 2 + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have h2 : (groupHomology.δ hC₁ 1 0 rfl).hom ((groupHomology.δ hR₃ 2 1 rfl).hom c)
      = -((groupHomology.δ hR₁ 1 0 rfl).hom ((groupHomology.δ hC₃ 2 1 rfl).hom c)) :=
    P2mS26AH.hom_chase hR₁ hR₂ hR₃ hC₁ hC₂ hC₃ 0 c
  change Rep.tateδneg2 hC₁ ((groupHomology.δ hR₃ 2 1 rfl).hom c)
    = -(Rep.tateδneg2 hR₁ ((groupHomology.δ hC₃ 2 1 rfl).hom c))
  apply Subtype.ext
  rw [Submodule.coe_neg, Rep.coe_tateδneg2_apply, Rep.coe_tateδneg2_apply]
  change ((groupHomology.H0Iso (X.X₁ ⊗ Y.X₁)).hom).hom ((groupHomology.δ hC₁ 1 0 rfl).hom
      ((groupHomology.δ hR₃ 2 1 rfl).hom c))
    = -(((groupHomology.H0Iso (X.X₁ ⊗ Y.X₁)).hom).hom ((groupHomology.δ hR₁ 1 0 rfl).hom
      ((groupHomology.δ hC₃ 2 1 rfl).hom c)))
  rw [h2]
  exact map_neg ((groupHomology.H0Iso (X.X₁ ⊗ Y.X₁)).hom).hom _

theorem regime_neg (m : ℕ) :
    Rep.tateδ hR₃ (Int.negSucc (m + 3)) ≫ Rep.tateδ hC₁ (Int.negSucc (m + 3) + 1)
      = -(Rep.tateδ hC₃ (Int.negSucc (m + 3)) ≫ Rep.tateδ hR₁ (Int.negSucc (m + 3) + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact P2mS26AH.hom_chase hR₁ hR₂ hR₃ hC₁ hC₂ hC₃ (m + 1) c

end P2mS26AG

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X Y : ShortComplex (Rep.{u} k G)}
    (hR₁ : (X.map (MonoidalCategory.tensorRight Y.X₁)).ShortExact)
    (hR₂ : (X.map (MonoidalCategory.tensorRight Y.X₂)).ShortExact)
    (hR₃ : (X.map (MonoidalCategory.tensorRight Y.X₃)).ShortExact)
    (hC₁ : (Y.map (MonoidalCategory.tensorLeft X.X₁)).ShortExact)
    (hC₂ : (Y.map (MonoidalCategory.tensorLeft X.X₂)).ShortExact)
    (hC₃ : (Y.map (MonoidalCategory.tensorLeft X.X₃)).ShortExact) (n : ℤ) :
    Rep.tateδ hR₃ n ≫ Rep.tateδ hC₁ (n + 1) = -(Rep.tateδ hC₃ n ≫ Rep.tateδ hR₁ (n + 1)) := by
  match n with
  | Int.ofNat (m + 1) => exact P2mS26AG.regime_pos hR₁ hR₂ hR₃ hC₁ hC₂ hC₃ m
  | Int.ofNat 0 => exact P2mS26AG.regime_zero hR₁ hR₂ hR₃ hC₁ hC₂ hC₃
  | Int.negSucc 0 => exact P2mS26AG.regime_neg_one hR₁ hR₂ hR₃ hC₁ hC₂ hC₃
  | Int.negSucc 1 => exact P2mS26AG.regime_neg_two hR₁ hR₂ hR₃ hC₁ hC₂ hC₃
  | Int.negSucc 2 => exact P2mS26AG.regime_neg_three hR₁ hR₂ hR₃ hC₁ hC₂ hC₃
  | Int.negSucc (m + 3) => exact P2mS26AG.regime_neg hR₁ hR₂ hR₃ hC₁ hC₂ hC₃ m

end S_Rep_tateDelta_comp_tateDelta_eq_neg
end P2MW
export P2MW.S_Rep_tateDelta_comp_tateDelta_eq_neg (solution)
