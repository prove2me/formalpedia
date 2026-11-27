-- Prove2me | solution 1 for PositivityTheory.ThKF0.Geo.exists_lag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:29.429286+00:00
-- url     : https://prove2.me/submissions/0f671295-da46-4b8f-9e95-21aa30433ceb

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_GeoAlg
import Theorems.Thm_PositivityTheory_ThKF0_Geo_om_apply
import Theorems.Thm_PositivityTheory_ThKF0_Geo_eq_zero_of_om
import Theorems.Thm_PositivityTheory_ThKF0_Geo_om_refl
import Theorems.Thm_PositivityTheory_ThKF0_Geo_emb_apply
import Theorems.Thm_PositivityTheory_ThKF0_Geo_emb_form
import Theorems.Thm_PositivityTheory_ThKF0_Geo_exists_coord
import Theorems.Thm_PositivityTheory_ThKF0_Geo_schr_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM Module
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Geo
variable {F : Type} [Field F] {A : Type} [CommRing A] [Algebra F A]
variable {VA : Type} [AddCommGroup VA] [Module A VA] [Module F VA] [IsScalarTower F A VA] {BA : VA → VA → A}
  {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module F V]
variable {VB : Type} [AddCommGroup VB] [Module A VB] [Module F VB] [IsScalarTower F A VB] {BB : VB → VB → A}
  {κ₁ : Type} [Fintype κ₁] {V₁ : Type} [AddCommGroup V₁] [Module F V₁] {U : Type} [AddCommGroup U] [Module F U]
namespace PositivityTheory.ThKF0.Geo
theorem _root_.solution [Invertible (2 : A)] [FiniteDimensional F V₁] [FiniteDimensional F U]
    (hA : Function.Injective (algebraMap F A)) (co : Darboux BA κ) (inc : V →ₗ[F] VA) (hinc : Function.Injective inc)
    (hr : ∀ x, ∃ w, co.e (inc x) = emb (F := F) A κ w)
    (co₁ : Darboux BB κ₁) (inc₁ : V₁ →ₗ[F] VB) (hinc₁ : Function.Injective inc₁)
    (hr₁ : ∀ x, ∃ w, co₁.e (inc₁ x) = emb (F := F) A κ₁ w) (hd₁ : finrank F V₁ = 2 * Fintype.card κ₁)
    (j : V₁ →ₗ[F] V) (jA : VB →ₗ[A] VA) (hj : ∀ z, inc (j z) = jA (inc₁ z)) (hB : ∀ z z', BA (jA z) (jA z') = BB z z')
    (s : U →ₗ[F] V) (hs : Function.Injective s) (hss : ∀ u u', BA (inc (s u)) (inc (s u')) = 0)
    (hjs : ∀ z u, BA (jA z) (inc (s u)) = 0) (hd : finrank F U + Fintype.card κ₁ = Fintype.card κ) :
    ∃ L : Submodule F ((κ → F) × (κ → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧ finrank F L = Fintype.card κ ∧
      ∀ (t : A), ∀ w ∈ L, ∃ (u : U) (z : VB), (co₁.e z).1 = 0 ∧ ∀ (ψ : AddChar A ℂ) (φ : (κ → A) → ℂ),
        schr ψ (t • emb A κ w) φ = co.rho ψ (t • inc (s u)) (co.rho ψ (jA z) φ) := by
  classical
  obtain ⟨r, hr'⟩ := exists_coord hA co inc hr
  obtain ⟨r₁, hr₁'⟩ := exists_coord hA co₁ inc₁ hr₁
  have hBx : ∀ x y, BA (inc x) (inc y) = algebraMap F A (om F κ (r x) (r y)) := fun x y => by
    rw [co.form, hr', hr', emb_form]
  have hBz : ∀ z z', BB (inc₁ z) (inc₁ z') = algebraMap F A (om F κ₁ (r₁ z) (r₁ z')) := fun z z' => by
    rw [co₁.form, hr₁', hr₁', emb_form]
  have hBA0 : ∀ w, BA w 0 = 0 := fun w => by
    rw [co.form]
    simp
  have hrinj : Function.Injective r := by
    intro a b hab
    apply hinc
    apply co.e.injective
    rw [hr', hr', hab]
  have hr₁inj : Function.Injective r₁ := by
    intro a b hab
    apply hinc₁
    apply co₁.e.injective
    rw [hr₁', hr₁', hab]
  have hr₁surj : Function.Surjective r₁ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := r₁) ?_).mp hr₁inj
    rw [hd₁, Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
    ring
  let L₁ : Submodule F V₁ := LinearMap.ker ((LinearMap.fst F (κ₁ → F) (κ₁ → F)).comp r₁)
  have hL₁ : ∀ z, z ∈ L₁ ↔ (r₁ z).1 = 0 := fun z => by
    simp [L₁]
  have hfinL₁ : finrank F L₁ = Fintype.card κ₁ := by
    have hsurj : Function.Surjective ((LinearMap.fst F (κ₁ → F) (κ₁ → F)).comp r₁) := fun v => by
      obtain ⟨x, hx⟩ := hr₁surj (v, 0)
      exact ⟨x, by simp [hx]⟩
    have hrn := LinearMap.finrank_range_add_finrank_ker ((LinearMap.fst F (κ₁ → F) (κ₁ → F)).comp r₁)
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, hd₁] at hrn
    have e : finrank F L₁ =
        finrank F (LinearMap.ker ((LinearMap.fst F (κ₁ → F) (κ₁ → F)).comp r₁)) := rfl
    omega
  have hjinj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).mpr fun z hz => ?_
    apply hr₁inj
    rw [map_zero]
    apply eq_zero_of_om
    intro v
    obtain ⟨z', rfl⟩ := hr₁surj v
    apply hA
    rw [← hBz, ← hB, ← hj, ← hj, hz]
    simp [hBA0]
  have hdisj : LinearMap.range s ⊓ L₁.map j = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hx1
    obtain ⟨z, hz, hzs⟩ := Submodule.mem_map.mp hx2
    rw [Submodule.mem_bot]
    have hz0 : z = 0 := by
      apply hr₁inj
      rw [map_zero]
      apply eq_zero_of_om
      intro v
      obtain ⟨z', rfl⟩ := hr₁surj v
      apply hA
      rw [← hBz, ← hB, ← hj z, hzs, hjs, map_zero]
    rw [← hzs, hz0, map_zero]
  let L' : Submodule F V := LinearMap.range s ⊔ L₁.map j
  have hfinL' : finrank F L' = Fintype.card κ := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range s) (L₁.map j)
    rw [hdisj, finrank_bot, add_zero, LinearMap.finrank_range_of_inj hs,
      ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective j hjinj L₁), hfinL₁] at h1
    rw [← hd]
    exact h1
  have T1 : ∀ u u', om F κ (r (s u)) (r (s u')) = 0 := fun u u' => hA (by
    rw [← hBx, hss, map_zero])
  have T2 : ∀ z u, om F κ (r (j z)) (r (s u)) = 0 := fun z u => hA (by
    rw [← hBx, hj, hjs, map_zero])
  have T3 : ∀ u z, om F κ (r (s u)) (r (j z)) = 0 := fun u z => om_refl _ _ (T2 z u)
  have T4 : ∀ z z', z ∈ L₁ → z' ∈ L₁ → om F κ (r (j z)) (r (j z')) = 0 := fun z z' hz hz' => hA (by
    rw [← hBx, hj, hj, hB, hBz, om_apply, (hL₁ z).mp hz, (hL₁ z').mp hz']
    simp)
  have hiso : ∀ x ∈ L', ∀ y ∈ L', om F κ (r x) (r y) = 0 := by
    intro x hx y hy
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨p', hp', q', hq', rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hp
    obtain ⟨u', rfl⟩ := LinearMap.mem_range.mp hp'
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hq
    obtain ⟨z', hz', rfl⟩ := Submodule.mem_map.mp hq'
    simp only [map_add, LinearMap.add_apply, T1, T2, T3, T4 z z' hz hz', add_zero]
  refine ⟨L'.map r, ?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hb
    have h0 := hiso x hx y hy
    rw [om_apply] at h0
    exact sub_eq_zero.mp h0
  · rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective r hrinj L'), hfinL']
  · intro t w hw
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hw
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hp
    obtain ⟨z₀, hz₀, rfl⟩ := Submodule.mem_map.mp hq
    refine ⟨u, t • inc₁ z₀, ?_, fun ψ φ => ?_⟩
    · rw [map_smul, hr₁' z₀, emb_apply]
      funext i
      simp [(hL₁ z₀).mp hz₀]
    · have hsum : t • emb A κ (r (s u + j z₀)) = co.e (t • inc (s u)) + co.e (jA (t • inc₁ z₀)) := by
        rw [← hr', map_add, map_add, hj, smul_add, map_smul, map_smul, map_smul]
      have hω : (co.e (t • inc (s u))).1 ⬝ᵥ (co.e (jA (t • inc₁ z₀))).2 -
          (co.e (jA (t • inc₁ z₀))).1 ⬝ᵥ (co.e (t • inc (s u))).2 = 0 := by
        have hf := co.form (jA (inc₁ z₀)) (inc (s u))
        rw [hjs] at hf
        rw [map_smul, map_smul, map_smul]
        simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        linear_combination (t * t) * hf
      simp only [Darboux.rho]
      rw [hsum, schr_add ψ _ _ hω φ]
end PositivityTheory.ThKF0.Geo
