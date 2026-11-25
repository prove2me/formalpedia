-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.uq_exists_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:21.36303+00:00
-- url     : https://prove2.me/submissions/427d7208-d660-40a5-8dd8-a41708cee100

import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_mem_kSpan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_kSpan_stable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_kRel_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_kRel_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uqG_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_bij

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open Formalism.REAL
variable {n : ℕ}
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V)
    (F' : Fin n → Fin n → Module.End ℂ V') (Λ : Fin n → ℝ) (w : V) (w' : V')
    (hR : KRel ε F) (hR' : KRel ε F') (hU : KUnit ε F) (hU' : KUnit ε F')
    (hw : KHighest ε F Λ w) (hw' : KHighest ε F' Λ w') (hw0 : w ≠ 0) (hw0' : w' ≠ 0)
    (hT : kSpan ε F w = ⊤) (hT' : kSpan ε F' w' = ⊤) :
    ∃ φ : V ≃ₗ[ℂ] V', (∀ a b, ε a = ε b → ∀ v, φ (F a b v) = F' a b (φ v)) ∧ φ w = w' := by
  classical
  have hRG : KRel ε (uqG F F') :=
    uq_kRel_map ε (fun a b => ((F a b, F' a b) : Module.End ℂ V × Module.End ℂ V'))
      ((LinearEquiv.conjRingEquiv (WithLp.linearEquiv 2 ℂ (V × V')).symm).toRingHom.comp
        (LinearMap.prodMapRingHom ℂ V V')) (uq_kRel_prod ε F F' hR hR')
  have hUG : KUnit ε (uqG F F') := by
    intro a b hab y z
    simp only [WithLp.prod_inner_apply, uqG_apply]
    rw [hU a b hab, hU' a b hab]
  have hxH : KHighest ε (uqG F F') Λ (WithLp.toLp 2 (w, w')) := by
    refine ⟨fun a => WithLp.ofLp_injective 2 ?_, fun a b hlt hab => WithLp.ofLp_injective 2 ?_⟩
    · rw [uqG_apply]
      simp [hw.1 a, hw'.1 a]
    · rw [uqG_apply]
      simp [hw.2 a b hlt hab, hw'.2 a b hlt hab]
  let p₁ : WithLp 2 (V × V') →ₗ[ℂ] V :=
    LinearMap.fst ℂ V V' ∘ₗ (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap
  let p₂ : WithLp 2 (V × V') →ₗ[ℂ] V' :=
    LinearMap.snd ℂ V V' ∘ₗ (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap
  have hp₁ : ∀ y, p₁ y = (WithLp.ofLp y).1 := fun _ => rfl
  have hp₂ : ∀ y, p₂ y = (WithLp.ofLp y).2 := fun _ => rfl
  have hb₁ := uq_bij ε (uqG F F') F Λ (WithLp.toLp 2 (w, w')) hRG hUG hxH p₁
    (fun a b hab y => by rw [hp₁, hp₁, uqG_apply] <;> rfl) (by rw [hp₁]; simpa using hw0)
    (by rw [hp₁]; simpa using hT)
  have hb₂ := uq_bij ε (uqG F F') F' Λ (WithLp.toLp 2 (w, w')) hRG hUG hxH p₂
    (fun a b hab y => by rw [hp₂, hp₂, uqG_apply] <;> rfl) (by rw [hp₂]; simpa using hw0')
    (by rw [hp₂]; simpa using hT')
  let e₁ := LinearEquiv.ofBijective (p₁.domRestrict (kSpan ε (uqG F F') (WithLp.toLp 2 (w, w')))) hb₁
  let e₂ := LinearEquiv.ofBijective (p₂.domRestrict (kSpan ε (uqG F F') (WithLp.toLp 2 (w, w')))) hb₂
  have he₁ : ∀ z, e₁ z = p₁ z := fun _ => rfl
  have he₂ : ∀ z, e₂ z = p₂ z := fun _ => rfl
  refine ⟨e₁.symm.trans e₂, ?_, ?_⟩
  · intro a b hab v
    have hmem : uqG F F' a b ((e₁.symm v : _) : WithLp 2 (V × V')) ∈
        kSpan ε (uqG F F') (WithLp.toLp 2 (w, w')) :=
      uq_kSpan_stable ε (uqG F F') _ a b hab _ (e₁.symm v).2
    have hv1 : (WithLp.ofLp ((e₁.symm v : _) : WithLp 2 (V × V'))).1 = v := by
      rw [← hp₁, ← he₁, LinearEquiv.apply_symm_apply]
    have h1 : e₁.symm (F a b v) = ⟨_, hmem⟩ := by
      rw [LinearEquiv.symm_apply_eq, he₁]
      show F a b v = p₁ (uqG F F' a b (e₁.symm v))
      rw [hp₁, uqG_apply, hv1]
    show e₂ (e₁.symm (F a b v)) = F' a b (e₂ (e₁.symm v))
    simp only [h1, he₂, hp₂, uqG_apply]
  · have hx : WithLp.toLp 2 (w, w') ∈ kSpan ε (uqG F F') (WithLp.toLp 2 (w, w')) :=
      uq_mem_kSpan ε _ _
    have h2 : e₁.symm w = ⟨_, hx⟩ := by
      rw [LinearEquiv.symm_apply_eq, he₁, hp₁] <;> simp
    show e₂ (e₁.symm w) = w'
    rw [h2, he₂, hp₂] <;> simp
end ReciprocityTheory.ChartRestriction.DS.HW
