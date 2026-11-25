-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagFrame_join_fbb3c079eb15
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:29.165798+00:00
-- url     : https://prove2.me/submissions/8bbbf8d8-6eeb-4250-b208-ddd35a38dd19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSubQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω] {O : Type*} [CommRing O]
  [Algebra O Ω] {N r m : ℕ} {E U V : Type*} [AddCommGroup E] [Module Ω E] [AddCommGroup U]
  [Module Ω U] [AddCommGroup V] [Module Ω V]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (y : (Σ k, ι k) → Ω) (B : ChartBundle O (segreVec y) N E)
    (BU : ChartBundle O (segreVec y) r U) (BV : ChartBundle O (segreVec y) m V)
    (φ : (U × V) ≃ₗ[Ω] E) (e : Fin r ⊕ Fin m ≃ Fin N)
    (he : ∀ t, ((e t : Fin N) : ℕ) = Sum.elim (fun a : Fin r => (a : ℕ)) (fun b : Fin m => r + b) t)
    (hU : ∀ c, segreVec y c ≠ 0 → ∀ u, u ∈ BU.lat c ↔ φ (u, 0) ∈ B.lat c)
    (hV : ∀ c, segreVec y c ≠ 0 → ∀ q, q ∈ BV.lat c ↔ ∃ z ∈ B.lat c, (φ.symm z).2 = q)
    {wU : Module.Basis (Fin r) Ω U} {xU : Fin r → K → ℤ} (hfU : IsFlagFrame y BU wU xU)
    {wV : Module.Basis (Fin m) Ω V} {xV : Fin m → K → ℤ} (hfV : IsFlagFrame y BV wV xV) :
    IsFlagFrame y B (((wU.prod wV).map φ).reindex e) (fun i => Sum.elim xU xV (e.symm i)) where
  graded c hc i := by
    obtain ⟨t, rfl⟩ := e.surjective i
    rcases t with a | b
    · rw [Equiv.symm_apply_apply, Sum.elim_inl, ← hfU.graded c hc a]
      ext s
      constructor
      · rintro ⟨v, hv, hhi, rfl⟩
        have h2 : (φ.symm v).2 = 0 := by
          refine wV.repr.injective (Finsupp.ext fun b => ?_)
          have := hhi (e (Sum.inr b)) (by
            rw [Fin.lt_def, he, he]
            have := a.isLt
            simp only [Sum.elim_inl, Sum.elim_inr]
            omega)
          simpa using this
        have hv' : φ ((φ.symm v).1, 0) = v := by
          rw [← h2]
          simp
        refine ⟨(φ.symm v).1, (hU c hc _).2 (hv'.symm ▸ hv), fun a' ha' => ?_, ?_⟩
        · have := hhi (e (Sum.inl a')) (by
            rw [Fin.lt_def, he, he]
            simpa using Fin.lt_def.1 ha')
          simpa using this
        · simp
      · rintro ⟨u, hu, hhi, rfl⟩
        refine ⟨φ (u, 0), (hU c hc u).1 hu, fun i' hi' => ?_, by simp⟩
        obtain ⟨t', rfl⟩ := e.surjective i'
        rw [Fin.lt_def, he, he] at hi'
        rcases t' with a' | b'
        · simp only [Sum.elim_inl] at hi'
          simp [hhi a' (Fin.lt_def.2 hi')]
        · simp
    · rw [Equiv.symm_apply_apply, Sum.elim_inr, ← hfV.graded c hc b]
      ext s
      constructor
      · rintro ⟨v, hv, hhi, rfl⟩
        refine ⟨(φ.symm v).2, (hV c hc _).2 ⟨v, hv, rfl⟩, fun b' hb' => ?_, by simp⟩
        have := hhi (e (Sum.inr b')) (by
          rw [Fin.lt_def, he, he]
          have := Fin.lt_def.1 hb'
          simp only [Sum.elim_inr]
          omega)
        simpa using this
      · rintro ⟨q, hq, hhi, rfl⟩
        obtain ⟨z, hz, rfl⟩ := (hV c hc q).1 hq
        refine ⟨z, hz, fun i' hi' => ?_, by simp⟩
        obtain ⟨t', rfl⟩ := e.surjective i'
        rw [Fin.lt_def, he, he] at hi'
        rcases t' with a' | b'
        · simp only [Sum.elim_inl, Sum.elim_inr] at hi'
          have := a'.isLt
          omega
        · simp only [Sum.elim_inr] at hi'
          simp [hhi b' (Fin.lt_def.2 (by omega))]
end GroundTheory.Heights₂.Heights.NumbersDVR
