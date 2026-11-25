-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_join_61f48e399a76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:22:03.256873+00:00
-- url     : https://prove2.me/submissions/56baa185-778f-4b3e-a1de-e9b9afc9059b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSubQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagFrame_join_fbb3c079eb15

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
variable [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (ϖ : O) (y : (Σ k, ι k) → Ω) (B B' : ChartBundle O (segreVec y) N E)
    (BU BU' : ChartBundle O (segreVec y) r U) (BV BV' : ChartBundle O (segreVec y) m V)
    (φ : (U × V) ≃ₗ[Ω] E) (e : Fin r ⊕ Fin m ≃ Fin N)
    (he : ∀ t, ((e t : Fin N) : ℕ) = Sum.elim (fun a : Fin r => (a : ℕ)) (fun b : Fin m => r + b) t)
    (hU : ∀ c, segreVec y c ≠ 0 → ∀ u,
      (u ∈ BU.lat c ↔ φ (u, 0) ∈ B.lat c) ∧ (u ∈ BU'.lat c ↔ φ (u, 0) ∈ B'.lat c))
    (hV : ∀ c, segreVec y c ≠ 0 → ∀ q,
      (q ∈ BV.lat c ↔ ∃ z ∈ B.lat c, (φ.symm z).2 = q) ∧
        (q ∈ BV'.lat c ↔ ∃ z ∈ B'.lat c, (φ.symm z).2 = q))
    {wU wU' : Module.Basis (Fin r) Ω U} {xU xU' : Fin r → K → ℤ} {fU gU : Fin r → MRing ι O}
    (hpU : IsFlagPair ϖ y BU BU' wU wU' xU xU' fU gU)
    {wV wV' : Module.Basis (Fin m) Ω V} {xV xV' : Fin m → K → ℤ} {fV gV : Fin m → MRing ι O}
    (hpV : IsFlagPair ϖ y BV BV' wV wV' xV xV' fV gV) :
    IsFlagPair ϖ y B B' (((wU.prod wV).map φ).reindex e) (((wU'.prod wV').map φ).reindex e)
      (fun i => Sum.elim xU xV (e.symm i)) (fun i => Sum.elim xU' xV' (e.symm i))
      (fun i => Sum.elim fU fV (e.symm i)) (fun i => Sum.elim gU gV (e.symm i)) where
  flag := isFlagFrame_join y B BU BV φ e he (fun c hc u => (hU c hc u).1)
    (fun c hc q => (hV c hc q).1) hpU.flag hpV.flag
  flag' := isFlagFrame_join y B' BU' BV' φ e he (fun c hc u => (hU c hc u).2)
    (fun c hc q => (hV c hc q).2) hpU.flag' hpV.flag'
  sameFlag i i' hii' := by
    obtain ⟨t, rfl⟩ := e.surjective i
    obtain ⟨t', rfl⟩ := e.surjective i'
    rw [Fin.lt_def, he, he] at hii'
    rcases t with a | b <;> rcases t' with a' | b' <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at hii'
    · simpa using hpU.sameFlag a a' (Fin.lt_def.2 hii')
    · simp
    · have := a'.isLt
      omega
    · simpa using hpV.sameFlag b b' (Fin.lt_def.2 (by omega))
  vertical i := by
    obtain ⟨t, rfl⟩ := e.surjective i
    rcases t with a | b
    · simpa using hpU.vertical a
    · simpa using hpV.vertical b
  generic i := by
    obtain ⟨t, rfl⟩ := e.surjective i
    rcases t with a | b
    · simpa using hpU.generic a
    · simpa using hpV.generic b
end GroundTheory.Heights₂.Heights.NumbersDVR
