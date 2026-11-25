-- Prove2me | solution 1 for PI.KerIso.DetOrdW.comp_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:48:52.273206+00:00
-- url     : https://prove2.me/submissions/2f356732-fba4-48b3-9df7-f0a0ae2feddc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelOrder_ValNatCastEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KerIso PI.KerIso.DetOrdW
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
variable {E : Type} [Field E] [Algebra K E] {n : Type} [Fintype n]
namespace PI.KerIso.DetOrdW
theorem _root_.solution {M : Set E} {p : ℕ} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)}
    (hg : AtP M g p) (hg' : AtP M g' p) (v : Fin 4 × n → K)
    (hv : ∀ w, v w ∈ (algebraMap (𝓞 K) K).range) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ w, (s : K) * g' (g.symm v) w ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨-, hgB⟩ := hg
  obtain ⟨hgA', -⟩ := hg'
  obtain ⟨s₁, hs₁, h₁⟩ := hgB v hv
  obtain ⟨s₂, hs₂, h₂⟩ := hgA' ((s₁ : K) • g.symm v) (fun a => by
    simpa [Pi.smul_apply, Algebra.smul_def] using h₁ a)
  refine ⟨s₂ * s₁, Nat.Coprime.mul hs₂ hs₁, fun w => ?_⟩
  have h := h₂ w
  rw [map_smul, Pi.smul_apply, smul_eq_mul] at h
  rw [Nat.cast_mul, mul_assoc]
  exact h
end PI.KerIso.DetOrdW
