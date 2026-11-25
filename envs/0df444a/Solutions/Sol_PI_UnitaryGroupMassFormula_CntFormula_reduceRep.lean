-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.reduceRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:13.461572+00:00
-- url     : https://prove2.me/submissions/98d2a4f5-e50d-48b0-8ab4-8bc9ddc0b417

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_IsIntIntCast
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_isInt_O
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_O_of_isInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula
open NumberField
variable {K : Type} [Field K] [NumberField K]
namespace PI.UnitaryGroupMassFormula.CntFormula
theorem _root_.solution (N : ℕ) (hN : 0 < N) : ∃ Rep : Set K, Rep.Finite ∧ (∀ ρ ∈ Rep, IsIntegral ℤ ρ) ∧
    ∀ o : K, IsIntegral ℤ o → ∃ t ρ : K, IsIntegral ℤ t ∧ ρ ∈ Rep ∧ o = (N : K) * t + ρ := by
  set I : Ideal (𝓞 K) := Ideal.span {(N : 𝓞 K)} with hI
  have hIne : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have := I.finiteQuotientOfFreeOfNeBot hIne
  set σ := Function.surjInv (Ideal.Quotient.mk_surjective (I := I)) with hσ
  refine ⟨Set.range (fun q : 𝓞 K ⧸ I => algebraMap (𝓞 K) K (σ q)), Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩; exact isInt_O _
  · intro o ho
    obtain ⟨oo, rfl⟩ := O_of_isInt ho
    set q := Ideal.Quotient.mk I oo
    have hq : Ideal.Quotient.mk I (σ q) = q := Function.surjInv_eq _ q
    have hmem : oo - σ q ∈ I := Ideal.Quotient.eq.1 hq.symm
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨algebraMap (𝓞 K) K t, algebraMap (𝓞 K) K (σ q), isInt_O _, ⟨q, rfl⟩, ?_⟩
    have e : oo = t * N + σ q := by rw [ht]; ring
    rw [e, map_add, map_mul, map_natCast]
    ring
end PI.UnitaryGroupMassFormula.CntFormula
