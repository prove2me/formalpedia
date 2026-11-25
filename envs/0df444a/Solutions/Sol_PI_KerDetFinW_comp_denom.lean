-- Prove2me | solution 1 for PI.KerDetFinW.comp_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:45:04.022991+00:00
-- url     : https://prove2.me/submissions/8d1f09c7-f57b-40cc-8090-401072038b7a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom

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
open PI PI.KerDetFinW
open PI.KerIso
namespace PI.KerDetFinW
theorem _root_.solution {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type} [Fintype n]
    {M : Set E} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)} {p : ℕ}
    (hg : AtP M g p) (hg' : AtP M g' p) (v : Fin 4 × n → K)
    (hv : ∀ w, v w ∈ (algebraMap (𝓞 K) K).range) :
    ∃ u : ℕ, Nat.Coprime u p ∧ ∀ w, (u : K) * (g.symm.trans g') v w ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨s, hs, hsM⟩ := hg.2 v hv
  have hx : ∀ a, ((s : K) • g.symm v) a ∈ M := by
    intro a
    rw [Pi.smul_apply, Algebra.smul_def, map_natCast]
    exact hsM a
  obtain ⟨t, ht, htM⟩ := hg'.1 ((s : K) • g.symm v) hx
  refine ⟨t * s, Nat.Coprime.mul ht hs, fun w => ?_⟩
  have h := htM w
  rw [map_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc] at h
  rw [LinearEquiv.trans_apply, Nat.cast_mul]
  exact h
end PI.KerDetFinW
