-- Prove2me | solution 1 for PI.WwMainW.wwMain_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:54.535945+00:00
-- url     : https://prove2.me/submissions/d720cb97-31c0-4c42-a516-c225b6c15cf8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_InfinitePadicComplex
import Theorems.Thm_PI_WwMainW_Lfun_sum
import Theorems.Thm_PI_WwMainW_applyQ_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open PI PI.WwMainW
open PI.WwMain PI.WwMain.KM
namespace PI.WwMainW
theorem _root_.solution (hE : EvalH) (hL : LH) (hLin : LLin) (hD : DeXCB) : WwMain := by
  intro Lt _ _ l _ N0 N1 nu Th ph Q hQ y'
  rw [applyQ_eq l N0 N1 Th Q y']
  have heval : ∀ (g : Lt × Fin N0 × ℕ → MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l])
      (z : Lt × Fin N0 × Fin N1 → ℂ_[l]), eval z (aeval g Q) = eval (fun v => eval z (g v)) Q := by
    intro g z
    have h : (aeval z).comp (aeval g) = aeval (R := ℂ_[l]) (fun v => aeval z (g v)) :=
      MvPolynomial.algHom_ext fun v => by simp
    have h2 := congrArg (fun φ : MvPolynomial (Lt × Fin N0 × ℕ) ℂ_[l] →ₐ[ℂ_[l]] ℂ_[l] => φ Q) h
    simpa [MvPolynomial.coe_aeval_eq_eval] using h2
  have hP : aeval (fun v : Lt × Fin N0 × ℕ => ∑ b : Fin N1,
      C (y' v.1 b v.2.2) * X ((v.1, v.2.1, b) : Lt × Fin N0 × Fin N1)) Q =
      ∑ I : ColChoice N1 nu, C (minY N1 nu I y') * Hpol l N0 N1 ph (Gxz N0 N1 nu I) := by
    apply MvPolynomial.funext
    intro z
    rw [heval]
    have hy : (fun v : Lt × Fin N0 × ℕ => eval z (∑ b : Fin N1,
        C (y' v.1 b v.2.2) * X ((v.1, v.2.1, b) : Lt × Fin N0 × Fin N1))) =
        fun v => (fun s a j => ∑ b : Fin N1, z (s, a, b) * y' s b j) v.1 v.2.1 v.2.2 := by
      funext v
      simp [mul_comm]
    rw [hy, hQ (fun s a j => ∑ b : Fin N1, z (s, a, b) * y' s b j), hD Lt l N0 N1 nu z y']
    simp only [map_sum, map_mul, eval_C, C_mul', map_smul, smul_eq_mul, MvPolynomial.smul_eval,
      hE Lt l N0 N1 ph]
  rw [hP, Lfun_sum hLin, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [(hLin Lt l N0 N1 Th).2.2, hL Lt l N0 N1 Th ph]
end PI.WwMainW
