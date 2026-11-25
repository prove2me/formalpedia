-- Prove2me | solution 1 for PI.WwInjectiveWork.sum_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:31:13.336193+00:00
-- url     : https://prove2.me/submissions/d581adb5-d507-4359-a3ea-d8d513fc03df

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwInjective
import Definitions.Def_Formalism_PeriodIntegrals_WwCauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramInjectivity_GramVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramInjectivity_InstFintypeColChoice
import Theorems.Thm_PI_WwInjectiveWork_eval_map_nablaX
import Theorems.Thm_PI_WwInjectiveWork_deX_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WwInjectiveWork
open MvPolynomial PI.WwInjective PI.WwInjective.KM
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
namespace PI.WwInjectiveWork
theorem _root_.solution (hCB : PI.WwCauchyBinet.WwCauchyBinet) (l : ℕ) [Fact l.Prime]
    (ph : Module.Dual ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[l]))
    (hph : ∀ y, ph (DeX N nu y) = 0) :
    ∑ J : ColChoice N nu, ph (map (Int.castRingHom ℂ_[l]) (nablaX N nu J)) •
      map (Int.castRingHom ℂ_[l]) (nablaX N nu J) = 0 := by
  haveI : Infinite ℂ_[l] := Infinite.of_injective (Nat.cast : ℕ → ℂ_[l]) Nat.cast_injective
  apply MvPolynomial.funext
  intro x
  have hx := hph (fun s a i => x (s, i, a))
  rw [deX_eq_sum N nu hCB, map_sum] at hx
  simp only [MvPolynomial.C_mul', map_smul, smul_eq_mul] at hx
  simp only [map_sum, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_map_nablaX, map_zero]
  refine Eq.trans ?_ hx
  exact Finset.sum_congr rfl fun J _ => mul_comm _ _
end PI.WwInjectiveWork
