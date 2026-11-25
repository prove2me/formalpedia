-- Prove2me | solution 1 for PI.KerExtCWork.ringHom_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:50:37.455255+00:00
-- url     : https://prove2.me/submissions/b735a164-cee8-4294-afea-cdbcfb729f4c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConstantCoefficientKernel_RingHomCoeffZero

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
open PI PI.KerExtCWork
namespace PI.KerExtCWork
theorem _root_.solution {E : Type} [Field E] {n : Type} [Fintype n]
    (τ : n → E →+* ℂ) (hτ : Function.Injective τ) (c : n → ℂ)
    (h : ∀ e : E, ∑ i, c i * τ i e = 0) : c = 0 := by
  have hinj : Function.Injective (fun i => (τ i).toMonoidHom) := by
    intro i j hij
    apply hτ
    ext x
    exact DFunLike.congr_fun hij x
  have hli := (linearIndependent_monoidHom E ℂ).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  funext i
  apply hli c
  funext e
  simpa [Finset.sum_apply, smul_eq_mul] using h e
end PI.KerExtCWork
