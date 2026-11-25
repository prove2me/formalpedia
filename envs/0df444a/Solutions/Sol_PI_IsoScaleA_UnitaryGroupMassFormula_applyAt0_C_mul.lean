-- Prove2me | solution 1 for PI.IsoScaleA.UnitaryGroupMassFormula.applyAt0_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:44:15.655624+00:00
-- url     : https://prove2.me/submissions/bca3c1b1-d5c0-4cc4-a0c4-3c5a5d38cce3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoScaleA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryScaleCount_CardEqSumColLen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoScaleA PI.IsoScaleA.UnitaryGroupMassFormula
open PI.IsoScaleA
namespace PI.IsoScaleA.UnitaryGroupMassFormula
theorem _root_.solution {T : Type} [Fintype T] {N N' : ℕ} (a : ℂ) (P : MvPolynomial (Idx T N N') ℂ)
    (G : VC T N N' → ℂ) : applyAt0 (MvPolynomial.C a * P) G = a * applyAt0 P G := by
  unfold applyAt0
  rw [MvPolynomial.C_mul', Finset.mul_sum]
  rw [Finset.sum_subset MvPolynomial.support_smul]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    ring
  · intro α _ hα
    rw [MvPolynomial.notMem_support_iff.mp hα]
    ring
end PI.IsoScaleA.UnitaryGroupMassFormula
