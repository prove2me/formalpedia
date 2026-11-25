-- Prove2me | solution 1 for PI.Residue.classSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:21.211948+00:00
-- url     : https://prove2.me/submissions/28d7ce1d-deaa-4659-8542-f8a8eaadce5d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_IdealEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors ENNReal Classical
noncomputable section
open PI PI.Residue
namespace PI.Residue
theorem _root_.solution : ClassSum := by
  intro K _ _ s hs
  have h1 : ∑ C : ClassGroup (𝓞 K), classZeta K C s =
      ∑' I : (Ideal (𝓞 K))⁰, ENNReal.ofReal ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s)) := by
    rw [← (Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 K))⁰ => ClassGroup.mk0 I)).tsum_eq,
      ENNReal.tsum_sigma', tsum_fintype]
    rfl
  rw [h1, idealZeta, ENNReal.ofReal_tsum_of_nonneg (fun I => by positivity) hs,
    ← (idealEquiv K).tsum_eq]
  exact le_of_eq rfl
end PI.Residue
