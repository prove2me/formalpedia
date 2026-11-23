-- Prove2me | solution 1 for PI.WwMainW.Lfun_eq_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:10.85361+00:00
-- url     : https://prove2.me/submissions/8aec4ec7-b213-4ac4-ba57-9b409269a13d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_LfunEqOfSubset

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
theorem _root_.solution {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l])
    (s : Finset ((Lt × Fin N0 × Fin N1) →₀ ℕ)) (hs : P.support ⊆ s) :
    Lfun l N0 N1 Th P = ∑ α ∈ s, coeff α P * wt l N0 N1 Th α := by
  unfold Lfun
  exact Finset.sum_subset hs (fun α _ h => by
    rw [MvPolynomial.mem_support_iff, not_not] at h
    rw [h, zero_mul])
end PI.WwMainW
