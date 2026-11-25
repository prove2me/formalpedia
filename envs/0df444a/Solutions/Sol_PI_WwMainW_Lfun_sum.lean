-- Prove2me | solution 1 for PI.WwMainW.Lfun_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:53.632732+00:00
-- url     : https://prove2.me/submissions/aaedc0a8-5d11-4456-b336-10e9e852baf2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_InfinitePadicComplex

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
theorem _root_.solution (hLin : LLin) {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) {ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l]) :
    Lfun l N0 N1 Th (∑ i ∈ s, f i) = ∑ i ∈ s, Lfun l N0 N1 Th (f i) := by
  classical
  obtain ⟨hadd, hzero, -⟩ := hLin Lt l N0 N1 Th
  refine Finset.induction_on s ?_ ?_
  · simp [hzero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
end PI.WwMainW
