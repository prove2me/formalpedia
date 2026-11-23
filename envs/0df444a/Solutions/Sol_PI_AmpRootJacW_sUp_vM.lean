-- Prove2me | solution 1 for PI.AmpRootJacW.sUp_vM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:04.544065+00:00
-- url     : https://prove2.me/submissions/10df6843-9cc7-4127-8062-7798c1932afa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.AmpRootJacW
variable {n : ℕ}
variable (S : Finset (Fin n × Fin n))
namespace PI.AmpRootJacW
theorem _root_.solution (hS : ∀ q ∈ S, q.1 < q.2) (v : S → ℂ) : SUp (vM S v) := by
  intro i j hji
  unfold vM
  rw [dif_neg]
  intro hm
  have h1 : i < j := hS _ hm
  rw [Fin.lt_def] at h1
  omega
end PI.AmpRootJacW
