-- Prove2me | solution 1 for PI.VolStabS.FFHS.ffH_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:50:36.189901+00:00
-- url     : https://prove2.me/submissions/0754f3d7-c180-435f-8719-64dbb04fae19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFCnt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFIn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.VolStabS.FFHS
open Module Polynomial
section matrix
variable {K : Type} [Field K] {σ : K →+* K}
private theorem ffH_single_right {M : ℕ} (J : Matrix (Fin M) (Fin M) K) (x : Fin M → K)
    (j : Fin M) :
    PI.VolStabS.ffH σ J x (Pi.single j 1) = ∑ i, σ (x i) * J i j := by
  unfold PI.VolStabS.ffH
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_eq_single j]
  · simp
  · intro b hb
    simp [Pi.single_apply, hb]
end matrix
section field
variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
end field
end PI.VolStabS.FFHS
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.FFHS
open Module Polynomial
variable {K : Type} [Field K] {σ : K →+* K}
namespace PI.VolStabS.FFHS
theorem _root_.solution {n : ℕ} (T : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    ffH σ T (Pi.single i 1) (Pi.single j 1) = T i j := by
  rw [ffH_single_right, Fintype.sum_eq_single i]
  · simp
  · intro b hb
    simp [Pi.single_apply, hb]
end PI.VolStabS.FFHS
