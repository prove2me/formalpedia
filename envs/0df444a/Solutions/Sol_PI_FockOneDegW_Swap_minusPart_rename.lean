-- Prove2me | solution 1 for PI.FockOneDegW.Swap.minusPart_rename
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:48.503941+00:00
-- url     : https://prove2.me/submissions/976849d3-ca73-468b-939e-82c31efcd8a0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
import Theorems.Thm_PI_FockOneDegW_Swap_hc_rename

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Swap
open PI.FockOneDegW PI.FockOneDegW.Diag
variable {σ τ : Type*} (f : σ ≃ τ)
namespace PI.FockOneDegW.Swap
theorem _root_.solution (A : Module.End ℂ (MvPolynomial σ ℂ))
    (B : Module.End ℂ (MvPolynomial τ ℂ)) (hAB : ∀ Q, B (rename f Q) = rename f (A Q))
    (P : MvPolynomial σ ℂ) : rename f (minusPart A P) = minusPart B (rename f P) := by
  unfold minusPart
  have hfin : Function.HasFiniteSupport
      (fun d : ℕ => homogeneousComponent d (A (homogeneousComponent (d + 2) P))) := by
    refine (Set.finite_Iio P.totalDegree).subset ?_
    intro d hd
    by_contra h
    apply hd
    simp only [Set.mem_Iio, not_lt] at h
    simp only [homogeneousComponent_eq_zero (d + 2) P (by omega), map_zero]
  rw [map_finsum (rename f) hfin]
  refine finsum_congr fun d => ?_
  rw [← hc_rename, ← hAB, ← hc_rename]
end PI.FockOneDegW.Swap
