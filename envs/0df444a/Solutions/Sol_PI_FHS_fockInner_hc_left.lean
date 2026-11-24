-- Prove2me | solution 1 for PI.FHS.fockInner_hc_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:23.474649+00:00
-- url     : https://prove2.me/submissions/35880664-294e-4c8f-9bac-d846866b2dd1

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Theorems.Thm_PI_FHS_fockInner_eq_sum_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FHS
variable {σ : Type*}
namespace PI.FHS
theorem _root_.solution {n : ℕ} (P Q : MvPolynomial σ ℂ) (hQ : Q ∈ FockH1Action.homog σ n) :
    FockH1Action.fockInner (homogeneousComponent n P) Q = FockH1Action.fockInner P Q := by
  have hQ' : Q.IsHomogeneous n := (mem_homogeneousSubmodule _ _).mp hQ
  rw [fockInner_eq_sum_right (homogeneousComponent n P) Q Q.support
      (Finset.Subset.refl _),
    fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _)]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  have hdeg := hQ' (MvPolynomial.mem_support_iff.mp hα)
  rw [coeff_homogeneousComponent]
  split_ifs with hc
  · rfl
  · exact absurd (by
      first
      | exact hdeg
      | (rw [Finsupp.degree_eq_weight_one]; exact hdeg)) hc
end PI.FHS
