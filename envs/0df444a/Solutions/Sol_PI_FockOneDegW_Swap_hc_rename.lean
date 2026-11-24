-- Prove2me | solution 1 for PI.FockOneDegW.Swap.hc_rename
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:08.223395+00:00
-- url     : https://prove2.me/submissions/85571814-893e-44b2-abf2-f508178dd8b2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap

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
theorem _root_.solution (φ : MvPolynomial σ ℂ) (k : ℕ) :
    homogeneousComponent k (rename f φ) = rename f (homogeneousComponent k φ) := by
  conv_lhs => rw [← sum_homogeneousComponent φ]
  rw [map_sum, map_sum]
  have h : ∀ i, homogeneousComponent k (rename f (homogeneousComponent i φ)) =
      if k = i then rename f (homogeneousComponent i φ) else 0 := fun i =>
    homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2
      ((homogeneousComponent_isHomogeneous i φ).rename_isHomogeneous))
  simp_rw [h]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by simp only [Finset.mem_range] at hk; omega), map_zero]
end PI.FockOneDegW.Swap
