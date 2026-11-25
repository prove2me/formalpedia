-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartFinite_lineVar_natDegree_coeff_0f4cef3db7dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:52.650278+00:00
-- url     : https://prove2.me/submissions/8b9d635f-3829-4820-87ae-ad12203cb140

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PFGNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartFinite
variable {F : Type} [Field F] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartFinite
theorem _root_.solution (t : Fin n → F) (m : Fin n) (ij : Fin (e + 1) × Fin n) :
    (lineVar t m ij).natDegree ≤ groupWeight (e + 1) n ij 0 ∧
      (lineVar t m ij).coeff (groupWeight (e + 1) n ij 0) = specFirstVar t ij := by
  obtain ⟨i, j⟩ := ij
  cases i using Fin.cases with
  | zero =>
    simp only [lineVar, specFirstVar, groupWeight, Fin.cases_zero, Pi.single_eq_same]
    refine ⟨?_, ?_⟩
    · compute_degree
    · by_cases h : j = m <;> simp [h, Polynomial.coeff_one]
  | succ i =>
    simp [lineVar, specFirstVar, groupWeight, (Fin.succ_ne_zero i).symm]
end GroundTheory.Heights₂.Heights.ChartFinite
