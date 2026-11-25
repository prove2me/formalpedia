-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.maximal_compact_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:31.963694+00:00
-- url     : https://prove2.me/submissions/868bbe88-3d74-41cc-8130-42fc38978992

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Mathlib.Analysis.CStarAlgebra.Matrix
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Matrix
noncomputable section
namespace PI.QuotSetU.UnitaryGroupMassFormula
open PI PI.QuotSetU
private lemma isClosed_UH' (k r : ℕ) : IsClosed (UH (Hpk k r)) := by
  rw [UH.eq_1]
  exact isClosed_eq
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const
end PI.QuotSetU.UnitaryGroupMassFormula
end
end

set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula
open PI PI.QuotSetU
namespace PI.QuotSetU.UnitaryGroupMassFormula
theorem _root_.solution : KCompact := by
  intro k r
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin (2 * r + k + 1) =>
      Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have c2 : IsClosed {u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | uᴴ * u = 1} :=
    isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
  have hC : IsClosed {u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ |
      u ∈ UH (Hpk k r) ∧ uᴴ * u = 1} := (isClosed_UH' k r).inter c2
  refine hK.of_isClosed_subset hC
    (fun (u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) hu => ?_)
  have hu' : u ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hu.2
  exact Set.mem_pi.2 fun i _ => Set.mem_pi.2 fun j _ =>
    mem_closedBall_zero_iff.2 (entry_norm_bound_of_unitary hu' i j)
end PI.QuotSetU.UnitaryGroupMassFormula
