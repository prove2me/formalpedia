-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.exists_conj_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:36:19.504882+00:00
-- url     : https://prove2.me/submissions/25494fd3-5565-40ea-84a0-8cdb820e95f3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ExistsModularFunction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_NonstandardUnimodularLattice
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_norm_dS_conj_le


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
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
namespace PI.NUnimodLoc.UnitaryGroupMassFormula
theorem _root_.solution {k r : ℕ} {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hn : n ∈ Nset k r) :
    ∃ s : ℝ, 0 < s ∧ ∀ i j, ‖(dS k r s * n * (dS k r s)⁻¹ - 1) i j‖ ≤ 1 := by
  set M : ℝ := ∑ i, ∑ j, ‖n i j‖ + 1 with hM
  have h0 : 0 ≤ ∑ i, ∑ j, ‖n i j‖ := by positivity
  have hM1 : 1 ≤ M := by linarith
  have hMp : 0 < M := by linarith
  refine ⟨1 / M, div_pos one_pos hMp, fun i j => ?_⟩
  have hs1 : 1 / M ≤ 1 := by rw [div_le_one hMp]; exact hM1
  refine (norm_dS_conj_le (div_pos one_pos hMp) hs1 hn i j).trans ?_
  have h1 : ‖n i j‖ ≤ ∑ j', ‖n i j'‖ :=
    Finset.single_le_sum (f := fun j' => ‖n i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖n i j'‖ ≤ ∑ i', ∑ j', ‖n i' j'‖ :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖n i' j'‖) (fun _ _ => by positivity) (Finset.mem_univ i)
  have hle : ‖n i j‖ ≤ M := by linarith
  rw [one_div, inv_mul_le_iff₀ hMp, mul_one]
  exact hle
end PI.NUnimodLoc.UnitaryGroupMassFormula
