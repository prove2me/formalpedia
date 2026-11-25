-- Prove2me | solution 1 for PI.Residue.mem_hit_of_mem_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:14:01.731703+00:00
-- url     : https://prove2.me/submissions/8ca72b9e-26aa-46df-b25e-d4e5dc2252d0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_LatticeCountGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_NormAtPlacePosOfNormPos
import Theorems.Thm_PI_Residue_normAtPlace_pos_of_norm_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable (K : Type) [Field K] [NumberField K]
variable {K}
namespace PI.Residue
theorem _root_.solution {ρ : ℝ} {y x : mixedSpace K} (hy : 0 < mixedEmbedding.norm y)
    (hx : x ∈ box K (fun w => ρ / (2 * normAtPlace w y)) -
      box K (fun w => ρ / (2 * normAtPlace w y))) : y ∈ hit K ρ x := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sub.mp hx
  intro w
  have hw := normAtPlace_pos_of_norm_pos hy w
  have h1 : normAtPlace w (a - b) ≤ normAtPlace w a + normAtPlace w b := by
    rw [sub_eq_add_neg]
    refine (normAtPlace_add_le w a (-b)).trans ?_
    rw [normAtPlace_neg]
  have ha' : normAtPlace w a < ρ / (2 * normAtPlace w y) := ha w
  have hb' : normAtPlace w b < ρ / (2 * normAtPlace w y) := hb w
  have h2 : normAtPlace w (a - b) < ρ / normAtPlace w y := by
    have : ρ / (2 * normAtPlace w y) + ρ / (2 * normAtPlace w y) = ρ / normAtPlace w y := by
      field_simp
      ring
    linarith
  rw [lt_div_iff₀ hw] at h2
  rw [mul_comm]
  exact h2
end PI.Residue
