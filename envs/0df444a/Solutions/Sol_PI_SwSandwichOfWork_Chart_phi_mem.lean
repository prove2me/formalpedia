-- Prove2me | solution 1 for PI.SwSandwichOfWork.Chart_phi_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:15.866908+00:00
-- url     : https://prove2.me/submissions/91f3076e-4b30-4dcc-878c-9999afa1e122

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_UnrealifyRL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_ChartZeroEqOneOfLongWeylSq
import Theorems.Thm_PI_SwSandwichOfWork_Chart_UH_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
open PI PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}
namespace PI.SwSandwichOfWork
theorem _root_.solution (hBC : BigCellG) (hPF : PhiForm) (hLW : LieWb) (hEN : ExpN)
    {v : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r} (hv : v ∈ Vs k r) (hx : ‖v.2.1‖ < 1) :
    PhiP k r v ∈ UH (Hpk k r) := by
  simp only [Vs, Submodule.mem_prod] at hv
  obtain ⟨h1, -, h3, h4⟩ := hv
  have hc : ∀ a, (1 + v.2.1) a ≠ 0 := by
    intro a h
    have h0 : (1 : ℂ) + v.2.1 a = 0 := h
    have h' : v.2.1 a = -1 := by linear_combination h0
    have hle := norm_le_pi_norm v.2.1 a
    rw [h', norm_neg, norm_one] at hle
    linarith
  have hw : w0B k r ∈ UH (Hpk k r) := hBC k r 1 (fun _ => by simp)
  obtain ⟨hX, -⟩ := hEN k r v.1 h1
  have hB : bigCell k r (1 + v.2.1) 1 ∈ UH (Hpk k r) := hBC k r _ hc
  obtain ⟨hZ, -⟩ := (hLW k r).1 _ h3
  have hX' : (NormedSpace.exp v.2.2.2)⁻¹ ∈ UH (Hpk k r) := by
    rw [← Matrix.exp_neg]
    obtain ⟨hm, -⟩ := hEN k r _ ((lieNS k r).neg_mem h4)
    exact hm
  have e := hPF k r v.1 v.2.1 v.2.2.1 v.2.2.2
  show Phi k r v.1 v.2.1 v.2.2.1 v.2.2.2 ∈ UH (Hpk k r)
  rw [e]
  exact Chart_UH_mul hw (Chart_UH_mul (Chart_UH_mul (Chart_UH_mul hX hB) hZ) hX')
end PI.SwSandwichOfWork
