-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.sep_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:06:59.654388+00:00
-- url     : https://prove2.me/submissions/d61ef3ab-0c2d-4e49-a0a3-aaa42ac1ae4c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_IsPD_const
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_IsPD_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_IsPD_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_Sep_const
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_Sep_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_Sep_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_Sep_coord
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_Sep_conjCoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory Matrix
namespace PI.UnitaryGroupMassFormula.PolyCoef
theorem _root_.solution {N : ℕ} {f : C(UG N, ℂ)} (hf : f ∈ algA N) : Sep (⇑f) := by
  have hf' : f ∈ Algebra.adjoin ℂ ((Set.range fun ij : Fin N × Fin N => coordC ij.1 ij.2) ∪
      star (Set.range fun ij : Fin N × Fin N => coordC ij.1 ij.2)) := by
    rw [← StarAlgebra.adjoin_toSubalgebra]; exact hf
  clear hf
  induction hf' using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨⟨i, j⟩, rfl⟩ | hx
    · exact Sep.coord i j
    · obtain ⟨⟨i, j⟩, hij⟩ := (Set.mem_star.mp hx)
      have : x = star (coordC i j) := by rw [show coordC i j = star x from hij, star_star]
      subst this
      exact Sep.conjCoord i j
  | algebraMap r => exact Sep.const r
  | add x y _ _ hx hy => exact Sep.add hx hy
  | mul x y _ _ hx hy => exact Sep.mul hx hy
end PI.UnitaryGroupMassFormula.PolyCoef
