-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.smem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:03:34.670505+00:00
-- url     : https://prove2.me/submissions/38c7568a-f4e2-424f-abdb-ae71f06e21db

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
variable {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ} (P : Matrix (Fin n) (Fin n) K)
  (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution {M : Submodule O (Fin n → K)} {c : K} (hc : c ∈ O) {x : Fin n → K} (hx : x ∈ M) :
    c • x ∈ M := by
  first
  | exact M.smul_mem (⟨c, hc⟩ : O) hx
  | (have h := M.smul_mem (⟨c, hc⟩ : O) hx
     simpa [Algebra.smul_def] using h)
end PI.UnitaryGroupMassFormula.ScXuExists
