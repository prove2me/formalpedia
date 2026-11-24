-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_mem_dual_iff_40d47eed4618
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:16.814782+00:00
-- url     : https://prove2.me/submissions/c179ccca-4088-44a0-8c0a-ebaf6572be83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K]
variable {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} {φ : Fin (N + 1) → Fin m → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (hφ : IsDualBasis L φ) (u : Fin m → K) :
    u ∈ latticeDual L ↔ ∃ c : Fin (N + 1) → ℤ, ∑ b, c b • φ b = u := by
  rw [← Submodule.mem_span_range_iff_exists_fun ℤ, hφ.span_eq, Submodule.restrictScalars_mem]
end GroundTheory.Heights₂.Heights.LatticeModel
