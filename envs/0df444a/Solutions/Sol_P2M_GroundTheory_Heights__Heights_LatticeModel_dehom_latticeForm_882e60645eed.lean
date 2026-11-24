-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_882e60645eed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:57.017973+00:00
-- url     : https://prove2.me/submissions/7eac0562-a522-4b27-a991-61b5e27fcaee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_algebraMap_C_06ff1ad36227

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
variable {r : ℕ}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (u : Fin (r + 1) → K) :
    dehom K r (latticeForm u) = algebraMap (MvPolynomial (Fin r) K) (LatticeField K r)
      (C (u 0) + ∑ j : Fin r, C (u j.succ) * X j) := by
  simp only [dehom, latticeForm, map_sum, map_mul, map_add, coe_eval₂Hom, eval₂_C, eval₂_X, algebraMap_C,
    Fin.sum_univ_succ, genericVal, Fin.cases_zero, Fin.cases_succ, mul_one]
end GroundTheory.Heights₂.Heights.LatticeModel
