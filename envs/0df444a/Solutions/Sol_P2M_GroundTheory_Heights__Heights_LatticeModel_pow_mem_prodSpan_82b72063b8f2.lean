-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_pow_mem_prodSpan_82b72063b8f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:01:46.567752+00:00
-- url     : https://prove2.me/submissions/e51cb468-88d4-4bdc-947b-2c4eba7b0b7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_one_mem_prodSpan_zero_c23367664238
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_mul_mem_prodSpan_f0c3d551bff6

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
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution {p : MvPolynomial (Fin m) K} (hp : p ∈ prodSpan L 1) (k : ℕ) :
    p ^ k ∈ prodSpan L k := by
  induction k with
  | zero => rw [pow_zero]; exact one_mem_prodSpan_zero
  | succ k ih => rw [pow_succ]; exact mul_mem_prodSpan ih hp
end GroundTheory.Heights₂.Heights.LatticeModel
