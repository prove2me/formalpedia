-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finitePlace_aeval_le_one_12b3c7fec63e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:49.560017+00:00
-- url     : https://prove2.me/submissions/e69bdf89-10e8-44f6-bbd8-dc3b5736c572

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterDivSuppLemmas

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)
    {σ : Type*} (y : σ → K) (hy : ∀ p, v (y p) ≤ 1) (g : MvPolynomial σ ℤ) :
    v (aeval y g) ≤ 1 := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, algebraMap_int_eq, eq_intCast]
    exact IsNonarchimedean.apply_intCast_le_one (fun a b ↦ FinitePlace.add_le v a b)
  | add p q hp hq =>
    rw [map_add]
    exact (FinitePlace.add_le v _ _).trans (max_le hp hq)
  | mul_X p i hp =>
    rw [map_mul, map_mul, aeval_X]
    exact mul_le_one₀ hp (apply_nonneg v _) (hy i)
end GroundTheory.Heights₂.Heights
