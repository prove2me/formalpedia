-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SmallSections_mkF_chartMonomial_ne_zero_b5c3c1e12aff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:14.72369+00:00
-- url     : https://prove2.me/submissions/c1c8a887-ba02-43c0-b61c-86ebddc1c475

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_mkF_X_ne_zero_5ca902d68882

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SmallSections
theorem _root_.solution {P : ArithVariety n} {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    (d : ι → ℕ) : P.mkF (chartMonomial c d) ≠ 0 := by
  rw [chartMonomial, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ by rw [map_pow]; exact pow_ne_zero _ (mkF_X_ne_zero hc k)
end GroundTheory.Heights₂.Heights.SmallSections
