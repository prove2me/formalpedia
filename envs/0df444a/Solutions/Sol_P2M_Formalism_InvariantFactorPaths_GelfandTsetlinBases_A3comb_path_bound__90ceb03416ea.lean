-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_path_bound__90ceb03416ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:32.139642+00:00
-- url     : https://prove2.me/submissions/55550674-89d2-47cb-b949-b38dec4f6492

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_path_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
theorem _root_.solution {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) (i : ℕ) (hi : i ≤ N) (m : Fin n) :
    |μ i m| ≤ ((∑ k ∈ range N, B k : ℕ) : ℤ) := by
  have := path_bound hp i hi m
  have h2 : (∑ k ∈ range i, B k) ≤ ∑ k ∈ range N, B k :=
    Finset.sum_le_sum_of_subset (Finset.range_mono hi)
  have h3 : ((∑ k ∈ range i, B k : ℕ) : ℤ) ≤ ((∑ k ∈ range N, B k : ℕ) : ℤ) := by
    exact_mod_cast h2
  linarith
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
