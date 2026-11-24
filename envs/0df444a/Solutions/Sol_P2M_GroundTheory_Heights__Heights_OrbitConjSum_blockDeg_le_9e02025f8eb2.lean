-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitConjSum_blockDeg_le_9e02025f8eb2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:27:16.359621+00:00
-- url     : https://prove2.me/submissions/082e80d2-0201-48bd-b18a-f2d7ab981dd0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitConjSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitConjSumLemmas

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitConjSum
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.OrbitConjSum
theorem _root_.solution (P : MvPolynomial (Coord n) ℤ) {m : Coord n →₀ ℕ} (hm : m ∈ P.support)
    (k : ι) : ∑ i, m ⟨k, i⟩ ≤ P.totalDegree := by
  refine le_trans ?_ (le_totalDegree hm)
  rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl), Fintype.sum_sigma]
  exact Finset.single_le_sum (f := fun k ↦ ∑ i, m ⟨k, i⟩) (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ k)
end GroundTheory.Heights₂.Heights.OrbitConjSum
