-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finite_support_blockFin_1d8804ad44af
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:55.184874+00:00
-- url     : https://prove2.me/submissions/3764b94a-d0c8-4d7c-982d-f2809ba6cc0f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison

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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {K : Type*} [Field K] [NumberField K]
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (y : Cone n K) (k : ι) (hy : y k ≠ 0) :
    (Function.support (blockFin y k)).Finite := by
  classical
  have hT : (⋃ i ∈ {i | y k i ≠ 0}, Function.mulSupport fun w : FinitePlace K ↦ w (y k i)).Finite :=
    Set.Finite.biUnion (Set.toFinite _) fun i hi ↦ FinitePlace.hasFiniteMulSupport hi
  refine hT.subset fun v hv ↦ ?_
  by_contra hvT
  apply hv
  have h1 : ∀ i, y k i ≠ 0 → v (y k i) = 1 := by
    intro i hi
    by_contra hne
    exact hvT (Set.mem_biUnion (x := i) hi hne)
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hy
  have hs : (⨆ i, v (y k i)) = 1 := by
    refine le_antisymm (ciSup_le fun i ↦ ?_) (le_ciSup_of_le (Set.finite_range _).bddAbove i0 ?_)
    · by_cases h : y k i = 0
      · rw [h, map_zero]; exact zero_le_one
      · exact (h1 i h).le
    · exact (h1 i0 hi0).ge
  simp only [blockFin, hs, Real.log_one]
end GroundTheory.Heights₂.Heights
