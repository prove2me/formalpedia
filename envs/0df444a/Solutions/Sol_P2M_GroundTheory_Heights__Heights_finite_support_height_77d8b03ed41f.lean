-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finite_support_height_77d8b03ed41f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:56.499614+00:00
-- url     : https://prove2.me/submissions/ba3865f0-83d9-4943-882e-cb21a48e6b11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight

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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (A : HermLine n)
    (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x) :
    (Function.support fun v : FinitePlace (coordField x) ↦
      ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (coordVec x k i))).Finite := by
  classical
  let c : Coord n → coordField x := fun p ↦ coordVec x p.1 p.2
  have hT : (⋃ p ∈ {p | c p ≠ 0},
      Function.mulSupport fun w : FinitePlace (coordField x) ↦ w (c p)).Finite :=
    Set.Finite.biUnion (Set.toFinite _) fun p hp ↦ FinitePlace.hasFiniteMulSupport hp
  refine hT.subset fun v hv ↦ ?_
  by_contra hvT
  apply hv
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  have h1 : ∀ i, coordVec x k i ≠ 0 → v (coordVec x k i) = 1 := by
    intro i hi
    by_contra hne
    exact hvT (Set.mem_biUnion (x := (⟨k, i⟩ : Coord n)) hi hne)
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp (hx k)
  have hi0' : coordVec x k i0 ≠ 0 := fun h ↦ hi0 (congrArg Subtype.val h)
  have hs : (⨆ i, v (coordVec x k i)) = 1 := by
    refine le_antisymm (ciSup_le fun i ↦ ?_) (le_ciSup_of_le (Set.finite_range _).bddAbove i0 ?_)
    · by_cases h : coordVec x k i = 0
      · rw [h, map_zero]; exact zero_le_one
      · exact (h1 i h).le
    · exact (h1 i0 hi0').ge
  rw [hs, Real.log_one, mul_zero]
end GroundTheory.Heights₂.Heights
