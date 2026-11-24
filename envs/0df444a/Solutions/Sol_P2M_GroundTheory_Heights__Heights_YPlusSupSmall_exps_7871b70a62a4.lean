-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSupSmall_exps_7871b70a62a4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:50.993657+00:00
-- url     : https://prove2.me/submissions/711c1344-1dcb-4e0f-a2bb-02473afa9bd5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSupSmall

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
open GroundTheory.Heights₂.Heights.YPlusSupSmall
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.YPlusSupSmall
theorem _root_.solution {τ : ℕ} {f : MvPolynomial (Coord D.extSizes) ℤ}
    (hf : Geo.IsMultiHomog (ι := blockIdx D.extSizes) f (Pi.single none τ)) {m : Coord D.extSizes →₀ ℕ}
    (hm : m ∈ f.support) : (∀ k i, m ⟨some k, i⟩ = 0) ∧ ∑ j, m ⟨none, j⟩ = τ := by
  refine ⟨fun k i ↦ ?_, ?_⟩
  · have h := hf m hm (some k)
    rw [Pi.single_eq_of_ne (Option.some_ne_none k), Finset.sum_eq_zero_iff] at h
    exact h i (Finset.mem_univ _)
  · have h := hf m hm none
    rwa [Pi.single_eq_same] at h
end GroundTheory.Heights₂.Heights.YPlusSupSmall
