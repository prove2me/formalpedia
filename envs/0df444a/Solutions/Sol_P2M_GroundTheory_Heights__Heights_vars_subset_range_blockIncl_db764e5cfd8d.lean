-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_vars_subset_range_blockIncl_db764e5cfd8d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:41:01.042933+00:00
-- url     : https://prove2.me/submissions/4e61de68-8cd3-4b35-9a87-12115de0980b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VarsSubsetRangeBlockIncl

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (k₀ : ι) (m : ℕ) (f : MvPolynomial (Coord n) ℤ)
    (hf : IsWeightedHomogeneous (coordDeg n) f (m • Pi.single k₀ 1)) :
    (f.vars : Set (Coord n)) ⊆ Set.range (blockIncl k₀) := by
  classical
  intro v hv
  obtain ⟨d, hd, hdv⟩ := (mem_vars_iff_mem_support v).mp hv
  have hle : coordDeg n v ≤ Finsupp.weight (coordDeg n) d :=
    Finsupp.le_weight_of_ne_zero' (coordDeg n) (Finsupp.mem_support_iff.mp hdv)
  rw [hf (mem_support_iff.mp hd)] at hle
  have h1 := hle v.1
  obtain ⟨k, i⟩ := v
  by_cases hk : k = k₀
  · subst hk
    exact ⟨⟨(), i⟩, rfl⟩
  · simp [coordDeg, hk] at h1
end GroundTheory.Heights₂.Heights
