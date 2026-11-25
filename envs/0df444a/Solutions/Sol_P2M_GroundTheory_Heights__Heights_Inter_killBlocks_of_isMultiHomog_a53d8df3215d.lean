-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_killBlocks_of_isMultiHomog_a53d8df3215d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:34:29.917929+00:00
-- url     : https://prove2.me/submissions/5fca332c-4f28-4c75-a2c0-951e3246640e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UniquenessDegreeFormOfIntersectionForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_killBlocks_monomial_of_forall_a681e9d99ea6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_killBlocks_monomial_of_mem_58776ae9e633

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (S : Set K) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    killBlocks S f = f ∨ killBlocks S f = 0 := by
  by_cases ha : ∀ k ∈ S, a k = 0
  · left
    rw [f.as_sum, map_sum]
    refine Finset.sum_congr rfl fun m hm => killBlocks_monomial_of_forall S m _ ?_
    rintro ⟨k, i⟩ hp hkS
    have h1 := hf m hm k
    rw [ha k hkS] at h1
    have h2 : m ⟨k, i⟩ ≤ ∑ j, m ⟨k, j⟩ :=
      Finset.single_le_sum (f := fun j => m ⟨k, j⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact Finsupp.mem_support_iff.mp hp (by omega)
  · right
    push Not at ha
    obtain ⟨k, hkS, hak⟩ := ha
    rw [f.as_sum, map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    have h1 := hf m hm k
    obtain ⟨i, hi⟩ : ∃ i, m ⟨k, i⟩ ≠ 0 := by
      by_contra h0
      push Not at h0
      have : ∑ j, m ⟨k, j⟩ = 0 := Finset.sum_eq_zero fun j _ => h0 j
      omega
    exact killBlocks_monomial_of_mem S m _ ⟨k, i⟩ (Finsupp.mem_support_iff.mpr hi) hkS
end GroundTheory.Heights₂.Heights.Inter
