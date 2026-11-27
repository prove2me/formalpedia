-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isSupSmallBlock_one_ce57b19d901a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:12:21.964851+00:00
-- url     : https://prove2.me/submissions/a8b7e4ac-ec16-4f3b-b57b-bc82ab37a541

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading

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
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (n)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] {n' : κ → ℕ} {Ω : Type} [Field Ω]
    [CharZero Ω] (y : Coord n' → Ω) (k₀ : κ) (A : Geo.HermLine (blockIdx n')) :
    (1 : Ω) ∈ Geo.secM (ι := blockIdx n') y (Pi.single k₀ 0) ∧ IsSupSmallBlock y k₀ A 0 1 := by
  have hz : ∀ f : MvPolynomial (Coord n') ℤ, Geo.IsMultiHomog (ι := blockIdx n') f (Pi.single k₀ 0) →
      f = C (coeff 0 f) := by
    intro f hf
    ext m
    rw [coeff_C]
    split_ifs with h0
    · rw [h0]
    · by_contra hc
      refine h0 (Finsupp.ext fun p ↦ ?_).symm
      have h := hf m (mem_support_iff.mpr hc) p.1
      rw [Pi.single_zero, Pi.zero_apply, Finset.sum_eq_zero_iff] at h
      exact h p.2 (Finset.mem_univ _)
  constructor
  · refine Submodule.subset_span ⟨1, fun m hm k ↦ ?_, map_one _⟩
    have hm0 : m = 0 := by
      by_contra h0
      exact (mem_support_iff.mp hm) (by rw [← C_1, coeff_C, if_neg (Ne.symm h0)])
    simp [hm0]
  · intro f hf hs z _
    rw [hz f hf] at hs ⊢
    have h1 : coeff 0 f = 1 := by
      rw [aeval_C] at hs
      exact_mod_cast (by simpa using hs : ((coeff 0 f : ℤ) : Ω) = 1)
    simp [h1]
end GroundTheory.Heights₂.Heights
