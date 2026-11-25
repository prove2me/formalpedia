-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.mul_mem_grpN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:12:17.433566+00:00
-- url     : https://prove2.me/submissions/8fb16ab5-412a-4d51-9684-051ecac3473f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {F : ℕ → Submodule ℝ A} {L : ℕ} {f g : A → A}
variable [FiniteDimensional ℝ A]
variable {st : A →ₗ[ℝ] A}
omit [FiniteDimensional ℝ A]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution (hF : IsFil F L) (hst : IsAdj F st) {s g : A} (hs : s ∈ grpN F st)
    (hg : g ∈ grpN F st) : s * g ∈ grpN F st := by
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨hg1, hg2⟩ := hg
  show s * g - 1 ∈ F 0 ∧ st (s * g) * (s * g) = 1
  refine ⟨?_, ?_⟩
  · have e : s * g - 1 = (s - 1) * (g - 1) + (s - 1) + (g - 1) := by noncomm_ring
    rw [e]
    have h1 := hF.mul 0 0 _ _ hs1 hg1
    exact (F 0).add_mem ((F 0).add_mem (hF.anti 0 (0 + 0 + 1) (Nat.zero_le _) h1) hs1) hg1
  · rw [hst.mul]
    calc st g * st s * (s * g) = st g * (st s * s) * g := by simp only [mul_assoc]
      _ = 1 := by rw [hs2, mul_one, hg2]
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
