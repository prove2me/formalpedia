-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.fiber_count_le_ncard_inter_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:14:11.49007+00:00
-- url     : https://prove2.me/submissions/efd09607-b96e-4cab-9801-2a9004f4d623

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_CountZSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_finite_inter_lattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Module
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (S : Set E) (hconv : Convex ℝ S) (hsymm : ∀ x ∈ S, -x ∈ S) (hb : Bornology.IsBounded S)
    (x : E) :
    ∑' g : L, ((g +ᵥ ((2⁻¹ : ℝ) • S)).indicator 1 x : ENNReal) ≤ ((S ∩ (L : Set E)).ncard : ENNReal) := by
  classical
  by_cases hx : ∃ g0 : L, x ∈ g0 +ᵥ ((2⁻¹ : ℝ) • S)
  swap
  · push_neg at hx
    simp [Set.indicator_of_notMem (hx _)]
  obtain ⟨g0, hg0⟩ := hx

  have key : ∀ g : L, x ∈ g +ᵥ ((2⁻¹ : ℝ) • S) → ((g : E) - g0) ∈ S := by
    intro g hg
    rw [Set.mem_vadd_set] at hg hg0
    obtain ⟨a, ha, hax⟩ := hg
    obtain ⟨c, hc, hcx⟩ := hg0
    rw [Set.mem_smul_set] at ha hc
    obtain ⟨s1, hs1, rfl⟩ := ha
    obtain ⟨s2, hs2, rfl⟩ := hc
    rw [Submodule.vadd_def, vadd_eq_add] at hax hcx
    have e : (g : E) - g0 = (2⁻¹ : ℝ) • s2 + (2⁻¹ : ℝ) • (-s1) := by
      rw [smul_neg, eq_sub_of_add_eq hax, eq_sub_of_add_eq hcx]; abel
    rw [e]
    exact hconv hs2 (hsymm s1 hs1) (by norm_num) (by norm_num) (by norm_num)
  have hfin : {g : L | ((g : E) - g0) ∈ S}.Finite := by
    have hinj : Function.Injective (fun g : L => (g : E) - g0) :=
      fun a b h => Subtype.ext (sub_left_injective h)
    refine ((finite_inter_lattice L S hb).preimage hinj.injOn).subset ?_
    intro g hg
    exact Set.mem_inter hg (sub_mem g.2 g0.2)
  rw [tsum_eq_sum (s := hfin.toFinset) (fun g hg => Set.indicator_of_notMem
    (fun h => hg (hfin.mem_toFinset.2 (key g h))) _)]
  calc ∑ g ∈ hfin.toFinset, ((g +ᵥ ((2⁻¹ : ℝ) • S)).indicator 1 x : ENNReal)
      ≤ ∑ g ∈ hfin.toFinset, (1 : ENNReal) := by
        refine Finset.sum_le_sum fun g _ => ?_
        unfold Set.indicator; split_ifs <;> simp
    _ = (hfin.toFinset.card : ENNReal) := by simp
    _ ≤ ((S ∩ (L : Set E)).ncard : ENNReal) := by
        rw [← Set.ncard_eq_toFinset_card _ hfin]
        have hh := Set.ncard_le_ncard_of_injOn (s := {g : L | ((g : E) - g0) ∈ S})
          (t := S ∩ (L : Set E)) (fun g : L => (g : E) - g0)
          (fun g hg => Set.mem_inter hg (sub_mem g.2 g0.2))
          (fun a _ b _ h => Subtype.ext (sub_left_injective h)) (finite_inter_lattice L S hb)
        exact_mod_cast hh
end ReciprocityTheory.GeometryOfNumbersTheory
