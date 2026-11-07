-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.localLemma_conditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:42:37.203698+00:00
-- url     : https://prove2.me/submissions/3c0b473a-89c5-4ab6-9726-8f50d33b7a44

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_antitone
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_HasDependencyGraph_factor_avoid
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_union_lower
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (B : I → Set Ω) (hB : ∀ i, MeasurableSet (B i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
include hB
variable (G : SimpleGraph I) [DecidableRel G.Adj]
variable (hdep : HasDependencyGraph μ B G)
variable (hcrit : ∀ i, μ.real (B i) ≤ x i * ∏ j ∈ G.neighborFinset i, (1 - x j))
include hx0 hx1 hdep hcrit
namespace QEC.Coding.ProbabilisticConstruction
theorem _root_.solution (S : Finset I) (i : I) (hi : i ∉ S) :
    μ.real (B i ∩ avoid B S) ≤ x i * μ.real (avoid B S) := by
  induction S using Finset.strongInductionOn generalizing i with
  | _ S ih =>
    let T := S.filter (fun j => ¬ G.Adj i j)
    let U := S.filter (fun j => G.Adj i j)
    have hTU : T ∪ U = S := by ext j; simp [T, U]; tauto
    have hT : T ⊆ S := Finset.filter_subset _ _
    have hU : U ⊆ S := Finset.filter_subset _ _
    have hfactor := hdep.factor_avoid i T (by
      intro j hj
      have hj' := Finset.mem_filter.mp hj
      exact ⟨fun he => hi (he ▸ hj'.1), hj'.2⟩)
    have hext := avoid_union_lower μ B hB x hx1 T U (by
      intro A hA j hj hjA
      have hjU := Finset.mem_filter.mp hj
      have hsubset : T ∪ A ⊆ S := Finset.union_subset hT (hA.trans hU)
      have hjnot : j ∉ T ∪ A := by
        simp only [Finset.mem_union, not_or]
        exact ⟨fun hjT => (Finset.mem_filter.mp hjT).2 hjU.2, hjA⟩
      have hstrict : T ∪ A ⊂ S :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, fun he => hjnot (he.symm ▸ hjU.1)⟩
      exact ih (T ∪ A) hstrict j hjnot)
    rw [hTU] at hext
    have hprod : (∏ j ∈ G.neighborFinset i, (1 - x j)) ≤ ∏ j ∈ U, (1 - x j) := by
      apply Finset.prod_le_prod_of_subset_of_le_one
      · intro j hj
        simpa using (Finset.mem_filter.mp hj).2
      · intro j hj; exact sub_nonneg.mpr (hx1 j).le
      · intro j hj hjU; linarith [hx0 j]
    have hbound : μ.real (B i) ≤ x i * ∏ j ∈ U, (1 - x j) :=
      (hcrit i).trans (mul_le_mul_of_nonneg_left hprod (hx0 i))
    calc
      μ.real (B i ∩ avoid B S) ≤ μ.real (B i ∩ avoid B T) :=
        measureReal_mono (fun _ hω => ⟨hω.1, avoid_antitone B hT hω.2⟩)
      _ = μ.real (B i) * μ.real (avoid B T) := hfactor
      _ ≤ (x i * ∏ j ∈ U, (1 - x j)) * μ.real (avoid B T) :=
        mul_le_mul_of_nonneg_right hbound measureReal_nonneg
      _ ≤ x i * μ.real (avoid B S) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hext (hx0 i)
end QEC.Coding.ProbabilisticConstruction
