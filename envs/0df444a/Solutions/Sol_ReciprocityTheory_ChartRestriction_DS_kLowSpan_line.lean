-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kLowSpan_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:45:51.462523+00:00
-- url     : https://prove2.me/submissions/359208c6-7d03-413c-9001-570409438784

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lowWord_wt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lowWt_ne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section Straight
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
end Straight
section Unitary
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
private lemma inner_eq_zero_of_distinct_weights (hU : IsInfUnitary ε E) {μ ν : Fin n → ℝ} {u v : M}
    (hu : ∀ a, E a a u = (μ a : ℂ) • u) (hv : ∀ a, E a a v = (ν a : ℂ) • v) (hne : ν ≠ μ) :
    inner ℂ u v = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  have h := hU a a u v
  have hs : adjSign ε a a = 1 := by simp [adjSign]
  rw [hu a, hv a, inner_smul_left, inner_smul_right, hs, one_mul, Complex.conj_ofReal] at h
  have h3 : ((μ a : ℂ) - (ν a : ℂ)) * inner ℂ u v = 0 := by rw [sub_mul, h, sub_self]
  have h5 : (μ a : ℂ) - (ν a : ℂ) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast Ne.symm ha
  exact (mul_eq_zero.mp h3).resolve_left h5
end Unitary
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E) {μ : Fin n → ℝ} {y : M}
    (hy : IsKHWVec ε E μ y) (hy0 : y ≠ 0) {z : M} (hz : z ∈ kLowSpan ε E y)
    (hzw : ∀ a, E a a z = (μ a : ℂ) • z) : ∃ c : ℂ, z = c • y := by
  have hy' : (∀ a, E a a y = (μ a : ℂ) • y) ∧ ∀ a b, a < b → ε a = ε b → E a b y = 0 := hy
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℂ M, W = Submodule.span ℂ
      {x | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) ∧ l ≠ [] ∧ x = lowWord E y l} := ⟨_, rfl⟩
  have hle : kLowSpan ε E y ≤ Submodule.span ℂ {y} ⊔ W := by
    unfold kLowSpan
    rw [Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    rcases l with _ | ⟨p, l⟩
    · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self y)
    · apply Submodule.mem_sup_right
      rw [hW]
      exact Submodule.subset_span ⟨p :: l, hl, List.cons_ne_nil _ _, rfl⟩
  have horth : ∀ u : M, (∀ a, E a a u = (μ a : ℂ) • u) → ∀ g ∈ W, inner ℂ u g = 0 := by
    intro u hu g hg
    have hWle : W ≤ (Submodule.span ℂ {u})ᗮ := by
      rw [hW, Submodule.span_le]
      rintro _ ⟨l, hl, hne, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact inner_eq_zero_of_distinct_weights hU hu (lowWord_wt hE hy'.1 l) (lowWt_ne hl hne)
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hWle hg)
  obtain ⟨y', hy'', w, hw, hzw'⟩ := Submodule.mem_sup.mp (hle hz)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy''
  have h1 := horth z hzw w hw
  have h2 := horth y hy'.1 w hw
  have hww : inner ℂ w w = 0 := by
    calc inner ℂ w w = inner ℂ (z - c • y) w := by rw [← hzw', add_sub_cancel_left]
      _ = 0 := by rw [inner_sub_left, inner_smul_left, h1, h2, mul_zero, sub_zero]
  have hw0 : w = 0 := inner_self_eq_zero.mp hww
  exact ⟨c, by rw [← hzw', hw0, add_zero]⟩
end ReciprocityTheory.ChartRestriction.DS
