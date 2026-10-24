-- Prove2me | solution 1 for OnlineMaxWeightMatch.Approx.proposition_2_7_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T15:04:01.052558+00:00
-- url     : https://prove2.me/submissions/bdb99d1e-f887-4ed8-8f04-940ad76b2f45

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_NegativelyAssociated

open MeasureTheory ProbabilityTheory

open OnlineMaxWeightMatch.Approx in
theorem solution {Ω κ ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : κ → Ω → ℝ) (hX : NegativelyAssociated X μ)
    (S : ι → Finset κ) (hS : Pairwise fun j k => Disjoint (S j) (S k))
    (f : (j : ι) → (S j → ℝ) → ℝ) (hmono : ∀ j, Monotone (f j))
    (hmeas : ∀ j, Measurable (f j)) :
    NegativelyAssociated (fun j ω => f j (fun a => X a ω)) μ := by
  classical
  intro A B hAB F G hF hG hFm hGm hFb hGb
  -- the composite test functions on the unions of the index sets
  let UA : Finset κ := A.biUnion S
  let UB : Finset κ := B.biUnion S
  have memA : ∀ (j : A) (a : S j), (a : κ) ∈ UA := fun j a =>
    Finset.mem_biUnion.mpr ⟨j, j.2, a.2⟩
  have memB : ∀ (j : B) (a : S j), (a : κ) ∈ UB := fun j a =>
    Finset.mem_biUnion.mpr ⟨j, j.2, a.2⟩
  let F' : (UA → ℝ) → ℝ := fun y => F (fun j => f j (fun a => y ⟨a, memA j a⟩))
  let G' : (UB → ℝ) → ℝ := fun y => G (fun j => f j (fun a => y ⟨a, memB j a⟩))
  have hdisj : Disjoint UA UB := by
    rw [Finset.disjoint_biUnion_left]
    intro j hj
    rw [Finset.disjoint_biUnion_right]
    intro k hk
    have hjk : j ≠ k := by
      rintro rfl
      exact Finset.disjoint_left.mp hAB hj hk
    exact hS hjk
  have hF'm : Monotone F' := by
    intro y y' hyy
    apply hF
    intro j
    apply hmono
    intro a
    exact hyy _
  have hG'm : Monotone G' := by
    intro y y' hyy
    apply hG
    intro j
    apply hmono
    intro a
    exact hyy _
  have hF'meas : Measurable F' := by
    apply hFm.comp
    apply measurable_pi_lambda
    intro j
    apply (hmeas j).comp
    apply measurable_pi_lambda
    intro a
    exact measurable_pi_apply _
  have hG'meas : Measurable G' := by
    apply hGm.comp
    apply measurable_pi_lambda
    intro j
    apply (hmeas j).comp
    apply measurable_pi_lambda
    intro a
    exact measurable_pi_apply _
  have hF'b : ∃ C : ℝ, ∀ y, |F' y| ≤ C := by
    obtain ⟨C, hC⟩ := hFb; exact ⟨C, fun y => hC _⟩
  have hG'b : ∃ C : ℝ, ∀ y, |G' y| ≤ C := by
    obtain ⟨C, hC⟩ := hGb; exact ⟨C, fun y => hC _⟩
  exact hX UA UB hdisj F' G' hF'm hG'm hF'meas hG'meas hF'b hG'b
