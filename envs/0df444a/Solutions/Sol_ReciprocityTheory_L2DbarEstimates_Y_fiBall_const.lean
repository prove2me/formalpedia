-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fiBall_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:17:04.206592+00:00
-- url     : https://prove2.me/submissions/b9803caf-f9ab-4692-91ac-7a8df5764ce8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourIndep
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fiStep_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Set
open scoped Interval
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Ω : Set (Fin (n + 1) → ℝ)} {h : (Fin (n + 1) → ℂ) → ℂ}
    (hΩ : IsOpen Ω) (hh : DifferentiableOn ℂ h (tube (n + 1) Ω))
    (hper : ∀ s ∈ tube (n + 1) Ω, ∀ m : Fin (n + 1) → ℤ, h (s + fun k => (m k : ℂ)) = h s)
    (ν : Fin (n + 1) → ℤ) (b : Fin (n + 1) → ℝ) (hb : b ∈ Ω) :
    ∃ r > 0, ∀ c ∈ Metric.ball b r, fourCoeff h c ν = fourCoeff h b ν := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ b hb
  refine ⟨r, hr, ?_⟩
  have key : ∀ s : Finset (Fin (n + 1)), ∀ c ∈ Metric.ball b r, (∀ i ∉ s, c i = b i) →
      fourCoeff h c ν = fourCoeff h b ν := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro c _ hc
      have : c = b := funext fun i => hc i (Finset.notMem_empty i)
      rw [this]
    | insert a s ha ih =>
      intro c hcb hc
      have hcb' := hcb
      rw [Metric.mem_ball, dist_pi_lt_iff hr] at hcb'
      set c' := Function.update c a (b a) with hc'def
      have hc'b : c' ∈ Metric.ball b r := by
        rw [Metric.mem_ball, dist_pi_lt_iff hr]
        intro i
        by_cases hi : i = a
        · subst hi
          simp [c', hr]
        · simp [c', Function.update_of_ne hi, hcb' i]
      have hc'off : ∀ i ∉ s, c' i = b i := by
        intro i hi
        by_cases hia : i = a
        · subst hia
          simp [c']
        · simp only [c', Function.update_of_ne hia]
          exact hc i (by simp [hia, hi])
      have hseg : ∀ t ∈ Set.uIcc (c' a) (c a), Function.update c' a t ∈ Ω := by
        intro t ht
        apply hball
        have hca : c' a = b a := by simp [c']
        rw [hca] at ht
        rw [Metric.mem_ball, dist_pi_lt_iff hr]
        intro i
        by_cases hi : i = a
        · subst hi
          simp only [Function.update_self]
          have := hcb' i
          rw [Real.dist_eq] at this ⊢
          rw [abs_lt] at this ⊢
          rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
        · simp [c', Function.update_of_ne hi, hcb' i]
      have e : Function.update c' a (c a) = c := by simp [c']
      rw [← ih c' hc'b hc'off, fiStep_eq hh hper ν c' a (c a) hseg, e]
  intro c hc
  exact key Finset.univ c hc (by simp)
end ReciprocityTheory.L2DbarEstimates.Y
