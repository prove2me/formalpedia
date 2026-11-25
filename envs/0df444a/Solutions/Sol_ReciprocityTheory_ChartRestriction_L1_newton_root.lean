-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.newton_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:46:47.063302+00:00
-- url     : https://prove2.me/submissions/f3a1f3b6-0cef-4b70-9a9c-7571d4570269

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_newton_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x₀ : K) (hx : ‖x₀‖ ≤ 1)
    (h0 : ‖P.eval x₀‖ < 1) (h1 : ‖P.derivative.eval x₀‖ = 1) :
    ∃ x : K, P.eval x = 0 ∧ ‖x - x₀‖ ≤ ‖P.eval x₀‖ := by
  set c : ℝ := ‖P.eval x₀‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  let S : Type := {x : K // ‖x‖ ≤ 1 ∧ ‖P.eval x‖ < 1 ∧ ‖P.derivative.eval x‖ = 1}
  have step : ∀ s : S, ∃ s' : S, ‖P.eval s'.1‖ ≤ ‖P.eval s.1‖ ^ 2 ∧
      ‖s'.1 - s.1‖ ≤ ‖P.eval s.1‖ := by
    intro s
    obtain ⟨y, hy, hy1, hy2, hy3⟩ := newton_step P hP s.1 s.2.1 s.2.2.1 s.2.2.2
    have : ‖P.eval y‖ < 1 :=
      lt_of_le_of_lt hy2 (pow_lt_one₀ (norm_nonneg _) s.2.2.1 two_ne_zero)
    exact ⟨⟨y, hy, this, hy1⟩, hy2, hy3⟩
  choose g hg1 hg2 using step
  let u : ℕ → S := fun n => Nat.rec ⟨x₀, hx, h0, h1⟩ (fun _ s => g s) n
  have hu0 : (u 0).1 = x₀ := rfl
  have hus : ∀ n, u (n + 1) = g (u n) := fun _ => rfl
  have hval : ∀ n, ‖P.eval (u n).1‖ ≤ c * c ^ n := by
    intro n
    induction n with
    | zero => rw [hu0, pow_zero, mul_one]
    | succ n ih =>
      have hle : ‖P.eval (u n).1‖ ≤ c :=
        ih.trans (mul_le_of_le_one_right hc0 (pow_le_one₀ hc0 h0.le))
      calc ‖P.eval (u (n + 1)).1‖ ≤ ‖P.eval (u n).1‖ ^ 2 := by rw [hus]; exact hg1 _
        _ = ‖P.eval (u n).1‖ * ‖P.eval (u n).1‖ := sq _
        _ ≤ (c * c ^ n) * c := mul_le_mul ih hle (norm_nonneg _) (by positivity)
        _ = c * c ^ (n + 1) := by ring
  have hdist : ∀ n, dist (u n).1 (u (n + 1)).1 ≤ c * c ^ n := by
    intro n
    rw [dist_comm, dist_eq_norm, hus]
    exact (hg2 _).trans (hval n)
  have hcau : CauchySeq (fun n => (u n).1) := cauchySeq_of_le_geometric c c h0 hdist
  obtain ⟨x, hxl⟩ := cauchySeq_tendsto_of_complete hcau
  have hnear : ∀ n, ‖(u n).1 - x₀‖ ≤ c := by
    intro n
    induction n with
    | zero => rw [hu0, sub_self, norm_zero]; exact hc0
    | succ n ih =>
      have h2 : ‖(u (n + 1)).1 - (u n).1‖ ≤ c := by
        rw [← dist_eq_norm, dist_comm]
        exact (hdist n).trans (mul_le_of_le_one_right hc0 (pow_le_one₀ hc0 h0.le))
      have := IsUltrametricDist.norm_add_le_max ((u (n + 1)).1 - (u n).1) ((u n).1 - x₀)
      rw [sub_add_sub_cancel] at this
      exact this.trans (max_le h2 ih)
  refine ⟨x, ?_, ?_⟩
  · have hl1 : Filter.Tendsto (fun n => P.eval (u n).1) Filter.atTop (nhds (P.eval x)) :=
      (P.continuous.tendsto x).comp hxl
    have hl2 : Filter.Tendsto (fun n => P.eval (u n).1) Filter.atTop (nhds 0) := by
      apply squeeze_zero_norm hval
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 h0).const_mul c
      rwa [mul_zero] at this
    exact tendsto_nhds_unique hl1 hl2
  · have hl : Filter.Tendsto (fun n => ‖(u n).1 - x₀‖) Filter.atTop (nhds ‖x - x₀‖) :=
      (hxl.sub_const x₀).norm
    exact le_of_tendsto' hl hnear
end ReciprocityTheory.ChartRestriction.L1
