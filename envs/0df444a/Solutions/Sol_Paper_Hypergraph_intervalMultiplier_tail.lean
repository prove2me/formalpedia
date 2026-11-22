-- Prove2me | solution 1 for Paper.Hypergraph.intervalMultiplier_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:32.689056+00:00
-- url     : https://prove2.me/submissions/3b5a2b0d-9129-4f9b-94c4-6d01f011672f

import Definitions.Def_Paper_TwoTerminalRounding
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Paper_RoundingAveraging
import Theorems.Thm_Paper_Hypergraph_levelMeasure_Icc_le

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open MeasureTheory Set
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution {V : Finset ℕ} (hne : V.Nonempty) {x d : ℕ → ℝ} {q : ℝ}
    (hq : ∀ v ∈ V, d v - x v ≤ q ∧ q ≤ d v) {t : ℝ} (ht : 0 < t) :
    levelMeasure.real {r | t ≤ intervalMultiplier V hne x d r} ≤ 2 / t := by
  have hsub : {r | t ≤ intervalMultiplier V hne x d r} ⊆ Icc (q - 1 / t) (q + 1 / t) := by
    intro r hr
    obtain ⟨v, hv, heq⟩ := Finset.exists_mem_eq_sup' hne (fun v => vertexMultiplier x d v r)
    change t ≤ V.sup' hne _ at hr
    rw [heq] at hr
    by_cases hrv : r ∈ Icc (d v - x v) (d v)
    swap
    · simp [vertexMultiplier, hrv] at hr
      linarith
    have hsmall : t ≤ 1 / x v := by simpa [vertexMultiplier, hrv] using hr
    have hxv : 0 < x v := one_div_pos.mp (ht.trans_le hsmall)
    have hxt : x v ≤ 1 / t := (le_div_iff₀ ht).2 (by
      have := (le_div_iff₀ hxv).1 hsmall
      nlinarith)
    have hqv := hq v hv
    exact ⟨by linarith [hrv.1, hrv.2], by linarith [hrv.1, hrv.2]⟩
  calc
    _ ≤ levelMeasure.real (Icc (q - 1 / t) (q + 1 / t)) := measureReal_mono hsub
    _ ≤ max ((q + 1 / t) - (q - 1 / t)) 0 := levelMeasure_Icc_le _ _
    _ = 2 / t := by
      have hn : 0 ≤ (q + 1 / t) - (q - 1 / t) := by linarith [one_div_pos.mpr ht]
      rw [max_eq_left hn]
      ring
end Paper.Hypergraph
