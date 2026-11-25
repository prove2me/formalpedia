-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.XI.rpow_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:34.387978+00:00
-- url     : https://prove2.me/submissions/957f6d55-12e0-4d4b-b4f2-6f0ef3455f85

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GramReDetLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.XI
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS ReciprocityTheory.ChartRestriction.DS.Xi.GSB
namespace ReciprocityTheory.ChartRestriction.DS.Xi.XI
theorem _root_.solution (a b K s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 1 ≤ K) (hs : 0 ≤ s) (h1 : b ≤ K * a)
    (h2 : a ≤ K * b) : a ^ (-s) ≤ K ^ s * b ^ (-s) := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    have hb0 : b = 0 := le_antisymm (by simpa using h1) hb
    subst hb0
    have h3 : 1 ≤ K ^ s := Real.one_le_rpow hK hs
    have h4 : 0 ≤ (0:ℝ) ^ (-s) := Real.rpow_nonneg le_rfl _
    nlinarith
  · have hbpos : 0 < b := by
      by_contra hc
      push_neg at hc
      nlinarith
    rw [Real.rpow_neg ha, Real.rpow_neg hb]
    have hbs : b ^ s ≤ K ^ s * a ^ s := by
      rw [← Real.mul_rpow (by linarith) ha]
      exact Real.rpow_le_rpow hb h1 hs
    have hapos : 0 < a ^ s := Real.rpow_pos_of_pos hpos s
    have hbpos' : 0 < b ^ s := Real.rpow_pos_of_pos hbpos s
    rw [← div_eq_mul_inv, inv_eq_one_div]
    first
      | (rw [div_le_div_iff_of_pos hapos hbpos']; linarith)
      | (rw [div_le_div_iff₀ hapos hbpos']; linarith)
end ReciprocityTheory.ChartRestriction.DS.Xi.XI
