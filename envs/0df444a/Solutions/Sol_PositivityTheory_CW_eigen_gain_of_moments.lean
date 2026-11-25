-- Prove2me | solution 1 for PositivityTheory.CW.eigen_gain_of_moments
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:26.791905+00:00
-- url     : https://prove2.me/submissions/9cc47aef-fabc-43c0-b4e6-8aa572fbfa7a

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisFormSumOfGain
import Theorems.Thm_PositivityTheory_CW_EigenGainPolynomial_re_inner_self
import Theorems.Thm_PositivityTheory_CW_EigenGainPolynomial_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
namespace PositivityTheory.CW
theorem _root_.solution : A0 → A8 → A9 → A10 → FunctionalCalculusLaws → A12 := by
  intro h0 h8 h9 h10 h11 n ε V _ _ E hM ι b μ hB κ hκ c hc
  obtain ⟨-, -, -, hnorm⟩ := h0 n ε V E hM
  obtain ⟨c0, x1, hc0, h8'⟩ := h8 n ε V E hM
  obtain ⟨C, hC, h9'⟩ := h9 n ε V E hM
  obtain ⟨-, hsym, hmono, hadd, hmul, hconst, hid⟩ := h11 n ε V E hM ι b μ hB
  obtain ⟨cs, hcs, h10'⟩ := h10 (⌈4 * (C + c + 1) / c0⌉₊ + 1) (by omega)
  refine ⟨⌈4 * (C + c + 1) / c0⌉₊ + 1, max 0 (max x1 (cs * C)), by omega, le_max_left _ _, ?_⟩
  intro ν v hν hv
  have hν0 : 0 ≤ ν := le_trans (le_max_left _ _) hν
  have hνx : x1 ≤ ν := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hν
  have hνc : cs * C ≤ ν := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hν
  have hsC : c + 1 ≤ ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) ^ 2 * c0 / 4
      - ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) * C := by
    have hce := Nat.le_ceil (4 * (C + c + 1) / c0)
    have hsc : 4 * (C + c + 1) ≤ ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) * c0 := by
      have := (div_le_iff₀ hc0).1 hce
      push_cast
      nlinarith
    have hs1 : (1 : ℝ) ≤ ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈4 * (C + c + 1) / c0⌉₊]
    nlinarith
  have hv' : casimirK ε E v = (ν : ℂ) • v := hv
  have hE : ∑ p ∈ nc ε, ‖E p.1 p.2 v‖ ^ 2 = (ν - κ) * ‖v‖ ^ 2 := by
    rw [(hnorm κ hκ v).2.1, hv', inner_smul_right, Complex.re_ofReal_mul, EigenGainPolynomial.re_inner_self]
    ring
  obtain ⟨h9a, h9b⟩ := h9' ν v hν0 hv
  exact EigenGainPolynomial.main hsym hmono hadd hmul hconst hid κ c _ c0 C cs ν hc0 hC hcs hsC hν0 hνc v hv h10'
    hE (h8' ν v hνx hv) h9a h9b
end PositivityTheory.CW
