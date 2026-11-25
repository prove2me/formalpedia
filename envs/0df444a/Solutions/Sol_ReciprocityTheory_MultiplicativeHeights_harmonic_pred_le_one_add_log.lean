-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.harmonic_pred_le_one_add_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:19:06.082427+00:00
-- url     : https://prove2.me/submissions/63ed0191-cb7a-4707-bad0-1396ea8dafdf

import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_LogNormCoeffSubLeBlockSphereLogMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial NumberField
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ} (hn : 0 < n) : (harmonic (n - 1) : ℝ) ≤ 1 + Real.log n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := harmonic_le_one_add_log (m + 1)
  have h2 : harmonic (m + 1 - 1) ≤ harmonic (m + 1) := by
    have e : m + 1 - 1 = m := by omega
    rw [e, harmonic_succ]
    have : (0 : ℚ) ≤ (((m + 1 : ℕ) : ℚ))⁻¹ := by positivity
    linarith
  have h3 : (harmonic (m + 1 - 1) : ℝ) ≤ harmonic (m + 1) := by exact_mod_cast h2
  linarith
end ReciprocityTheory.MultiplicativeHeights
