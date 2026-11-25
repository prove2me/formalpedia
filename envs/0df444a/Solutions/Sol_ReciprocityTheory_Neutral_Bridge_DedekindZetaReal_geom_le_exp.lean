-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.geom_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:32:03.690535+00:00
-- url     : https://prove2.me/submissions/89302a00-6454-472a-aa4d-ec7974ec3d63

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open NumberField IsDedekindDomain Filter Topology
variable (K : Type*) [Field K] [NumberField K]
open DedekindZetaReal
open ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
namespace ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
theorem _root_.solution {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) (B : ℕ) :
    ∑ k ∈ Finset.range (B + 1), x ^ k ≤ Real.exp (2 * x) := by
  have hg := geom_sum_Ico_le_of_lt_one (m := 0) (n := B + 1) h0 (by linarith)
  rw [← Finset.range_eq_Ico, pow_zero] at hg
  have h2 : 1 / (1 - x) ≤ 1 + 2 * x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith [Real.add_one_le_exp (2 * x)]
end ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
