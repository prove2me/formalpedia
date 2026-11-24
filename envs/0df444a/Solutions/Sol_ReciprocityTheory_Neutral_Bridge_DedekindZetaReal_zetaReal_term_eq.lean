-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.zetaReal_term_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:59.854909+00:00
-- url     : https://prove2.me/submissions/4e04ed77-6df3-4a32-8e05-ae760a636ac6

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
open ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
namespace ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
theorem _root_.solution {s : ℝ} (hs : 0 < s) (n : ℕ) :
    LSeries.term (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) (s : ℂ) n =
      (((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
  · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_neg, Complex.cpow_neg, div_eq_mul_inv]
    simp
end ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
