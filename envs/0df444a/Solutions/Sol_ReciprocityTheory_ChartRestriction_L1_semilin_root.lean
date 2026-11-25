-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.semilin_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:40:23.878697+00:00
-- url     : https://prove2.me/submissions/240ccd51-bdd9-4dd8-8f26-64d79bf1d3ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SemilinNormPowSubPow

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
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]
omit [CompleteSpace K] [CharZero K]
open Polynomial
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {l : ℕ} (hR : ResClosed K l) {m : ℕ} (hm : 2 ≤ m) (a b : K) (ha : ‖a‖ ≤ 1)
    (hb : ‖b‖ ≤ 1) : ∃ x : K, ‖x‖ ≤ 1 ∧ ‖x ^ m + a * x + b‖ ≤ ‖(l : K)‖ := by
  have hdeg : (C a * X + C b : K[X]).degree < (X ^ m : K[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt degree_linear_le (by exact_mod_cast hm)
  have hmon : (X ^ m + (C a * X + C b) : K[X]).Monic := monic_X_pow_add (by rwa [degree_X_pow] at hdeg)
  have hnat : (X ^ m + (C a * X + C b) : K[X]).natDegree = m := by
    rw [natDegree_add_eq_left_of_degree_lt hdeg, natDegree_X_pow]
  have hco : ∀ i, ‖(X ^ m + (C a * X + C b) : K[X]).coeff i‖ ≤ 1 := by
    intro i
    simp only [coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_))) <;> split_ifs <;> simp [ha, hb]
  obtain ⟨x, hx, hev⟩ := hR _ hmon (by omega) hco
  refine ⟨x, hx, ?_⟩
  simpa [add_assoc] using hev
end ReciprocityTheory.ChartRestriction.L1
