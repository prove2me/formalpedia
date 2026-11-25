-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.norm_le_one_of_monic_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:21:20.405602+00:00
-- url     : https://prove2.me/submissions/ee9bb675-d512-409b-ba5a-83195b0bbefe

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Inertia
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelC
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_norm_add_le_max_padic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
attribute [local instance] locRel
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (P : Polynomial (PadicAlgCl p)) (hP : P.Monic) (hc : ∀ i, ‖P.coeff i‖ ≤ 1)
    {x : PadicAlgCl p} (hx : P.eval x = 0) : ‖x‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have key : ∀ m, ‖∑ i ∈ Finset.range (m + 1), P.coeff i * x ^ i‖ ≤ ‖x‖ ^ m := by
    intro m
    induction m with
    | zero => simpa using hc 0
    | succ m ih =>
      rw [Finset.sum_range_succ]
      refine (norm_add_le_max_padic _ _).trans (max_le ?_ ?_)
      · exact ih.trans (pow_le_pow_right₀ hlt.le (Nat.le_succ m))
      · rw [norm_mul, norm_pow]
        calc ‖P.coeff (m + 1)‖ * ‖x‖ ^ (m + 1) ≤ 1 * ‖x‖ ^ (m + 1) := by gcongr; exact hc _
          _ = ‖x‖ ^ (m + 1) := one_mul _
  have he := P.eval_eq_sum_range (x := x)
  rw [hx] at he
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hpos
  · rw [h0] at he
    simp [hP.coeff_natDegree ▸ (show P.coeff 0 = P.coeff P.natDegree by rw [h0])] at he
  · obtain ⟨m, hm⟩ : ∃ m, P.natDegree = m + 1 := ⟨P.natDegree - 1, by omega⟩
    rw [hm, Finset.sum_range_succ, ← hm, hP.coeff_natDegree, one_mul, hm] at he
    have e2 : x ^ (m + 1) = -∑ i ∈ Finset.range (m + 1), P.coeff i * x ^ i := by
      linear_combination -he
    have := key m
    rw [← norm_neg, ← e2, norm_pow] at this
    have h3 : ‖x‖ ^ m < ‖x‖ ^ (m + 1) := pow_lt_pow_right₀ hlt (Nat.lt_succ_self m)
    linarith
end ReciprocityTheory.Neutral.Cmp
