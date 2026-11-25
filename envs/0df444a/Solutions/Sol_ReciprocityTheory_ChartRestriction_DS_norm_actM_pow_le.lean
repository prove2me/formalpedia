-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.norm_actM_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:04.54784+00:00
-- url     : https://prove2.me/submissions/5216a63b-5797-4dc8-99ad-1a162e70bc7b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Growth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_norm_actM_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_actM_pow_mem_layer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hV : IsKStableSub ε E V) {R d : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 ≤ ((R + √2 * k) ^ 2 - d) * ‖x‖ ^ 2)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (k : ℕ) {x : M} (hx : x ∈ layer ε E V k)
    (m : ℕ) :
    ‖((actM E X) ^ m) x‖ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) ^ m *
      (∏ l ∈ range m, (R + √(max 0 (-d)) + √2 * ((k : ℝ) + l))) * ‖x‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := norm_actM_le hR0 hR hX (k + m) (actM_pow_mem_layer hE hV hX hx m)
    have hc : 0 ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * (R + √(max 0 (-d)) + √2 * ((k + m : ℕ) : ℝ)) := by
      positivity
    calc _ ≤ _ := h
      _ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * (R + √(max 0 (-d)) + √2 * ((k + m : ℕ) : ℝ)) *
          (√(∑ a, ∑ b, ‖X a b‖ ^ 2) ^ m *
            (∏ l ∈ range m, (R + √(max 0 (-d)) + √2 * ((k : ℝ) + l))) * ‖x‖) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = _ := by
          rw [Finset.prod_range_succ, pow_succ]
          push_cast
          ring
end ReciprocityTheory.ChartRestriction.DS
