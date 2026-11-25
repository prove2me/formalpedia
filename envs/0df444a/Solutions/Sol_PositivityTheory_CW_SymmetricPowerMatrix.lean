-- Prove2me | solution 1 for PositivityTheory.CW.SymmetricPowerMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:24.448566+00:00
-- url     : https://prove2.me/submissions/e87e21c7-cd34-4130-86cb-9920cf18a5d0

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EnvelopingAlgebraGrowthBound
import Theorems.Thm_PositivityTheory_CW_IdentityFiltrationBound_mem_W
import Theorems.Thm_PositivityTheory_CW_IdentityFiltrationBound_N_nonneg
import Theorems.Thm_PositivityTheory_CW_IdentityFiltrationBound_U_bound
import Theorems.Thm_PositivityTheory_CW_IdentityFiltrationBound_step

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
open IdentityFiltrationBound
namespace PositivityTheory.CW
theorem _root_.solution : A0 → A1 → CasimirIsRealScalar → A6 := by
  intro h0 h1 h3 n ε V _ _ E hE
  obtain ⟨κ, hκ⟩ := h3 n ε V E hE
  obtain ⟨-, -, -, h0c⟩ := h0 n ε V E hE
  obtain ⟨hmono, -, -, -, hcomm, hK2, -⟩ := h1 n ε V E hE
  have hcas : ∀ w : V, ∑ a, ∑ b, ‖E a b w‖ ^ 2 = 2 * (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2 :=
    fun w => (h0c κ hκ w).1
  have grow : ∀ k : ℕ, ∃ G : ℝ, 0 ≤ G ∧ ∀ μ v, 0 ≤ μ → Eig ε E μ v →
      N E k v ≤ G * Real.sqrt (1 + μ) ^ k * ‖v‖ := by
    intro k
    induction k with
    | zero =>
      refine ⟨(W n 0).card, Nat.cast_nonneg _, fun μ v _ _ => ?_⟩
      simp only [pow_zero, mul_one]
      calc N E 0 v = ∑ l ∈ W n 0, ‖wd E l v‖ := rfl
        _ ≤ ∑ l ∈ W n 0, ‖v‖ := Finset.sum_le_sum fun l hl => by
            have := mem_W.1 hl
            cases l with
            | nil => simp [wd]
            | cons p l => simp at this
        _ = _ := by simp
    | succ k ih =>
      obtain ⟨G, hG, hG'⟩ := ih
      have hc : ∀ l : List (Fin n × Fin n), ∃ c : ℝ, 0 ≤ c ∧ (l.length ≤ k → ∀ v,
          ‖(casimirK ε E * wd E l - wd E l * casimirK ε E) v‖ ≤ c * N E (k + 1) v) := by
        intro l
        by_cases hl : l.length ≤ k
        · have hmem : wd E l ∈ U E k := hmono _ _ hl (Submodule.subset_span ⟨l, le_rfl, rfl⟩)
          have hin := hcomm 2 k _ hK2 _ hmem
          have h' : 2 + k - 1 = k + 1 := by omega
          rw [h'] at hin
          obtain ⟨c, hc, hc'⟩ := U_bound E (k + 1) _ hin
          exact ⟨c, hc, fun _ => hc'⟩
        · exact ⟨0, le_rfl, fun h => absurd h hl⟩
      choose c hc0 hc using hc
      have hC : ∀ l : List (Fin n × Fin n), l.length ≤ k → ∀ v,
          ‖(casimirK ε E * wd E l - wd E l * casimirK ε E) v‖ ≤ (∑ l ∈ W n k, c l) * N E (k + 1) v :=
        fun l hl v => (hc l hl v).trans (mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := c) (fun i _ => hc0 i) (mem_W.2 hl)) (N_nonneg _ _ _))
      have hC0 : 0 ≤ ∑ l ∈ W n k, c l := Finset.sum_nonneg fun i _ => hc0 i
      refine ⟨(2 * ((W n (k + 1)).card : ℝ) ^ 2 * (∑ l ∈ W n k, c l) +
        ((W n (k + 1)).card : ℝ) * Real.sqrt (2 + |κ|)) * G, by positivity, fun μ v hμ hv => ?_⟩
      have hst := step E ε κ μ _ k hcas hC0 hC v hv hμ
      calc N E (k + 1) v ≤ _ := hst
        _ ≤ (2 * ((W n (k + 1)).card : ℝ) ^ 2 * (∑ l ∈ W n k, c l) +
            ((W n (k + 1)).card : ℝ) * Real.sqrt (2 + |κ|)) * Real.sqrt (1 + μ) *
              (G * Real.sqrt (1 + μ) ^ k * ‖v‖) :=
          mul_le_mul_of_nonneg_left (hG' μ v hμ hv) (by positivity)
        _ = _ := by ring
  intro k u hu
  obtain ⟨c, hc, hc'⟩ := U_bound E k u hu
  obtain ⟨G, hG, hG'⟩ := grow k
  refine ⟨c * G, mul_nonneg hc hG, fun μ v hμ hv => ?_⟩
  calc ‖u v‖ ≤ c * N E k v := hc' v
    _ ≤ c * (G * Real.sqrt (1 + μ) ^ k * ‖v‖) := mul_le_mul_of_nonneg_left (hG' μ v hμ hv) hc
    _ = _ := by ring
end PositivityTheory.CW
