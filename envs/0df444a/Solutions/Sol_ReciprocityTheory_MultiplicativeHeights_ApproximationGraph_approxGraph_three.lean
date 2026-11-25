-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.approxGraph_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:46:29.356307+00:00
-- url     : https://prove2.me/submissions/b2832a40-d6f3-41e7-b222-66e09094cc79

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphB
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_jForm_span_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_pos_small_of_orth
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_euc_add
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_graph_bound
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_jForm_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_jForm_self
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_negPart_add
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_negSq_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_normSq_split
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_posPart_add
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_posSq_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
open ComplexConjugate
private theorem exists_coeffs_of_mem_span_lemma {r p : ℕ} (X : Fin r → Fin r → ℂ) {u : Fin r → ℂ}
    (hu : u ∈ Submodule.span ℂ (X '' {j | (j : ℕ) < p})) :
    ∃ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) ∧ u = ∑ j, w j • X j := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨(Pi.single j 1 : Fin r → ℂ), fun k hk => ?_, ?_⟩
    · have hkj : k ≠ j := fun h => by subst h; exact (not_lt.mpr hk) hj
      simp [hkj]
    · rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
      simp
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    refine ⟨a + b, fun j hj => by simp [ha j hj, hb j hj], ?_⟩
    simp [add_smul, Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨c • a, fun j hj => by simp [ha j hj], ?_⟩
    simp [Finset.smul_sum, smul_smul]
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
open ComplexConjugate
namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
theorem _root_.solution {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (v y : Fin r → ℂ) (hy : ∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0)
    (hvy : v - y ∈ Submodule.span ℂ (X '' {j | (j : ℕ) < p})) :
    ‖jForm p y y‖ ≤ 2 * normSq v := by
  obtain ⟨w, hw, hu⟩ := exists_coeffs_of_mem_span_lemma X hvy
  have hv : v = y + ∑ j, w j • X j := by rw [← hu]; abel
  have h0 : ReciprocityTheory.MultiplicativeHeights.jForm p (∑ j, w j • X j) y = 0 := jForm_span_zero p X y hy w hw
  have hb := (graph_bound X hμ hρ hρ1 hX w hw).1
  have hs := pos_small_of_orth X hμ hρ hρ1 hX y hy
  rw [jForm_eq, sub_eq_zero] at h0
  have hre : RCLike.re (inner ℂ (euc (posPart p y))
        (euc (posPart p (∑ j, w j • X j)))) =
      RCLike.re (inner ℂ (euc (negPart p y)) (euc (negPart p (∑ j, w j • X j)))) := by
    rw [inner_re_symm, h0, inner_re_symm]
  have hI := (RCLike.abs_re_le_norm (inner ℂ (euc (negPart p y))
    (euc (negPart p (∑ j, w j • X j))))).trans (norm_inner_le_norm _ _)
  rw [jForm_self, Complex.norm_real, Real.norm_eq_abs, normSq_split p v, posSq_eq,
    posSq_eq, negSq_eq, negSq_eq, hv, posPart_add, negPart_add, euc_add,
    euc_add, norm_add_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), hre]
  have hPy := norm_nonneg (euc (posPart p y))
  have hNy := norm_nonneg (euc (negPart p y))
  have hPu := norm_nonneg (euc (posPart p (∑ j, w j • X j)))
  have hNu := norm_nonneg (euc (negPart p (∑ j, w j • X j)))
  have hk : ρ / 3 ≤ 1 / 3 := by linarith
  have hs' : ‖euc (posPart p y)‖ ≤ ‖euc (negPart p y)‖ / 3 :=
    hs.trans (by nlinarith)
  have hb' : ‖euc (negPart p (∑ j, w j • X j))‖ ≤
      ‖euc (posPart p (∑ j, w j • X j))‖ / 3 :=
    hb.trans (by nlinarith)
  have hI' := (abs_le.mp hI).1
  have ha : ‖euc (posPart p y)‖ ^ 2 ≤ ‖euc (negPart p y)‖ ^ 2 := by nlinarith
  have hc : ‖euc (negPart p y)‖ * ‖euc (negPart p (∑ j, w j • X j))‖ ≤
      ‖euc (negPart p y)‖ * (‖euc (posPart p (∑ j, w j • X j))‖ / 3) :=
    mul_le_mul_of_nonneg_left hb' hNy
  rw [abs_le]
  constructor <;>
    nlinarith [sq_nonneg (‖euc (posPart p (∑ j, w j • X j))‖ -
      2 / 3 * ‖euc (negPart p y)‖), sq_nonneg ‖euc (posPart p y)‖,
      sq_nonneg ‖euc (negPart p (∑ j, w j • X j))‖, sq_nonneg ‖euc (negPart p y)‖]
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
