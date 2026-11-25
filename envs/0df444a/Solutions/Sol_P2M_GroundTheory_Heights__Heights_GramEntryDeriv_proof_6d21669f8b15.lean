-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GramEntryDeriv_proof_6d21669f8b15
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:56:46.266547+00:00
-- url     : https://prove2.me/submissions/a3e34919-0d17-4e36-8a29-1d45dc0f67bb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PGramEntryDeriv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_comp_linearIsometry_45b19afbe74f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_triple_84a0c6a2690f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_mul_three_le_mul_three_6941116cc9a5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open MCGramEntryDeriv
namespace GroundTheory.Heights₂.Heights
namespace GramEntryDeriv
theorem _root_.solution : GramEntryDeriv.Statement := by
  intro E _ _ g k F Z p a e e' hF hZ j l
  have hent : ∀ q, ((F q)ᴴ * (Z q).map (fun x : ℝ => (x : ℂ)) * F q) j l =
      ∑ t, ∑ s, star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l := by
    intro q
    simp [Matrix.mul_apply, Finset.sum_mul]
  have hfun : (fun q => ((F q)ᴴ * (Z q).map (fun x : ℝ => (x : ℂ)) * F q) j l) =
      fun q => ∑ t, ∑ s, star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l := funext hent
  rw [hfun, hent p]
  have hterm : ∀ t s : Fin g,
      DifferentiableAt ℝ (fun q => star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l) p ∧
      ‖star (F p s j) * ((Z p s t : ℝ) : ℂ) * F p t l‖ ≤ a ^ 2 * e ∧
      ‖fderiv ℝ (fun q => star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l) p‖ ≤
        2 * a ^ 2 * e + a ^ 2 * e' := by
    intro t s
    obtain ⟨hd1, hn1, hD1⟩ := hF s j
    obtain ⟨hd3, hn3, hD3⟩ := hF t l
    obtain ⟨hd2, hn2, hD2⟩ := hZ s t
    obtain ⟨hu, hu'⟩ := comp_linearIsometry Complex.conjLIE.toLinearIsometry
      (fun z : ℂ => star z) (fun z => rfl) hd1
    obtain ⟨hv, hv'⟩ := comp_linearIsometry Complex.ofRealLI
      (fun x : ℝ => (x : ℂ)) (fun x => rfl) hd2
    obtain ⟨hdiff, hbound⟩ := triple hu hv hd3
    have hnu : ‖star (F p s j)‖ ≤ a := by rw [norm_star]; exact hn1
    have hnv : ‖((Z p s t : ℝ) : ℂ)‖ ≤ e := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hn2
    have hDu : ‖fderiv ℝ (fun q => star (F q s j)) p‖ ≤ a := hu'.le.trans hD1
    have hDv : ‖fderiv ℝ (fun q => ((Z q s t : ℝ) : ℂ)) p‖ ≤ e' := hv'.le.trans hD2
    refine ⟨hdiff, ?_, ?_⟩
    · rw [norm_mul, norm_mul]
      calc ‖star (F p s j)‖ * ‖((Z p s t : ℝ) : ℂ)‖ * ‖F p t l‖ ≤ a * e * a :=
            mul_three_le_mul_three (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hnu hnv hn3
        _ = a ^ 2 * e := by ring
    · refine hbound.trans ?_
      have b1 := mul_three_le_mul_three (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hDu hnv hn3
      have b2 := mul_three_le_mul_three (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hnu hDv hn3
      have b3 := mul_three_le_mul_three (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hnu hnv hD3
      nlinarith
  have hH : HasFDerivAt (fun q => ∑ t, ∑ s, star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l)
      (∑ t, ∑ s, fderiv ℝ (fun q => star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l) p) p :=
    HasFDerivAt.fun_sum fun t _ => HasFDerivAt.fun_sum fun s _ => (hterm t s).1.hasFDerivAt
  refine ⟨hH.differentiableAt, ?_, ?_⟩
  · calc ‖∑ t, ∑ s, star (F p s j) * ((Z p s t : ℝ) : ℂ) * F p t l‖
          ≤ ∑ t : Fin g, ∑ s : Fin g, ‖star (F p s j) * ((Z p s t : ℝ) : ℂ) * F p t l‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => norm_sum_le _ _)
      _ ≤ ∑ t : Fin g, ∑ s : Fin g, a ^ 2 * e :=
            Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun s _ => (hterm t s).2.1
      _ = (g : ℝ) ^ 2 * a ^ 2 * e := by simp [Finset.sum_const]; ring
  · rw [hH.fderiv]
    calc ‖∑ t, ∑ s, fderiv ℝ (fun q => star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l) p‖
          ≤ ∑ t : Fin g, ∑ s : Fin g,
              ‖fderiv ℝ (fun q => star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l) p‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => norm_sum_le _ _)
      _ ≤ ∑ t : Fin g, ∑ s : Fin g, (2 * a ^ 2 * e + a ^ 2 * e') :=
            Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun s _ => (hterm t s).2.2
      _ = (g : ℝ) ^ 2 * (2 * a ^ 2 * e + a ^ 2 * e') := by simp [Finset.sum_const]; ring
end GramEntryDeriv
end GroundTheory.Heights₂.Heights
