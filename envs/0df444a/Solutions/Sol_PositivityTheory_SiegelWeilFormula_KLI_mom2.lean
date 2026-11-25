-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KLI.mom2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:45.46847+00:00
-- url     : https://prove2.me/submissions/bc3b81d4-df02-4fe3-a365-1187c9a0fe4e

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_EvalMonomial2
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_eval_toMv
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_deg_toMv
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_eval_monomial2
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_intg_mono2
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_J_eq
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_pk_deg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex MvPolynomial
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KLI
namespace PositivityTheory.SiegelWeilFormula.KLI
theorem _root_.solution {b : ℂ} (hb : b.re < 0) (R : MvPolynomial (Fin 2) ℂ) :
    ∃ R' : MvPolynomial (Fin 2) ℂ, R'.totalDegree ≤ R.totalDegree ∧ ∀ l μ : ℂ,
      ∫ p : ℝ × ℝ, eval ![(p.1 : ℂ), (p.2 : ℂ)] R * G2 b l μ p = eval ![l, μ] R' * (J b 0 l * J b 0 μ) := by
  refine ⟨∑ v ∈ R.support, C (coeff v R) * (toMv 0 (pk b (v 0)) * toMv 1 (pk b (v 1))), ?_, fun l μ => ?_⟩
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun v hv => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_mul _ _).trans ?_
    refine le_trans ?_ (le_totalDegree hv)
    have h0 := (deg_toMv (0 : Fin 2) (pk b (v 0))).trans (pk_deg b (v 0))
    have h1 := (deg_toMv (1 : Fin 2) (pk b (v 1))).trans (pk_deg b (v 1))
    have hs : v.sum (fun _ e => e) = v 0 + v 1 := by
      rw [Finsupp.sum_fintype _ _ (by simp)]; simp [Fin.sum_univ_two]
    rw [hs]; omega
  · have e : (fun p : ℝ × ℝ => eval ![(p.1 : ℂ), (p.2 : ℂ)] R * G2 b l μ p) =
        fun p => ∑ v ∈ R.support, eval ![(p.1 : ℂ), (p.2 : ℂ)] (monomial v (coeff v R)) * G2 b l μ p := by
      funext p
      conv_lhs => rw [R.as_sum]
      rw [map_sum, Finset.sum_mul]
    rw [e, integral_finsetSum _ fun v _ => intg_mono2 hb l μ v _, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    have e2 : (fun p : ℝ × ℝ => eval ![(p.1 : ℂ), (p.2 : ℂ)] (monomial v (coeff v R)) * G2 b l μ p) =
        fun p => coeff v R * (((p.1 : ℂ) ^ v 0 * cexp (b * (p.1 : ℂ) ^ 2 + l * p.1)) *
          ((p.2 : ℂ) ^ v 1 * cexp (b * (p.2 : ℂ) ^ 2 + μ * p.2))) := by
      funext p; simp only [G2, eval_monomial2]; ring
    rw [e2, integral_const_mul]
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      integral_prod_mul (fun x : ℝ => (x : ℂ) ^ v 0 * cexp (b * (x : ℂ) ^ 2 + l * x))
        (fun y : ℝ => (y : ℂ) ^ v 1 * cexp (b * (y : ℂ) ^ 2 + μ * y))]
    have h0 := J_eq hb (v 0) l
    have h1 := J_eq hb (v 1) μ
    simp only [J] at h0 h1 ⊢
    rw [h0, h1]
    simp only [eval_mul, eval_C, eval_toMv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
end PositivityTheory.SiegelWeilFormula.KLI
