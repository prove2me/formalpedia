-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.fourierInv_poly_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:47.808775+00:00
-- url     : https://prove2.me/submissions/a4a582fc-ada2-4d7f-bdd6-4a2e90f5bae7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_circle_smul
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_integrable_mono
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_deg_rS
import Theorems.Thm_P2M_PositivityTheory_SiegelWeilFormula_KFPB_integral_mono__4b40e6adf110
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_eval_as_sum
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_J_eq
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_J_zero
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_intg_pow_quad
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
open scoped FourierTransform
open MeasureTheory Complex MvPolynomial
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
open PositivityTheory.SiegelWeilFormula.KLI (J pk J_eq J_zero intg_pow_quad pk_deg)
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.SiegelWeilFormula.KFPB
theorem _root_.solution {ι : Type} [Fintype ι] (b : ℝ) (hb : 0 < b) (Q : MvPolynomial ι ℂ) :
    ∃ Q' : MvPolynomial ι ℂ, Q'.totalDegree ≤ Q.totalDegree ∧ ∀ u : EuclideanSpace ℝ ι,
      𝓕⁻ (fun η : EuclideanSpace ℝ ι =>
          MvPolynomial.eval (fun i => ((η i : ℝ) : ℂ)) Q * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) u =
        MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) Q' * (Real.exp (-(Real.pi ^ 2 / b * ‖u‖ ^ 2)) : ℂ) := by
  refine ⟨∑ s ∈ Q.support, C (coeff s Q) * rS b s, ?_, fun u => ?_⟩
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (deg_rS b s).trans (le_totalDegree hs)
  · rw [Real.fourierInv_eq]
    have e : ∀ η : EuclideanSpace ℝ ι, 𝐞 (inner ℝ η u) •
        (eval (fun i => ((η i : ℝ) : ℂ)) Q * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) =
        ∑ s ∈ Q.support, coeff s Q * (𝐞 (inner ℝ η u) •
          (eval (fun i => ((η i : ℝ) : ℂ)) (monomial s (1 : ℂ)) * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ))) := by
      intro η
      rw [eval_as_sum, Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [circle_smul, circle_smul]
      ring
    simp_rw [e]
    rw [integral_finsetSum _ fun s _ => (integrable_mono hb s u).const_mul _]
    simp_rw [integral_const_mul, integral_mono' hb]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [eval_mul, eval_C]
    ring
end PositivityTheory.SiegelWeilFormula.KFPB
