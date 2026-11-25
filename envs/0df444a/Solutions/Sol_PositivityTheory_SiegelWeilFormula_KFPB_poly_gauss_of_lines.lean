-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.poly_gauss_of_lines
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:27.255848+00:00
-- url     : https://prove2.me/submissions/133291d7-1e03-4641-8e6d-d1f1f930f145

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivPolyRealZero
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_PolyGaussOfLines
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_gW_cont
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_gW_int
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_four_eq
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_fourierInv_poly_gauss
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_integrable_poly_gauss


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap InnerProductSpace FourierTransform
open MeasureTheory
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.SiegelWeilFormula.KFPB
theorem _root_.solution (c : ℝ) (hc : 0 < c) (N : ℕ) (h : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (H : ∀ ξ : EuclideanSpace ℝ ι, ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ z : ℂ,
      ∫ u, h u * Real.exp (-(c * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ) =
        Complex.exp (z ^ 2 * ‖ξ‖ ^ 2 / (8 * c)) * p.eval z) :
    ∃ P : MvPolynomial ι ℂ, P.totalDegree ≤ N ∧
      ∀ u, h u = MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(c * ‖u‖ ^ 2)) := by
  obtain ⟨Q, hQ, hF⟩ := four_eq hc N h H
  have hb : 0 < Real.pi ^ 2 / (2 * c) := by positivity
  obtain ⟨Q', hQ', hinv⟩ := fourierInv_poly_gauss _ hb Q
  refine ⟨Q', hQ'.trans hQ, fun u => ?_⟩
  have hFeq : 𝓕 (gW c h) = fun η : EuclideanSpace ℝ ι => MvPolynomial.eval (fun i => ((η i : ℝ) : ℂ)) Q *
      (Real.exp (-(Real.pi ^ 2 / (2 * c) * ‖η‖ ^ 2)) : ℂ) := funext hF
  have hint : Integrable (𝓕 (gW c h)) := by
    rw [hFeq]
    exact integrable_poly_gauss _ hb Q
  have key := (gW_int hc.le h).fourierInv_fourier_eq hint (gW_cont c h).continuousAt (v := u)
  rw [hFeq, hinv] at key
  have h2 : Real.pi ^ 2 / (Real.pi ^ 2 / (2 * c)) = 2 * c := by
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [h2] at key
  unfold gW at key
  have hE : (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  apply mul_right_cancel₀ hE
  rw [← key, mul_assoc _ ((Real.exp (-(c * ‖u‖ ^ 2)) : ℂ)), ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring
end PositivityTheory.SiegelWeilFormula.KFPB
