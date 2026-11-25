-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.Kf_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:19.440045+00:00
-- url     : https://prove2.me/submissions/f607c482-7b66-4bf0-b3bd-4344a767656d

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivPolyRealZero
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_PolyGaussOfLines
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_four_line

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
theorem _root_.solution {c : ℝ} (hc : 0 < c) (N : ℕ) (h : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (H : ∀ ξ : EuclideanSpace ℝ ι, ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ z : ℂ,
      ∫ u, h u * Real.exp (-(c * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ) =
        Complex.exp (z ^ 2 * ‖ξ‖ ^ 2 / (8 * c)) * p.eval z) (ξ : EuclideanSpace ℝ ι) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ t : ℝ, Kf c h (t • ξ) = p.eval (t : ℂ) := by
  obtain ⟨p, hp, hpz⟩ := H ξ
  refine ⟨p.comp (Polynomial.C (-2 * Real.pi * Complex.I) * Polynomial.X), ?_, fun t => ?_⟩
  · calc (p.comp (Polynomial.C (-2 * Real.pi * Complex.I) * Polynomial.X)).natDegree
        ≤ p.natDegree * (Polynomial.C (-2 * Real.pi * Complex.I) * Polynomial.X).natDegree :=
          Polynomial.natDegree_comp_le
      _ ≤ N * 1 := Nat.mul_le_mul hp ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)
      _ = N := mul_one N
  · have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have e : ((Real.pi ^ 2 / (2 * c) * ‖t • ξ‖ ^ 2 : ℝ) : ℂ) +
        (-2 * Real.pi * Complex.I * t) ^ 2 * ‖ξ‖ ^ 2 / (8 * c) = 0 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      push_cast
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [Kf, four_line, hpz, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add, e, Complex.exp_zero,
      one_mul, Polynomial.eval_comp]
    simp
end PositivityTheory.SiegelWeilFormula.KFPB
