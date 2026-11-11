-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.geometricSupport_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:58:43.645204+00:00
-- url     : https://prove2.me/submissions/2bff3e08-cca7-4fe3-a65c-610b916294ec

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AvoidanceDensity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_finite_cap_support


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) {L : ℝ}
    (p : GeometricParameters L) : ∀ᵐ w ∂geometricLaw P p, w ∈ geometricSupport P p := by
  have hm : (0 : ℝ) < p.m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) p.m_two)
  have hl : (0 : ℝ) < p.lambda := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one p.lambda_one)
  have hmn : 0 < 6*p.m := by
    have hmN := p.m_two
    omega
  have hm6 : (0 : ℝ) < (6*p.m : ℕ) := by exact_mod_cast hmn
  exact finite_cap_support P (mul_pos hm6 hl) (capCutoff_bounds p.m_two).2
end QEC.Coding.BDL26RandomPerturbation
