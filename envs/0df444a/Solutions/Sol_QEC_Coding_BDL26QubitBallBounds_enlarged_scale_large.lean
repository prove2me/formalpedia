-- Prove2me | solution 1 for QEC.Coding.BDL26QubitBallBounds.enlarged_scale_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:30:12.036124+00:00
-- url     : https://prove2.me/submissions/63c62fd5-3f6a-4348-be80-81f4c3f1f039

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_perturbationOddScale_bounds


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26QubitBallBounds
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26CSSHamiltonian
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26QubitBallBounds
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) :
    33 ≤ (perturbationOddScale (enlargeScale p)).ell := by
  have bound := (perturbationOddScale_bounds (enlargeScale p)).1
  have hm : (2 : ℝ) ≤ (enlargeScale p).m := by exact_mod_cast (enlargeScale p).m_two
  have hl : (2 : ℝ) ≤ (enlargeScale p).lambda := by
    change (2 : ℝ) ≤ (max p.lambda 2 : Nat)
    exact_mod_cast le_max_right p.lambda 2
  have base : (25 : ℝ) ≤ 2*(6*((enlargeScale p).m : ℝ))+1 := by linarith
  have product : (49 : ℝ) ≤
      (2*(6*((enlargeScale p).m : ℝ))+1)*((enlargeScale p).lambda : ℝ) := by
    calc
      (49 : ℝ) ≤ 25*2 := by norm_num
      _ ≤ _ := mul_le_mul base hl (by norm_num) (by positivity)
  have actual : (33 : ℝ) ≤ (perturbationOddScale (enlargeScale p)).ell := by linarith
  exact_mod_cast actual
end QEC.Coding.BDL26QubitBallBounds
