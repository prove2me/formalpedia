-- Prove2me | solution 1 for QEC.Coding.BDL26QubitBallBounds.large_parameters_exist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:38:46.942605+00:00
-- url     : https://prove2.me/submissions/b27abf7e-3623-45dd-9ea7-bd998ac8896a

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Theorems.Thm_QEC_Coding_BDL26QubitBallBounds_enlarged_scale_large
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricParameters_nonempty


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26QubitBallBounds
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26CSSHamiltonian
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26QubitBallBounds
theorem _root_.solution (L : ℝ) :
    ∃ p : GeometricParameters L, 33 ≤ (perturbationOddScale p).ell := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  exact ⟨enlargeScale p,enlarged_scale_large p⟩
end QEC.Coding.BDL26QubitBallBounds
