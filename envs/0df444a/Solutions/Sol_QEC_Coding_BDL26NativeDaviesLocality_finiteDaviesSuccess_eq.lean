-- Prove2me | solution 1 for QEC.Coding.BDL26NativeDaviesLocality.finiteDaviesSuccess_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:20:25.338202+00:00
-- url     : https://prove2.me/submissions/2b3564fd-d568-4a4e-8f02-88a3f4dc9aa8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeDaviesLocality
import Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_finiteSuccess_davies

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeDaviesLocality
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open BDL26CSSDaviesLocality
open PauliSymplectic Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26NativeDaviesLocality
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    finiteDaviesSuccess p N = BDL26NativeFiniteComposition.finiteSuccess p N := by
  ext z
  constructor
  · exact fun hz => hz.1
  · exact fun hz => ⟨hz, finiteSuccess_davies p N hz⟩
end QEC.Coding.BDL26NativeDaviesLocality
