-- Prove2me | solution 1 for QEC.Coding.BDL26NativeHamiltonianLocality.extend_localCheck
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:46:30.714912+00:00
-- url     : https://prove2.me/submissions/08d4b99b-7cc4-4025-9ed4-da80c3db1ad9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_signedCheck_supported_ball
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_operatorSupportedOnRegister_iff_extend_restrict
import Theorems.Thm_QEC_Semantics_QuditSubsystem_operatorSupportedOnRegister_iff_extend_restrict


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeHamiltonianLocality
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open PauliSymplectic Semantics
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26NativeHamiltonianLocality
theorem _root_.solution (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : PhysicalGeometry S n J t) (j : Sum (ZLabel S n) (XLabel S n)) :
    (ballSubsystem S n J (checkCenter S n J j) 1).extendLocalToRegister
      (localCheck S n J j) = signedCheck S n j :=
  ((ballSubsystem S n J (checkCenter S n J j) 1).operatorSupportedOnRegister_iff_extend_restrict
    (signedCheck S n j)).mp (signedCheck_supported_ball S n J hJ j)
end QEC.Coding.BDL26NativeHamiltonianLocality
