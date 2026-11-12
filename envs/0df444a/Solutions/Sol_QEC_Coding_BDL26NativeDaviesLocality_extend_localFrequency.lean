-- Prove2me | solution 1 for QEC.Coding.BDL26NativeDaviesLocality.extend_localFrequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:45:30.719143+00:00
-- url     : https://prove2.me/submissions/ed3b36b3-7408-42b7-b599-1c9af4468b80

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeDaviesLocality
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_frequency_supported
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_frequency_supported
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_operatorSupportedOnRegister_iff_extend_restrict
import Theorems.Thm_QEC_Semantics_QuditSubsystem_operatorSupportedOnRegister_iff_extend_restrict


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
theorem _root_.solution (S : OddScale) (n : ℕ) (q : Physical S n)
    (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    (subsystem S n q).extendLocalToRegister (localFrequency S n q a ω) =
      actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω :=
  ((subsystem S n q).operatorSupportedOnRegister_iff_extend_restrict _).mp
    (frequency_supported S n q a ω)
end QEC.Coding.BDL26NativeDaviesLocality
