-- Prove2me | solution 1 for QEC.Coding.BDL26NativeDaviesLocality.extend_localJump
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:45:45.759974+00:00
-- url     : https://prove2.me/submissions/5b13f7ba-baa9-4b61-8449-28da7a01fbfd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeDaviesLocality
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_weightedJump_supported
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_weightedJump_supported
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
theorem _root_.solution (S : OddScale) (n : ℕ)
    (rate : CouplingIndex S n → Frequency S n → ℝ)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : Frequency S n) :
    (subsystem S n q).extendLocalToRegister (localJump S n rate q a ω) =
      hamiltonianJump (hamiltonian S n) (hamiltonian_symmetric S n)
        (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω) :=
  ((subsystem S n q).operatorSupportedOnRegister_iff_extend_restrict _).mp
    (weightedJump_supported S n rate q a ω)
end QEC.Coding.BDL26NativeDaviesLocality
