-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.bra_comp_ket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:47:07.346243+00:00
-- url     : https://prove2.me/submissions/d3f5abdc-8cb7-4394-8f3e-ff2a5c30f236

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
omit [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution (psi : H) (hpsi : ‖psi‖ ^ 2 = 1) :
    (bra psi).comp (ket psi) = 1 := by
  apply LinearMap.ext
  intro c
  change inner Complex psi (c • psi) = c
  have hnorm : (‖psi‖ : Complex) ^ 2 = 1 := by
    exact_mod_cast hpsi
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  calc
    c * (‖psi‖ : Complex) ^ 2 = c * 1 := congrArg (fun z : Complex => c * z) hnorm
    _ = c := mul_one c
end QEC.Semantics.DensityOperator
