-- Prove2me | solution 1 for QEC.Distillation.BK05T.tCanonicalizedInput_tInputFidelity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:39:44.749079+00:00
-- url     : https://prove2.me/submissions/cef67517-c1f5-48cd-b1ef-da782ae21071

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Theorems.Thm_QEC_Distillation_BK05T_tCanonicalizer_conj_tProjector
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionFidelity_conjDensity
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tMaximizingDirection_attains


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
open scoped BigOperators
namespace QEC.Distillation.BK05T
theorem _root_.solution (rho : DensityOperator QubitSpace) :
    tInputFidelity (tCanonicalizedInput rho) = tFidelity rho := by
  unfold tCanonicalizedInput tInputFidelity tDirectionFidelity
  rw [← tCanonicalizer_conj_tProjector (tMaximizingDirection rho)]
  rw [projectionFidelity_conjDensity]
  exact (tMaximizingDirection_attains rho).symm
end QEC.Distillation.BK05T
