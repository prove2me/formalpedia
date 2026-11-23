-- Prove2me | solution 1 for PI.VolStabSW.secCtblG_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:09.9028+00:00
-- url     : https://prove2.me/submissions/dd816b63-dd05-4d1f-bbd6-e411ba268237

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExStabSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExStabTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal
namespace PI.VolStabSW
theorem _root_.solution (hW : SecCtblW) : SecCtblG := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := hW F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : SecondCountableTopology (Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → AF F ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin M) (Fin M) (AF F ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  have : SecondCountableTopology (GL (Fin M) (AF F ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have h2 : SecondCountableTopology (HR (AF F) σ J) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  exact h2
end PI.VolStabSW
