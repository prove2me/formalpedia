-- Prove2me | solution 1 for PI.VolStabSW.densVLC_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:44.097201+00:00
-- url     : https://prove2.me/submissions/e2f787e6-3ab6-42c7-9fbd-2ea16e62fec1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVSt
import Theorems.Thm_PI_VolStabSW_densLC_of_cos


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
  Topology
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution (hT : TensAll) (hNA : TensNA) (hC : DensVCs) : DensVLC := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν
  obtain ⟨_t1, t2, _t3, _t4, _t5, _t6, _t7⟩ := (hT F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet).2 v
  have := hμ.1
  have := hν.1
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  exact densLC_of_cos _ (hNA F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet v)
    (hC F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν)
end PI.VolStabSW
