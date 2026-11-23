-- Prove2me | solution 1 for PI.VolStabSW.FiniteThetaCoordinates.crd_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:54.071153+00:00
-- url     : https://prove2.me/submissions/039a87cf-1a99-4079-b4db-13e7b58d378f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
namespace PI.VolStabSW.FiniteThetaCoordinates
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] {ι : Type} (s : Finset ι) (y : ι → R ⊗[F] E)
    (k : Fin d) : crd b R (∑ i ∈ s, y i) k = ∑ i ∈ s, crd b R (y i) k := by
  simp [crd, map_sum, Finsupp.finsetSum_apply]
end PI.VolStabSW.FiniteThetaCoordinates
