-- Prove2me | solution 1 for PI.VolStabSW.continuous_hR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:44.490222+00:00
-- url     : https://prove2.me/submissions/fd0c2012-81c2-4cd3-beab-39b978e32db4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop

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
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
variable [LocallyCompactSpace R] [T2Space R]
namespace PI.VolStabSW
theorem _root_.solution (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous (fun p : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) => hR R σ J p.1 p.2) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
  have hs := continuous_sigR_stabilizer_orbit_volume (F := F) (E := E) R σ
  unfold hR Formalism.UG.hform
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    ((hs.comp ((continuous_apply i).comp continuous_fst)).mul continuous_const).mul
      ((continuous_apply j).comp continuous_snd)
end PI.VolStabSW
