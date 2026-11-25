-- Prove2me | solution 1 for PI.AprimeInfT.continuous_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:11:54.673945+00:00
-- url     : https://prove2.me/submissions/6d0003d7-6a47-4eba-9c13-3d2e8399db64

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_T2SpaceTensorProductFiniteExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfT
open scoped TensorProduct
open NumberField MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
variable [LocallyCompactSpace R] [T2Space R]
variable {M : ℕ}
namespace PI.AprimeInfT
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) {a : ℕ}
    (X0 : Fin a → Fin M → E) :
    Continuous (fun g : HA R σ J => g • ratTup (F := F) R X0) := by
  have hmat : Continuous (fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))) :=
    Units.continuous_val.comp continuous_subtype_val
  show Continuous (fun g : HA R σ J => actTup R (HA.mat R σ J g) (ratTup (F := F) R X0))
  unfold actTup
  exact continuous_pi fun i => hmat.matrix_mulVec continuous_const
end PI.AprimeInfT
