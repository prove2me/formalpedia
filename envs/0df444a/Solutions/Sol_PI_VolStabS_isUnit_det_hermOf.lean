-- Prove2me | solution 1 for PI.VolStabS.isUnit_det_hermOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:34.385605+00:00
-- url     : https://prove2.me/submissions/ed971db6-9a8e-4ab2-a86e-9c4aeaec0b19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TensTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
namespace PI.VolStabS
theorem _root_.solution (σ : E →ₐ[F] E) {n : ℕ} (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a b, σ (T b a) = T a b) (hdet : T.det ≠ 0) :
    IsUnit ((hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) := by
  show IsUnit (T.map (inclR R)).det
  rw [show (T.map (inclR R)).det = inclR R T.det from (RingHom.map_det (inclR R) T).symm]
  exact (isUnit_iff_ne_zero.2 hdet).map _
end PI.VolStabS
