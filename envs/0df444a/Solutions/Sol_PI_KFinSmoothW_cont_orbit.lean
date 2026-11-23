-- Prove2me | solution 1 for PI.KFinSmoothW.cont_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:56.921029+00:00
-- url     : https://prove2.me/submissions/d881b7e5-dff6-421b-9730-2e385f709744

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_DenseWeakVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace PI.KFinSmoothW
theorem _root_.solution {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ) (u : H) :
    Continuous (fun h : UJ ε => τ (umat h) u) := (hτ.2.2 u).comp_continuous (Units.continuous_val.comp continuous_subtype_val) (fun h => h.2)
end PI.KFinSmoothW
