-- Prove2me | solution 1 for PI.VolStabW.LocPosW.gramR_ratTup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:31:33.4278+00:00
-- url     : https://prove2.me/submissions/fc032306-a6ec-435f-ba07-0297bdba2048

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FreeOpen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibInf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter Topology Set
open scoped TensorProduct ENNReal
open PI.VolStabW.LocPosW
namespace PI.VolStabW.LocPosW
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X0 : Fin n → Fin M → E) :
    gramR R σ J (ratTup R X0) = (gramE σ J X0).map (inclR R) := by
  have hs : ∀ e : E, sigR R σ (inclR R e) = inclR R (σ e) := by
    intro e
    simp [sigR, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  ext a b
  simp only [gramR, gramE, hR, hE, Formalism.UG.hform, ratTup, JR, Matrix.map_apply, hs, map_sum, map_mul,
    AlgHom.coe_toRingHom]
end PI.VolStabW.LocPosW
