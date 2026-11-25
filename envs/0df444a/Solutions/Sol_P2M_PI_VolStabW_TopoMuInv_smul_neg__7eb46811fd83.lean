-- Prove2me | solution 1 for P2M_PI_VolStabW_TopoMuInv_smul_neg__7eb46811fd83
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:27.298347+00:00
-- url     : https://prove2.me/submissions/f12c7674-a6bd-4f27-a176-f4d649a7a389

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoFibInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMuInv
import Theorems.Thm_PI_VolStabW_TopoMuInv_smul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.TopoMuInv
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [SecondCountableTopology R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolStabW.TopoMuInv
theorem _root_.solution (h : HA R σ J) {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    h • (-X) = -(h • X) := by
  funext x
  simp only [smul_apply, Pi.neg_apply, Matrix.mulVec_neg]
end PI.VolStabW.TopoMuInv
