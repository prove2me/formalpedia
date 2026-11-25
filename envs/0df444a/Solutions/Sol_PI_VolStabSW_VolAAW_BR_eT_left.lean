-- Prove2me | solution 1 for PI.VolStabSW.VolAAW.BR_eT_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:41:24.50019+00:00
-- url     : https://prove2.me/submissions/a0e358a5-ba1d-46d4-8027-c5da3fe125c4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolB
import Theorems.Thm_PI_VolStabSW_VolAAW_BR_eT
import Theorems.Thm_PI_VolStabSW_SdDualW_sum_eT


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
open PI.VolStabSW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabSW.VolAAW
theorem _root_.solution (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (q : Fin a × Fin M × Fin d) (Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J (eT v b q) Y =
      ((gG b σ J a).map (algebraMap F (Fv F v))).mulVec (cT b v Y) q := by
  have h := congrFun (congrArg (phiL (a := a) v b σ J) (sum_eT v b Y)) q
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  change BR (Fv F v) σ J (eT v b q) Y = _
  have h2 : phiL (a := a) v b σ J Y q = BR (Fv F v) σ J (eT v b q) Y := rfl
  rw [← h2, h]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, cT]
  refine Finset.sum_congr rfl fun q' _ => ?_
  have h3 : phiL (a := a) v b σ J (eT v b q') q = BR (Fv F v) σ J (eT v b q) (eT v b q') := rfl
  rw [h3, BR_eT, mul_comm]
end PI.VolStabSW.VolAAW
