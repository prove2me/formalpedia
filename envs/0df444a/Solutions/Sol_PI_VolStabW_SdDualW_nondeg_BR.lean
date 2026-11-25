-- Prove2me | solution 1 for PI.VolStabW.SdDualW.nondeg_BR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:06:20.611302+00:00
-- url     : https://prove2.me/submissions/fa3f71f4-e198-45af-93b0-7b5c15eb3ec8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual
import Theorems.Thm_PI_VolStabW_SdDualW_trace_nondeg
import Theorems.Thm_PI_VolStabW_TensAllW_inj_of_isUnit


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
open PI.VolStabW.SdDualW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E]
namespace PI.VolStabW.SdDualW
theorem _root_.solution [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) (Y : Fin a → Fin M → Fv F v ⊗[F] E)
    (h : ∀ X, BR (Fv F v) σ J X Y = 0) : Y = 0 := by
  classical
  funext p
  have hz : ∀ i, (JR (Fv F v) J).mulVec (Y p) i = 0 := by
    intro i
    apply trace_nondeg v (Module.finBasis F E)
    intro w
    have := h (Pi.single p (Pi.single i (sigR (Fv F v) σ w)))
    simp only [BR, hR, Formalism.UG.hform] at this
    rw [Finset.sum_eq_single p (fun p' _ hp' => by simp [Pi.single_apply, hp']) (by simp)] at this
    rw [Finset.sum_eq_single i (fun i' _ hi' => by simp [Pi.single_apply, hi']) (by simp)] at this
    simp only [Pi.single_eq_same, sigR_invol (Fv F v) σ hσ] at this
    simpa [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using this
  have hdet : IsUnit ((1 : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) * JR (Fv F v) J).det := by
    rw [one_mul]
    have e := RingHom.map_det (inclR (F := F) (E := E) (Fv F v)) J
    rw [RingHom.mapMatrix_apply] at e
    show IsUnit (J.map (inclR (Fv F v))).det
    rw [← e]
    exact (isUnit_iff_ne_zero.2 hJ).map _
  exact TensAllW.inj_of_isUnit _ 1 hdet _ (funext hz)
end PI.VolStabW.SdDualW
