-- Prove2me | solution 1 for PI.VolStabW.VolAAW.BR_eT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:16:38.225691+00:00
-- url     : https://prove2.me/submissions/af7f2619-92b1-4575-8788-6a3e48a45cfa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolB
import Theorems.Thm_PI_VolStabW_VolAAW_hform_single
import Theorems.Thm_Formalism_UG_P_hform_single
import Theorems.Thm_PI_VolStabW_SdDualW_trace_one_tmul


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
open PI.VolStabW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabW.VolAAW
theorem _root_.solution (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (q q' : Fin a × Fin M × Fin d) :
    BR (Fv F v) σ J (eT v b q) (eT v b q') = algebraMap F (Fv F v) (gG b σ J a q q') := by
  obtain ⟨p, i, k⟩ := q
  obtain ⟨p', j, l⟩ := q'
  simp only [BR, eT]
  rw [Finset.sum_eq_single p (fun p'' _ h => by simp [Pi.single_apply, h, hR, Formalism.UG.hform])
    (by simp)]
  simp only [Pi.single_eq_same, gG]
  by_cases hp : p = p'
  · subst hp
    simp only [Pi.single_eq_same, if_true, hR, hform_single, JR, Matrix.map_apply]
    have e : sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] b k) * inclR (Fv F v) (J i j) *
        ((1 : Fv F v) ⊗ₜ[F] b l) = (1 : Fv F v) ⊗ₜ[F] (σ (b k) * J i j * b l) := by
      simp [sigR, inclR, Algebra.TensorProduct.tmul_mul_tmul]
    rw [e, trace_one_tmul]
  · have hp' : p' ≠ p := fun h => hp h.symm
    simp [Pi.single_apply, hp, hR, Formalism.UG.hform]
end PI.VolStabW.VolAAW
