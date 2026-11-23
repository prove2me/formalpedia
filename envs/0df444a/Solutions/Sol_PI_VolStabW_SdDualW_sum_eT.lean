-- Prove2me | solution 1 for PI.VolStabW.SdDualW.sum_eT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:57.857463+00:00
-- url     : https://prove2.me/submissions/68d5c27b-4e94-4949-83bc-703759c0926c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_eq_sum_crd


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
variable [FiniteDimensional F E] (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolStabW.SdDualW
theorem _root_.solution (X : Fin a → Fin M → Fv F v ⊗[F] E) :
    X = ∑ q : Fin a × Fin M × Fin d, crd b (Fv F v) (X q.1 q.2.1) q.2.2 • eT v b q := by
  funext p i
  rw [Finset.sum_apply, Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single p]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simp only [eT, Pi.smul_apply, Pi.single_eq_same]
      exact eq_sum_crd b (Fv F v) (X p i)
    · intro j _ hj
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [eT, hj]
    · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [eT, Ne.symm hx]
  · simp
end PI.VolStabW.SdDualW
