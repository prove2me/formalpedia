-- Prove2me | solution 1 for PI.VolStabSW.TensAllW.isOpen_linIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:09.853658+00:00
-- url     : https://prove2.me/submissions/2e27afcc-6840-453b-b8a0-d629b5b70808

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibOfTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll
import Theorems.Thm_PI_VolStabSW_TensAllW_inj_of_isUnit
import Theorems.Thm_PI_VolStabSW_TensAllW_linIndep_iff
import Theorems.Thm_PI_VolStabSW_TensAllW_continuous_wMat

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
open PI.VolStabSW.TensAllW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
  [IsTopologicalRing R]
include b
namespace PI.VolStabSW.TensAllW
theorem _root_.solution (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R) {a M : ℕ} :
    IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
  have hset : {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} =
      ⋃ P : Matrix (Fin a × Fin d) (Fin M × Fin d) R, {X | IsUnit (P * wMat b R X).det} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [linIndep_iff b R X]
    constructor
    · intro h
      obtain ⟨P, hP⟩ := hL _ _ (wMat b R X) h
      refine ⟨P, ?_⟩
      rw [hP, Matrix.det_one]
      exact isUnit_one
    · rintro ⟨P, hP⟩ c hc
      exact inj_of_isUnit (wMat b R X) P hP c hc
  rw [hset]
  exact isOpen_iUnion fun P =>
    hU.preimage ((continuous_const.matrix_mul (continuous_wMat b R)).matrix_det)
end PI.VolStabSW.TensAllW
