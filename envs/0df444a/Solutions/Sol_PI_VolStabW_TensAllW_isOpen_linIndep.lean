-- Prove2me | solution 1 for PI.VolStabW.TensAllW.isOpen_linIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:32.509519+00:00
-- url     : https://prove2.me/submissions/87baf501-6f0e-4f6e-acef-59f64a9c1f99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibOfTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Theorems.Thm_PI_VolStabW_TensAllW_inj_of_isUnit
import Theorems.Thm_PI_VolStabW_TensAllW_linIndep_iff
import Theorems.Thm_PI_VolStabW_TensAllW_continuous_wMat

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
open PI.VolStabW.TensAllW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
  [IsTopologicalRing R]
include b
namespace PI.VolStabW.TensAllW
theorem _root_.solution (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R) {a M : ℕ} :
    IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
  have e : {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} =
      ⋃ P : Matrix (Fin a × Fin d) (Fin M × Fin d) R,
        (fun X => (P * wMat b R X).det) ⁻¹' {r | IsUnit r} := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
    rw [linIndep_iff b]
    constructor
    · intro h
      obtain ⟨P, hP⟩ := hL _ _ _ h
      exact ⟨P, by rw [hP, Matrix.det_one]; exact isUnit_one⟩
    · rintro ⟨P, hP⟩ c hc
      exact inj_of_isUnit _ P hP c hc
  rw [e]
  exact isOpen_iUnion fun P =>
    hU.preimage ((continuous_const.matrix_mul (continuous_wMat b R)).matrix_det)
end PI.VolStabW.TensAllW
