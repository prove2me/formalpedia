-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.BM.absV_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:53.209039+00:00
-- url     : https://prove2.me/submissions/1069ef00-6f1e-44ae-a0d0-f4ef9673080e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_Transport
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_GoodTransvection
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiagonalOneJacobian
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.UnitaryGroupMassFormula.LocJacTyp.BM
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp
open scoped TensorProduct ENNReal NNReal
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
private theorem absV_mul_lemma (x y : Fv F v) : absV v (x * y) = absV v x * absV v y := by
  have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
  by_cases hx : Valued.v x = 0
  · have hxy : Valued.v (x * y) = 0 := by rw [map_mul, hx, zero_mul]
    simp [absV, hx, hxy]
  by_cases hy : Valued.v y = 0
  · have hxy : Valued.v (x * y) = 0 := by rw [map_mul, hy, mul_zero]
    simp [absV, hy, hxy]
  have hxy : Valued.v (x * y) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hx hy
  unfold absV
  rw [dif_neg hx, dif_neg hy, dif_neg hxy, ← zpow_add₀ hq, ← toAdd_mul]
  congr 2
  rw [← WithZero.coe_inj, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero,
    WithZero.coe_unzero, map_mul]
private theorem absV_one_lemma_2 : absV v (1 : Fv F v) = 1 := by
  have h1 : Valued.v (1 : Fv F v) ≠ 0 := by
    rw [map_one]
    exact one_ne_zero
  unfold absV
  rw [dif_neg h1]
  have h2 : WithZero.unzero h1 = 1 := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, map_one, WithZero.coe_one]
  rw [h2, toAdd_one, zpow_zero]
end PI.UnitaryGroupMassFormula.LocJacTyp.BM
end
end

set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp.BM
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp
open scoped TensorProduct ENNReal NNReal
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp.BM
theorem _root_.solution {ι : Type} [Fintype ι] (a : ι → Fv F v) :
    absV v (∏ i, a i) = ∏ i, absV v (a i) := by
  let f : Fv F v →* ℝ :=
    { toFun := absV v, map_one' := absV_one_lemma_2 v, map_mul' := absV_mul_lemma v }
  exact map_prod f a Finset.univ
end PI.UnitaryGroupMassFormula.LocJacTyp.BM
