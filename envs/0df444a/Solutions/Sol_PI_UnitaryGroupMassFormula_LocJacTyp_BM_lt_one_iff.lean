-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.BM.lt_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:41.875042+00:00
-- url     : https://prove2.me/submissions/16cf4347-7416-4a85-bac1-587d46b5af2d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_LocPowB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp.BM
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped ENNReal NNReal Pointwise
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp.BM
theorem _root_.solution (ϖ : Fv F v) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (y : Fv F v) :
    Valued.v y < 1 ↔ Valued.v (ϖ⁻¹ * y) ≤ 1 := by
  rw [map_mul, map_inv₀, hϖ]
  rcases eq_or_ne (Valued.v y) 0 with h0 | h0
  · rw [h0]
    simp
  · obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v y = WithZero.exp n := by
      first
      | exact ⟨WithZero.log (Valued.v y), (WithZero.exp_log h0).symm⟩
      | (obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp h0
         exact ⟨Multiplicative.toAdd a, by rw [← ha]; rfl⟩)
    rw [hn, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_add, ← WithZero.exp_zero,
      WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega
end PI.UnitaryGroupMassFormula.LocJacTyp.BM
