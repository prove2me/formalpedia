-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.BM.mem_max_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:43.289668+00:00
-- url     : https://prove2.me/submissions/d90dd2d8-94da-4e14-8e82-874d9b7b2985

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
theorem _root_.solution (x : v.adicCompletionIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔ Valued.v (x : Fv F v) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hx1 : Valued.v (x : Fv F v) ≤ 1 := x.2
  constructor
  · intro hx
    refine lt_of_le_of_ne hx1 (fun h1 => hx ?_)
    have hx0 : (x : Fv F v) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    have hinv : Valued.v ((x : Fv F v)⁻¹) ≤ 1 := by
      rw [map_inv₀, h1, inv_one]
    have hmul : x * ⟨(x : Fv F v)⁻¹, hinv⟩ = 1 := by
      apply Subtype.ext
      change (x : Fv F v) * (x : Fv F v)⁻¹ = 1
      exact mul_inv_cancel₀ hx0
    exact ⟨⟨x, ⟨(x : Fv F v)⁻¹, hinv⟩, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  · intro hlt hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have h2 : (x : Fv F v) * (y : Fv F v) = 1 := congrArg Subtype.val hy
    have hy1 : Valued.v (y : Fv F v) ≤ 1 := y.2
    have h3 : Valued.v (x : Fv F v) * Valued.v (y : Fv F v) = 1 := by
      rw [← map_mul, h2, map_one]
    have h4 : Valued.v (x : Fv F v) * Valued.v (y : Fv F v) < 1 :=
      calc Valued.v (x : Fv F v) * Valued.v (y : Fv F v) ≤ Valued.v (x : Fv F v) * 1 :=
            by
              first
              | gcongr
              | exact mul_le_mul_of_nonneg_left hy1 zero_le'
              | exact mul_le_mul_right' hy1 _
              | exact mul_le_mul_left hy1 _
        _ = Valued.v (x : Fv F v) := mul_one _
        _ < 1 := hlt
    rw [h3] at h4
    exact lt_irrefl _ h4
end PI.UnitaryGroupMassFormula.LocJacTyp.BM
