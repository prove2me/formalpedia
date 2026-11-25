-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.BM.measure_Ov
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:29.446629+00:00
-- url     : https://prove2.me/submissions/03e7f8f6-11ba-4bcc-b25a-5cdd4433df86

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_LocPowB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulA
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_isOpen_Ov
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_q_ne_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_mem_max_iff
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_lt_one_iff
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_isOpen_Mv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_index_max

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
theorem _root_.solution [MeasurableSpace (Fv F v)] [BorelSpace (Fv F v)] (μ : Measure (Fv F v))
    [μ.IsAddLeftInvariant] (ϖ : Fv F v) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    (Ideal.absNorm v.asIdeal : ℝ≥0∞) * μ (Mv v ϖ) = μ (Ov v) := by
  let O' := v.adicCompletionIntegers F
  have hO : MeasurableSet (Ov v) := (isOpen_Ov v).measurableSet
  have hme : MeasurableEmbedding (Subtype.val : O' → Fv F v) := MeasurableEmbedding.subtype_coe hO
  let ν : Measure O' := Measure.comap Subtype.val μ
  haveI : MeasurableAdd O' :=
    ⟨fun c => hme.measurable_comp_iff.1 (by
        show Measurable fun x : O' => ((c + x : O') : Fv F v)
        simpa using (measurable_subtype_coe.const_add (c : Fv F v))),
     fun c => hme.measurable_comp_iff.1 (by
        show Measurable fun x : O' => ((x + c : O') : Fv F v)
        simpa using (measurable_subtype_coe.add_const (c : Fv F v)))⟩
  haveI : ν.IsAddLeftInvariant := ⟨fun g => by
    ext S hS
    rw [Measure.map_apply (measurable_const_add g) hS]
    simp only [ν, hme.comap_apply]
    have e : Subtype.val '' ((fun h => g + h) ⁻¹' S) =
        (fun h : Fv F v => (g : Fv F v) + h) ⁻¹' (Subtype.val '' S) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨g + x, hx, by simp⟩
      · rintro ⟨z, hz, hzy⟩
        have hy : y ∈ O' := by
          have e2 : y = (z : Fv F v) - g := by rw [hzy]; ring
          rw [e2]; exact sub_mem z.2 g.2
        refine ⟨⟨y, hy⟩, ?_, rfl⟩
        have e3 : g + ⟨y, hy⟩ = z := Subtype.ext (by simp [hzy])
        show g + ⟨y, hy⟩ ∈ S
        rw [e3]; exact hz
    rw [e, measure_preimage_add]⟩
  let H : AddSubgroup O' := (IsLocalRing.maximalIdeal O').toAddSubgroup
  haveI : H.FiniteIndex := ⟨by rw [index_max]; exact q_ne_zero v⟩
  have hHset : (H : Set O') = Subtype.val ⁻¹' Mv v ϖ := by
    ext x
    show x ∈ IsLocalRing.maximalIdeal O' ↔ _
    rw [mem_max_iff, lt_one_iff v ϖ hϖ]
    rfl
  have hH : MeasurableSet (H : Set O') := by
    rw [hHset]; exact measurable_subtype_coe (isOpen_Mv v ϖ).measurableSet
  have key := AddSubgroup.index_mul_measure H hH ν
  have e1 : ν H = μ (Mv v ϖ) := by
    simp only [ν, hme.comap_apply]
    rw [hHset, Set.image_preimage_eq_inter_range, Subtype.range_coe]
    congr 1
    ext y
    constructor
    · rintro ⟨h1, -⟩; exact h1
    · intro h1
      refine ⟨h1, ?_⟩
      exact le_of_lt ((lt_one_iff v ϖ hϖ y).2 h1)
  have e2 : ν Set.univ = μ (Ov v) := by
    simp only [ν, hme.comap_apply, Set.image_univ]
    rw [Subtype.range_coe_subtype]
    rfl
  rw [e1, e2, index_max] at key
  exact key
end PI.UnitaryGroupMassFormula.LocJacTyp.BM
