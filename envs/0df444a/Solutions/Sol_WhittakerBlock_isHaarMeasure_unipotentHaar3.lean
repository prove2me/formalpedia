-- Prove2me | solution 1 for WhittakerBlock.isHaarMeasure_unipotentHaar3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1f31f6b7-19c5-594e-97ee-440db6d26af0

import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_M4aHerbrand_AdeleTopologyFacts
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WhittakerBlock_isHaarMeasure_unipotentHaar3
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory LanglandsTunnell.CubicInduction

noncomputable section

open NumberField NumberField.AdelicHaar WhittakerBlock Set Function
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private scoped instance : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdeleRing.secondCountableTopology ℚ

private abbrev AQ := AdeleRing (𝓞 ℚ) ℚ

private abbrev T3 := AQ × AQ × AQ

private def nParam (t : T3) : unipotentSubgroup3 :=
  ⟨upperUnipotent3 t.1 t.2.1 t.2.2, Subgroup.subset_closure ⟨t, rfl⟩⟩

private noncomputable def nu3 :
    Measure (T3) :=
  (adelicAddHaar (𝓞 ℚ) ℚ).prod ((adelicAddHaar (𝓞 ℚ) ℚ).prod (adelicAddHaar (𝓞 ℚ) ℚ))

private theorem unipotentHaar3_eq_map : unipotentHaar3 = Measure.map nParam nu3 := rfl

private scoped instance : (adelicAddHaar (𝓞 ℚ) ℚ).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ

private scoped instance : SFinite nu3 := by unfold nu3; infer_instance

private scoped instance : IsFiniteMeasureOnCompacts nu3 := by unfold nu3; infer_instance

private scoped instance : nu3.IsOpenPosMeasure := by unfold nu3; infer_instance

private def ent (n : unipotentSubgroup3) : T3 :=
  (((n : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) AQ) 0 1,
    ((n : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) AQ) 1 2,
    ((n : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) AQ) 0 2)

private theorem ent_nParam (t : T3) : ent (nParam t) = t := by
  obtain ⟨x, y, z⟩ := t
  simp [ent, nParam, upperUnipotent3_coe]

private theorem nParam_ent (n : unipotentSubgroup3) : nParam (ent n) = n := by
  obtain ⟨x, y, z, hn⟩ := (mem_unipotentSubgroup3_iff (n : AdelicGL 3 (𝓞 ℚ) ℚ)).1 n.2
  apply Subtype.ext
  simp only [nParam]
  rw [hn]
  simp [ent, hn, upperUnipotent3_coe]

private theorem preimage_nParam_eq (s : Set unipotentSubgroup3) : nParam ⁻¹' s = ent '' s := by
  ext t
  constructor
  · intro ht
    exact ⟨nParam t, ht, ent_nParam t⟩
  · rintro ⟨n, hn, rfl⟩
    simpa [mem_preimage, nParam_ent] using hn

private theorem nParam_surjective : Surjective nParam := fun n => ⟨ent n, nParam_ent n⟩

private theorem continuous_nParam : Continuous nParam := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  ·
    exact continuous_matrix fun i j => by fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop
  ·
    exact continuous_matrix fun i j => by fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop

private theorem continuous_ent : Continuous ent := by
  have h : Continuous fun n : unipotentSubgroup3 =>
      ((n : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) AQ) :=
    Units.continuous_val.comp continuous_subtype_val
  exact (h.matrix_elem 0 1).prodMk ((h.matrix_elem 1 2).prodMk (h.matrix_elem 0 2))

private theorem measurable_nParam : Measurable nParam := continuous_nParam.measurable

private def shearL (a b c : AQ) :
    T3 → T3 :=
  Prod.map (fun x => a + x) (fun p => (b + p.1, (c + a * p.1) + p.2))

private theorem measurePreserving_shearL (a b c : AQ) : MeasurePreserving (shearL a b c) nu3 nu3 := by
  unfold shearL nu3
  refine (measurePreserving_add_left _ a).prod ?_
  refine (measurePreserving_add_left _ b).skew_product (g := fun y z => (c + a * y) + z) ?_ ?_
  · exact (by fun_prop : Continuous fun p : AQ × AQ => (c + a * p.1) + p.2).measurable
  · exact Filter.Eventually.of_forall fun y => map_add_left_eq_self _ (c + a * y)

private theorem mul_nParam (a b c : AQ)
    (t : T3) :
    nParam (a, b, c) * nParam t = nParam (shearL a b c t) := by
  obtain ⟨x, y, z⟩ := t
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [nParam, shearL, upperUnipotent3_coe, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private scoped instance isMulLeftInvariant_unipotentHaar3 : unipotentHaar3.IsMulLeftInvariant := by
  refine ⟨fun n₀ => ?_⟩
  obtain ⟨a, b, c, h⟩ := (mem_unipotentSubgroup3_iff (n₀ : AdelicGL 3 (𝓞 ℚ) ℚ)).1 n₀.2
  have hn₀ : n₀ = nParam (a, b, c) := Subtype.ext h
  have hcomp : (fun n => n₀ * n) ∘ nParam = nParam ∘ shearL a b c := by
    funext t
    simp only [comp_apply, hn₀, mul_nParam]
  rw [unipotentHaar3_eq_map, Measure.map_map (measurable_const_mul n₀) measurable_nParam, hcomp,
    ← Measure.map_map measurable_nParam (measurePreserving_shearL a b c).measurable,
    (measurePreserving_shearL a b c).map_eq]

private scoped instance isFiniteMeasureOnCompacts_unipotentHaar3 : IsFiniteMeasureOnCompacts unipotentHaar3 := by
  refine ⟨fun K hK => ?_⟩
  rw [unipotentHaar3_eq_map, Measure.map_apply measurable_nParam hK.measurableSet, preimage_nParam_eq]
  exact (hK.image continuous_ent).measure_lt_top

private scoped instance isOpenPosMeasure_unipotentHaar3 : unipotentHaar3.IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [unipotentHaar3_eq_map, Measure.map_apply measurable_nParam hU.measurableSet]
  exact (hU.preimage continuous_nParam).measure_ne_zero nu3 (hne.preimage nParam_surjective)

attribute [local instance] NumberField.AdelicHaar.glBorel in
theorem solution : Measure.IsHaarMeasure unipotentHaar3 where
  toIsFiniteMeasureOnCompacts := isFiniteMeasureOnCompacts_unipotentHaar3
  toIsMulLeftInvariant := isMulLeftInvariant_unipotentHaar3
  toIsOpenPosMeasure := isOpenPosMeasure_unipotentHaar3

end

end S_WhittakerBlock_isHaarMeasure_unipotentHaar3
end P2MW
export P2MW.S_WhittakerBlock_isHaarMeasure_unipotentHaar3 (solution)
