-- Prove2me | solution 1 for UnramifiedWhittaker.integral_zetaIntegrand_unipotent_partMeasure_eq_mul_prod_tsum_torusFactor_mul_setIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9bb495f1-061d-5a6c-952b-b17ba3d16e65

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_HeightOneSpectrum
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Definitions.Def_NumberField_PlaceTransport

import Theorems.Thm_UnramifiedWhittaker_apply_mul_prod_placeEmbed_diagZ_eq_mul_prod_torusFactor
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UnramifiedWhittaker_integral_zetaIntegrand_unipotent_partMeasure_eq_mul_prod_tsum_torusFactor_mul_setIntegral
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"
set_option Elab.async false

set_option autoImplicit false

open Matrix MeasureTheory
open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdeleRing NumberField.TateGlobal
open AutomorphicForm AdelicDock

noncomputable section

namespace UnramifiedWhittaker
p2m_export "UnramifiedWhittaker" "zetaIntegrand torusFactor unipotent diagZ repSome repInf scalarPi placeEmbed apply_mul_prod_placeEmbed_diagZ_eq_mul_prod_torusFactor"
namespace PartMeasureFactorisation
p2m_open "UnramifiedWhittaker"

section Furniture

variable {K : Type} [Field K] [NumberField K]

private def compAt (w : HeightOneSpectrum (𝓞 K)) : AdelicGL2 (𝓞 K) K →* GL (Fin 2) (w.adicCompletion K) :=
  (finComponent (𝓞 K) K w).comp (glFin (𝓞 K) K)

private theorem compAt_apply (w : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    (compAt w g : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j
      = (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j w := rfl

private theorem compAt_placeEmbed_self (v : HeightOneSpectrum (𝓞 K)) (h : GL (Fin 2) (v.adicCompletion K)) :
    compAt v (placeEmbed K v h) = h := by
  show finComponent (𝓞 K) K v (glFin (𝓞 K) K (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v h))) = h
  rw [glFin_finEmbed, finComponent_localEmbed_self]

private theorem compAt_placeEmbed_of_ne {v w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v)
    (h : GL (Fin 2) (v.adicCompletion K)) :
    compAt w (placeEmbed K v h) = 1 := by
  show finComponent (𝓞 K) K w (glFin (𝓞 K) K (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v h))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]

private theorem glArch_placeEmbed (v : HeightOneSpectrum (𝓞 K)) (h : GL (Fin 2) (v.adicCompletion K)) :
    glArch (𝓞 K) K (placeEmbed K v h) = 1 := by
  show glArch (𝓞 K) K (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v h)) = 1
  exact glArch_finEmbed _ _ _

private theorem ext_of_glArch_of_compAt {x y : AdelicGL2 (𝓞 K) K} (harch : glArch (𝓞 K) K x = glArch (𝓞 K) K y)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 K), compAt w x = compAt w y) : x = y := by
  refine Units.ext (matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 K) K ?_ ?_)
  · exact congrArg Units.val harch
  · refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 K) K fun w => ?_
    exact congrArg Units.val (hfin w)

private theorem val_mul_inv_snd_apply (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (z : AdeleRing (𝓞 K) K).2 v * ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 :=
  congrArg (fun x : AdeleRing (𝓞 K) K => x.2 v) z.mul_inv

private theorem val_inv_mul_snd_apply (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v * (z : AdeleRing (𝓞 K) K).2 v = 1 :=
  congrArg (fun x : AdeleRing (𝓞 K) K => x.2 v) z.inv_mul

private def unitAt (v : HeightOneSpectrum (𝓞 K)) (z : (AdeleRing (𝓞 K) K)ˣ) : (v.adicCompletion K)ˣ where
  val := (z : AdeleRing (𝓞 K) K).2 v
  inv := ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v
  val_inv := val_mul_inv_snd_apply z v
  inv_val := val_inv_mul_snd_apply z v

private theorem unitAt_val (v : HeightOneSpectrum (𝓞 K)) (z : (AdeleRing (𝓞 K) K)ˣ) :
    (unitAt v z : v.adicCompletion K) = (z : AdeleRing (𝓞 K) K).2 v := rfl

private theorem compAt_diagOne (v : HeightOneSpectrum (𝓞 K)) (a : (AdeleRing (𝓞 K) K)ˣ) :
    compAt v (diagOne a) = diagOne (unitAt v a) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [compAt_apply, glFin_apply, diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [unitAt_val] <;> rfl

private def finIdele (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)

private theorem finIdele_inv (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    (finIdele v t)⁻¹ = finIdele v t⁻¹ := by
  unfold finIdele
  rw [← map_inv, ← map_inv]

private theorem finIdele_val_fst_apply (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ)
    (w : InfinitePlace K) : ((finIdele v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = 1 := rfl

private theorem finIdele_val_snd_self (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ((finIdele v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = (t : v.adicCompletion K) := by
  show ((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = _
  rw [localUnit_apply_self]

private theorem finIdele_val_snd_of_ne (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    ((finIdele v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 := by
  show ((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w = _
  exact localUnit_apply_of_ne (hw := hw) ..

private theorem localUnit_mem_unitIdeles (v : HeightOneSpectrum (𝓞 K)) {u : (v.adicCompletion K)ˣ}
    (hu : (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K)
    (hu' : ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    localUnit (𝓞 K) K v u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K := by
  rw [IsDedekindDomain.FiniteAdeleRing.mem_unitIdeles_iff, ← map_inv]
  refine ⟨fun w => ?_, fun w => ?_⟩
  · by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self]
      exact hu
    · rw [show (localUnit (𝓞 K) K v u : FiniteAdeleRing (𝓞 K) K) w = 1 from localUnit_apply_of_ne (hw := hw) ..]
      exact one_mem _
  · by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self]
      exact hu'
    · rw [show (localUnit (𝓞 K) K v u⁻¹ : FiniteAdeleRing (𝓞 K) K) w = 1 from
        localUnit_apply_of_ne (hw := hw) ..]
      exact one_mem _

private theorem diagOne_mul_placeEmbed_unipotent (δ : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) :
    diagOne δ * placeEmbed K v (unipotent x)
      = placeEmbed K v (unipotent (((δ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v * x)) * diagOne δ := by
  refine ext_of_glArch_of_compAt ?_ fun w => ?_
  · rw [map_mul, map_mul, glArch_placeEmbed, glArch_placeEmbed, mul_one, one_mul]
  · rw [map_mul, map_mul, compAt_diagOne]
    by_cases hw : w = v
    · subst hw
      rw [compAt_placeEmbed_self, compAt_placeEmbed_self]
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul]
      show (diagOne (unitAt w δ) : Matrix (Fin 2) (Fin 2) _) * !![1, x; 0, 1]
        = !![1, _ * x; 0, 1] * (diagOne (unitAt w δ) : Matrix (Fin 2) (Fin 2) _)
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply, unitAt_val]
    · rw [compAt_placeEmbed_of_ne hw, compAt_placeEmbed_of_ne hw, mul_one, one_mul]

private theorem charExt_units_mul (v : HeightOneSpectrum (𝓞 K)) (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (e : (v.adicCompletion K)ˣ) (x : v.adicCompletion K) :
    LanglandsTunnell.TateLocal.charExt χ ((e : v.adicCompletion K) * x)
      = ((χ e : ℂˣ) : ℂ) * LanglandsTunnell.TateLocal.charExt χ x := by
  by_cases hx : x = 0
  · subst hx; rw [mul_zero, LanglandsTunnell.TateLocal.charExt_zero, mul_zero]
  · have h : (e : v.adicCompletion K) * x ≠ 0 := mul_ne_zero e.ne_zero hx
    rw [LanglandsTunnell.TateLocal.charExt_of_ne_zero χ h, LanglandsTunnell.TateLocal.charExt_of_ne_zero χ hx]
    have hmk : Units.mk0 ((e : v.adicCompletion K) * x) h = e * Units.mk0 x hx := Units.ext rfl
    rw [hmk, map_mul, Units.val_mul]

private theorem val_mul_snd_apply (y z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((y * z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v
      = (y : AdeleRing (𝓞 K) K).2 v * (z : AdeleRing (𝓞 K) K).2 v := rfl

private theorem val_mul_fst (y z : (AdeleRing (𝓞 K) K)ˣ) :
    ((y * z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1
      = (y : AdeleRing (𝓞 K) K).1 * (z : AdeleRing (𝓞 K) K).1 := rfl

private theorem glArch_diagOne_of_forall_eq_one {u : (AdeleRing (𝓞 K) K)ˣ}
    (hu : ((u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1) : glArch (𝓞 K) K (diagOne u) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply, Units.val_one, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [hu] <;> rfl

private theorem diagOne_finIdele (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    (diagOne (finIdele v u) : AdelicGL2 (𝓞 K) K) = placeEmbed K v (diagOne u) := by
  refine ext_of_glArch_of_compAt ?_ fun w => ?_
  · rw [glArch_placeEmbed, glArch_diagOne_of_forall_eq_one (funext (finIdele_val_fst_apply v u))]
  · rw [compAt_diagOne]
    by_cases hw : w = v
    · subst hw
      rw [compAt_placeEmbed_self]
      congr 1
      exact Units.ext (by rw [unitAt_val, finIdele_val_snd_self])
    · rw [compAt_placeEmbed_of_ne hw]
      have h1 : unitAt w (finIdele v u) = 1 := Units.ext (by rw [unitAt_val, finIdele_val_snd_of_ne v u hw]; rfl)
      rw [h1, map_one]

open scoped Classical in

private noncomputable def ideleOf (v : HeightOneSpectrum (𝓞 K)) (c : v.adicCompletion K) : (AdeleRing (𝓞 K) K)ˣ :=
  if h : c = 0 then 1 else finIdele v (Units.mk0 c h)

private theorem ideleOf_of_ne_zero (v : HeightOneSpectrum (𝓞 K)) {c : v.adicCompletion K} (h : c ≠ 0) :
    ideleOf v c = finIdele v (Units.mk0 c h) := by
  rw [ideleOf, dif_neg h]

private def unitSet (v : HeightOneSpectrum (𝓞 K)) : Set (v.adicCompletion K) := {u | Valued.v u = 1}

private theorem ne_zero_of_mem_unitSet {v : HeightOneSpectrum (𝓞 K)} {u : v.adicCompletion K} (hu : u ∈ unitSet v) :
    u ≠ 0 := by
  rintro rfl
  simp [unitSet] at hu

private theorem mul_mem_unitSet {v : HeightOneSpectrum (𝓞 K)} {c u : v.adicCompletion K} (hc : c ∈ unitSet v)
    (hu : u ∈ unitSet v) : c * u ∈ unitSet v := by
  simp only [unitSet, Set.mem_setOf_eq, map_mul] at hc hu ⊢
  rw [hc, hu, mul_one]

private theorem lt_one_iff_le_exp_neg_one (c : WithZero (Multiplicative ℤ)) : c < 1 ↔ c ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [← WithZero.exp_log hc, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

private theorem isClopen_unitSet (v : HeightOneSpectrum (𝓞 K)) : IsClopen (unitSet v) := by
  have h1 := NumberField.PlaceTransport.isClopen_setOf_valued_le (K := K) v (c := 1) one_ne_zero
  have h2 := NumberField.PlaceTransport.isClopen_setOf_valued_le (K := K) v (c := WithZero.exp (-1 : ℤ))
    WithZero.exp_ne_zero
  convert h1.diff h2 using 1
  ext u
  simp only [unitSet, Set.mem_setOf_eq, Set.mem_diff, ← lt_one_iff_le_exp_neg_one, not_lt]
  exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩

private theorem isOpen_unitSet (v : HeightOneSpectrum (𝓞 K)) : IsOpen (unitSet v) := (isClopen_unitSet v).isOpen

private theorem isCompact_unitSet (v : HeightOneSpectrum (𝓞 K)) : IsCompact (unitSet v) := by
  have hc : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    NumberField.isCompactAdicCompletionIntegers K v
  refine hc.of_isClosed_subset (isClopen_unitSet v).isClosed fun u hu => ?_
  rw [SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  exact le_of_eq hu

private theorem integral_comp_of_map_eq {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (e : α ≃ᵐ α) (he : Measure.map e ν = ν) (f : α → E) :
    ∫ x, f (e x) ∂ν = ∫ x, f x ∂ν := by
  conv_rhs => rw [← he]
  exact (integral_map_equiv e f).symm

section LocalMeasure

variable {v : HeightOneSpectrum (𝓞 K)} [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

private theorem measurableSet_unitSet : MeasurableSet (unitSet v) := (isOpen_unitSet v).measurableSet

omit [BorelSpace (v.adicCompletion K)] in
private theorem measure_unitSet_ne_zero : μ (unitSet v) ≠ 0 :=
  (isOpen_unitSet v).measure_ne_zero μ ⟨1, by simp [unitSet]⟩

omit [BorelSpace (v.adicCompletion K)] in
private theorem measure_unitSet_ne_top : μ (unitSet v) ≠ ⊤ := (isCompact_unitSet v).measure_lt_top.ne

omit [BorelSpace (v.adicCompletion K)] in
private theorem real_unitSet_pos : 0 < μ.real (unitSet v) :=
  lt_of_le_of_ne measureReal_nonneg
    (Ne.symm ((measureReal_ne_zero_iff (measure_unitSet_ne_top μ)).mpr (measure_unitSet_ne_zero μ)))

private theorem setIntegral_unitSet_mul_left {c : v.adicCompletion K} (hc : c ∈ unitSet v)
    (h : v.adicCompletion K → ℂ) :
    ∫ u in unitSet v, h (c * u) ∂μ = ∫ u in unitSet v, h u ∂μ := by
  have hc0 : c ≠ 0 := ne_zero_of_mem_unitSet hc
  have hc1 : Valued.v c = 1 := hc
  let e : v.adicCompletion K ≃ᵐ v.adicCompletion K := (Homeomorph.mulLeft₀ c hc0).toMeasurableEquiv
  have he : ⇑e = fun u => c * u := rfl
  have hpre : e ⁻¹' unitSet v = unitSet v := by
    ext u
    simp only [Set.mem_preimage, he, unitSet, Set.mem_setOf_eq, map_mul, hc1, one_mul]

  have hmap : Measure.map e μ = μ := by
    haveI : (Measure.map e μ).IsAddHaarMeasure := by
      rw [he]
      exact Measure.isAddHaarMeasure_map μ (AddMonoidHom.mulLeft c) (continuous_const.mul continuous_id)
        (fun y => ⟨c⁻¹ * y, mul_inv_cancel_left₀ hc0 y⟩)
        (Homeomorph.mulLeft₀ c hc0).isClosedEmbedding.tendsto_cocompact
    have hs := Measure.isAddLeftInvariant_eq_smul (Measure.map e μ) μ
    have hU : Measure.map e μ (unitSet v) = μ (unitSet v) := by
      rw [MeasurableEquiv.map_apply, hpre]
    rw [hs, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hU
    conv_rhs at hU => rw [← one_mul (μ (unitSet v))]
    have hk := (ENNReal.mul_left_inj (measure_unitSet_ne_zero μ) (measure_unitSet_ne_top μ)).mp hU
    rw [hs, show Measure.addHaarScalarFactor (Measure.map e μ) μ = 1 from ENNReal.coe_eq_one.mp hk, one_smul]
  have hrestr : Measure.map e (μ.restrict (unitSet v)) = μ.restrict (unitSet v) := by
    have h1 := e.restrict_map μ (unitSet v)
    rw [hmap, hpre] at h1
    exact h1.symm
  exact integral_comp_of_map_eq e hrestr h

end LocalMeasure

private theorem ideleOf_val_fst (v : HeightOneSpectrum (𝓞 K)) (u : v.adicCompletion K) :
    ((ideleOf v u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := by
  by_cases h : u = 0
  · rw [ideleOf, dif_pos h]
    rfl
  · rw [ideleOf_of_ne_zero v h]
    exact funext fun w => finIdele_val_fst_apply v _ w

private theorem ideleOf_val_snd_self (v : HeightOneSpectrum (𝓞 K)) {u : v.adicCompletion K} (h : u ≠ 0) :
    ((ideleOf v u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = u := by
  rw [ideleOf_of_ne_zero v h]
  exact finIdele_val_snd_self v _

private theorem ideleOf_inv (v : HeightOneSpectrum (𝓞 K)) {u : v.adicCompletion K} (h : u ≠ 0) :
    (ideleOf v u)⁻¹ = ideleOf v u⁻¹ := by
  rw [ideleOf_of_ne_zero v h, ideleOf_of_ne_zero v (inv_ne_zero h), finIdele_inv]
  congr 1
  exact Units.ext rfl

private theorem ideleOf_val_snd_of_ne (v : HeightOneSpectrum (𝓞 K)) (u : v.adicCompletion K)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    ((ideleOf v u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 := by
  by_cases h : u = 0
  · rw [ideleOf, dif_pos h]
    rfl
  · rw [ideleOf_of_ne_zero v h]
    exact finIdele_val_snd_of_ne v _ hw

private theorem inv_mem_unitSet {v : HeightOneSpectrum (𝓞 K)} {u : v.adicCompletion K} (hu : u ∈ unitSet v) :
    u⁻¹ ∈ unitSet v := by
  simp only [unitSet, Set.mem_setOf_eq, map_inv₀] at hu ⊢
  rw [hu, inv_one]

private theorem mem_integers_of_mem_unitSet {v : HeightOneSpectrum (𝓞 K)} {u : v.adicCompletion K}
    (hu : u ∈ unitSet v) : u ∈ v.adicCompletionIntegers K := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  exact le_of_eq hu

private theorem finitePartUnits_ideleOf_mem_unitIdeles (v : HeightOneSpectrum (𝓞 K)) {u : v.adicCompletion K}
    (hu : u ∈ unitSet v) :
    finitePartUnits (𝓞 K) K (ideleOf v u) ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K := by
  have h0 : u ≠ 0 := ne_zero_of_mem_unitSet hu
  rw [ideleOf_of_ne_zero v h0]
  have hmem : finitePartUnits (𝓞 K) K (finIdele v (Units.mk0 u h0)) = localUnit (𝓞 K) K v (Units.mk0 u h0) :=
    Units.ext rfl
  rw [hmem]
  exact localUnit_mem_unitIdeles v (mem_integers_of_mem_unitSet hu) (mem_integers_of_mem_unitSet (inv_mem_unitSet hu))

private theorem ideleNorm_ideleOf (v : HeightOneSpectrum (𝓞 K)) {u : v.adicCompletion K} (hu : u ∈ unitSet v) :
    ideleNorm K (ideleOf v u) = 1 :=
  ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles K _ (ideleOf_val_fst v u)
    (finitePartUnits_ideleOf_mem_unitIdeles v hu)

private theorem ideleOf_mem_unitIdelesOutside (v : HeightOneSpectrum (𝓞 K)) {u : v.adicCompletion K}
    (hu : u ∈ unitSet v) (E : Set (HeightOneSpectrum (𝓞 K))) :
    ideleOf v u ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K E := by
  have h0 : u ≠ 0 := ne_zero_of_mem_unitSet hu
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  intro w _
  show ((ideleOf v u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w ∈ w.adicCompletionIntegers K ∧
    (((ideleOf v u)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w ∈ w.adicCompletionIntegers K
  rw [ideleOf_inv v h0]
  by_cases hw : w = v
  · subst hw
    rw [ideleOf_val_snd_self w h0, ideleOf_val_snd_self w (inv_ne_zero h0)]
    exact ⟨mem_integers_of_mem_unitSet hu, mem_integers_of_mem_unitSet (inv_mem_unitSet hu)⟩
  · rw [ideleOf_val_snd_of_ne v u hw, ideleOf_val_snd_of_ne v u⁻¹ hw]
    exact ⟨one_mem _, one_mem _⟩

private theorem partAt_ideleOf_of_mem {T : Finset (HeightOneSpectrum (𝓞 K))} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ T) (u : v.adicCompletion K) : NumberField.Idele.partAt K T (ideleOf v u) = ideleOf v u := by
  refine Units.ext (Prod.ext (NumberField.Idele.partAt_fst K T _) (IsDedekindDomain.FiniteAdeleRing.ext K fun w => ?_))
  by_cases hw : w ∈ T
  · exact NumberField.Idele.partAt_snd_of_mem K T _ hw
  · rw [NumberField.Idele.partAt_snd_of_not_mem K T _ hw, ideleOf_val_snd_of_ne v u (ne_of_mem_of_not_mem hv hw).symm]

private theorem coe_ideleOf_of_ne_zero (v : HeightOneSpectrum (𝓞 K)) {u : v.adicCompletion K} (h : u ≠ 0) :
    ((ideleOf v u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
      = ((1 : InfiniteAdeleRing K), 1 + StandardAddChar.finAdeleSingleAt K v (u - 1)) := by
  refine Prod.ext (ideleOf_val_fst v u) (IsDedekindDomain.FiniteAdeleRing.ext K fun w => ?_)
  by_cases hw : w = v
  · subst hw
    rw [ideleOf_val_snd_self w h]
    change u = 1 + StandardAddChar.finAdeleSingleAt K w (u - 1) w
    rw [StandardAddChar.finAdeleSingleAt_apply_self, add_sub_cancel]
  · rw [ideleOf_val_snd_of_ne v u hw]
    change (1 : w.adicCompletion K) = 1 + StandardAddChar.finAdeleSingleAt K v (u - 1) w
    rw [StandardAddChar.finAdeleSingleAt_apply_of_ne K v _ hw, add_zero]

private theorem continuousOn_ideleOf_ne_zero (v : HeightOneSpectrum (𝓞 K)) :
    ContinuousOn (ideleOf v) {u : v.adicCompletion K | u ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun u : {u : v.adicCompletion K | u ≠ 0} =>
      ((ideleOf v (u : v.adicCompletion K) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
    have hfun : (fun u : {u : v.adicCompletion K | u ≠ 0} =>
        ((ideleOf v (u : v.adicCompletion K) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))
        = fun u : {u : v.adicCompletion K | u ≠ 0} => (((1 : InfiniteAdeleRing K),
            1 + StandardAddChar.finAdeleSingleAt K v ((u : v.adicCompletion K) - 1)) : AdeleRing (𝓞 K) K) :=
      funext fun u => coe_ideleOf_of_ne_zero v u.2
    rw [hfun]
    exact continuous_const.prodMk (continuous_const.add
      ((StandardAddChar.continuous_finAdeleSingleAt K v).comp (continuous_subtype_val.sub continuous_const)))
  · show Continuous fun u : {u : v.adicCompletion K | u ≠ 0} =>
      (((ideleOf v (u : v.adicCompletion K))⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
    have hfun : (fun u : {u : v.adicCompletion K | u ≠ 0} =>
        (((ideleOf v (u : v.adicCompletion K))⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))
        = fun u : {u : v.adicCompletion K | u ≠ 0} => (((1 : InfiniteAdeleRing K),
            1 + StandardAddChar.finAdeleSingleAt K v ((u : v.adicCompletion K)⁻¹ - 1)) : AdeleRing (𝓞 K) K) :=
      funext fun u => by rw [ideleOf_inv v u.2, coe_ideleOf_of_ne_zero v (inv_ne_zero u.2)]
    rw [hfun]
    exact continuous_const.prodMk (continuous_const.add
      ((StandardAddChar.continuous_finAdeleSingleAt K v).comp
        ((continuous_subtype_val.inv₀ fun u => u.2).sub continuous_const)))

private theorem continuousOn_ideleOf (v : HeightOneSpectrum (𝓞 K)) : ContinuousOn (ideleOf v) (unitSet v) :=
  (continuousOn_ideleOf_ne_zero v).mono fun _ hu => ne_zero_of_mem_unitSet hu

private theorem measurable_ideleOf (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] : @Measurable _ _ _ (NumberField.Idele.ideleBorel K) (ideleOf v) := by
  letI := NumberField.Idele.ideleBorel K
  haveI := NumberField.Idele.borelSpace_ideleBorel K
  refine measurable_of_measurable_on_compl_singleton (0 : v.adicCompletion K) ?_
  exact (continuousOn_iff_continuous_restrict.1 (continuousOn_ideleOf_ne_zero v)).measurable

section Averaging

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

private theorem secondCountableTopology_ideles : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
  haveI hinf : ∀ w : InfinitePlace K, SecondCountableTopology w.Completion := fun w => by
    rcases w.isReal_or_isComplex with hw | hw
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.isEmbedding.secondCountableTopology
    · exact
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.isEmbedding.secondCountableTopology
  haveI h1 : SecondCountableTopology (InfiniteAdeleRing K) :=
    inferInstanceAs (SecondCountableTopology ((w : InfinitePlace K) → w.Completion))
  haveI h2 : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) :=
    RestrictedProduct.secondCountableTopology
      (C := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      (fun _ => Valued.isOpen_valuationSubring _)
  haveI h3 : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
    inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
  haveI h4 : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private noncomputable def avgAt (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) (G : (AdeleRing (𝓞 K) K)ˣ → ℂ) (b : (AdeleRing (𝓞 K) K)ˣ) : ℂ :=
  (∫ u in unitSet v, G (b * ideleOf v u) ∂μ) / ((μ.real (unitSet v) : ℝ) : ℂ)

private noncomputable def avgList [hM : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)) (L : List (HeightOneSpectrum (𝓞 K)))
    (G : (AdeleRing (𝓞 K) K)ˣ → ℂ) : (AdeleRing (𝓞 K) K)ˣ → ℂ :=
  L.foldr (fun v F => avgAt v (μ v) F) G

private theorem avgList_nil [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)) (G : (AdeleRing (𝓞 K) K)ˣ → ℂ) :
    avgList μ [] G = G := rfl

private theorem avgList_cons [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)) (v : HeightOneSpectrum (𝓞 K))
    (L : List (HeightOneSpectrum (𝓞 K))) (G : (AdeleRing (𝓞 K) K)ˣ → ℂ) :
    avgList μ (v :: L) G = avgAt v (μ v) (avgList μ L G) := rfl

private theorem map_mulRight_ideleOf_eq (T : Finset (HeightOneSpectrum (𝓞 K))) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ T) {u : v.adicCompletion K} (hu : u ∈ unitSet v) :
    Measure.map (MeasurableEquiv.mulRight (ideleOf v u)) (NumberField.Idele.productMeasureData K T).νS
      = (NumberField.Idele.productMeasureData K T).νS := by
  haveI := NumberField.Idele.borelSpace_ideleBorel K
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  have hg : ideleOf v u ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑T : Set (HeightOneSpectrum (𝓞 K))) :=
    ideleOf_mem_unitIdelesOutside v hu _
  have hmr : Measurable fun b : (AdeleRing (𝓞 K) K)ˣ => b * ideleOf v u := (continuous_mul_const _).measurable
  have hmp := NumberField.Idele.measurable_partAt K T
  have hcomm : (fun b : (AdeleRing (𝓞 K) K)ˣ => b * ideleOf v u) ∘ NumberField.Idele.partAt K T
      = NumberField.Idele.partAt K T ∘ fun a => a * ideleOf v u := by
    funext a
    simp only [Function.comp_apply, map_mul, partAt_ideleOf_of_mem hv u]
  have hpre : (fun a : (AdeleRing (𝓞 K) K)ˣ => ideleOf v u * a) ⁻¹'
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑T : Set (HeightOneSpectrum (𝓞 K))) :
        Set (AdeleRing (𝓞 K) K)ˣ)
      = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑T : Set (HeightOneSpectrum (𝓞 K))) :
        Set (AdeleRing (𝓞 K) K)ˣ) := by
    ext a
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mul_mem_cancel_left _ hg]
  have hleft : Measure.map (fun a : (AdeleRing (𝓞 K) K)ˣ => ideleOf v u * a)
      ((NumberField.Idele.idelicHaar K).restrict
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑T : Set (HeightOneSpectrum (𝓞 K))) :
          Set (AdeleRing (𝓞 K) K)ˣ))
      = (NumberField.Idele.idelicHaar K).restrict
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑T : Set (HeightOneSpectrum (𝓞 K))) :
          Set (AdeleRing (𝓞 K) K)ˣ) := by
    have h1 := (MeasurableEquiv.mulLeft (ideleOf v u)).restrict_map (NumberField.Idele.idelicHaar K)
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑T : Set (HeightOneSpectrum (𝓞 K))) :
        Set (AdeleRing (𝓞 K) K)ˣ)
    simp only [MeasurableEquiv.coe_mulLeft] at h1
    rw [map_mul_left_eq_self, hpre] at h1
    exact h1.symm
  have hfun : (fun a : (AdeleRing (𝓞 K) K)ˣ => a * ideleOf v u) = fun a => ideleOf v u * a :=
    funext fun a => mul_comm a _
  show Measure.map (fun b => b * ideleOf v u) (Measure.map (NumberField.Idele.partAt K T) _)
    = Measure.map (NumberField.Idele.partAt K T) _
  rw [Measure.map_map hmr hmp, hcomm, ← Measure.map_map hmp hmr, hfun, hleft]

private theorem integral_mul_ideleOf_eq (T : Finset (HeightOneSpectrum (𝓞 K))) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ T) {u : v.adicCompletion K} (hu : u ∈ unitSet v) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : (AdeleRing (𝓞 K) K)ˣ → E) :
    ∫ b, G (b * ideleOf v u) ∂(NumberField.Idele.productMeasureData K T).νS
      = ∫ b, G b ∂(NumberField.Idele.productMeasureData K T).νS :=
  integral_comp_of_map_eq (MeasurableEquiv.mulRight (ideleOf v u)) (map_mulRight_ideleOf_eq T hv hu) G

private theorem integrable_avgAt_and_integral_avgAt (T : Finset (HeightOneSpectrum (𝓞 K)))
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ T) [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] {G : (AdeleRing (𝓞 K) K)ˣ → ℂ}
    (hG : Integrable G (NumberField.Idele.productMeasureData K T).νS) :
    Integrable (avgAt v μ G) (NumberField.Idele.productMeasureData K T).νS ∧
      ∫ b, avgAt v μ G b ∂(NumberField.Idele.productMeasureData K T).νS
        = ∫ b, G b ∂(NumberField.Idele.productMeasureData K T).νS := by
  haveI := NumberField.Idele.borelSpace_ideleBorel K
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  haveI := secondCountableTopology_ideles (K := K)
  haveI : SFinite (NumberField.Idele.productMeasureData K T).νS := by
    show SFinite (Measure.map (NumberField.Idele.partAt K T) _)
    infer_instance
  haveI : IsFiniteMeasure (μ.restrict (unitSet v)) := isFiniteMeasure_restrict.2 (measure_unitSet_ne_top μ)
  have hmeasU : MeasurableSet (unitSet v) := (isOpen_unitSet v).measurableSet

  have hΦ : Measurable fun p : (AdeleRing (𝓞 K) K)ˣ × v.adicCompletion K => p.1 * ideleOf v p.2 :=
    measurable_fst.mul ((measurable_ideleOf v).comp measurable_snd)
  have hsec : ∀ c ∈ unitSet v, ∀ N : Set (AdeleRing (𝓞 K) K)ˣ,
      (NumberField.Idele.productMeasureData K T).νS {b | b * ideleOf v c ∈ N}
        = (NumberField.Idele.productMeasureData K T).νS N := by
    intro c hc N
    have h := congrArg (fun ρ : Measure (AdeleRing (𝓞 K) K)ˣ => ρ N) (map_mulRight_ideleOf_eq T hv hc)
    simp only [MeasurableEquiv.map_apply] at h
    exact h
  have hqmp : Measure.QuasiMeasurePreserving
      (fun p : (AdeleRing (𝓞 K) K)ˣ × v.adicCompletion K => p.1 * ideleOf v p.2)
      ((NumberField.Idele.productMeasureData K T).νS.prod (μ.restrict (unitSet v)))
      (NumberField.Idele.productMeasureData K T).νS := by
    refine ⟨hΦ, Measure.AbsolutelyContinuous.mk fun N hN hN0 => ?_⟩
    rw [Measure.map_apply hΦ hN, Measure.prod_apply_symm (hΦ hN)]
    have hae : ∀ᵐ c ∂(μ.restrict (unitSet v)),
        (NumberField.Idele.productMeasureData K T).νS
          ((fun b => (b, c)) ⁻¹' ((fun p : (AdeleRing (𝓞 K) K)ˣ × v.adicCompletion K => p.1 * ideleOf v p.2) ⁻¹' N))
          = 0 := by
      filter_upwards [ae_restrict_mem hmeasU] with c hc
      exact (hsec c hc N).trans hN0
    rw [lintegral_congr_ae hae, lintegral_zero]
  have hFm : AEStronglyMeasurable
      (fun p : (AdeleRing (𝓞 K) K)ˣ × v.adicCompletion K => G (p.1 * ideleOf v p.2))
      ((NumberField.Idele.productMeasureData K T).νS.prod (μ.restrict (unitSet v))) :=
    hG.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
  have hF : Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × v.adicCompletion K => G (p.1 * ideleOf v p.2))
      ((NumberField.Idele.productMeasureData K T).νS.prod (μ.restrict (unitSet v))) := by
    rw [integrable_prod_iff' hFm]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem hmeasU] with c hc
      have h := (integrable_map_equiv (MeasurableEquiv.mulRight (ideleOf v c)) G).1
        (by rw [map_mulRight_ideleOf_eq T hv hc]; exact hG)
      exact h
    · refine (integrable_const (∫ b, ‖G b‖ ∂(NumberField.Idele.productMeasureData K T).νS)).congr ?_
      filter_upwards [ae_restrict_mem hmeasU] with c hc
      exact (integral_mul_ideleOf_eq T hv hc fun b => ‖G b‖).symm
  have hint : Integrable (fun b => ∫ c in unitSet v, G (b * ideleOf v c) ∂μ)
      (NumberField.Idele.productMeasureData K T).νS := hF.integral_prod_left
  have hval : ∫ b, (∫ c in unitSet v, G (b * ideleOf v c) ∂μ) ∂(NumberField.Idele.productMeasureData K T).νS
      = μ.real (unitSet v) • ∫ b, G b ∂(NumberField.Idele.productMeasureData K T).νS := by
    rw [← integral_prod _ hF, integral_prod_symm _ hF]
    have hae : ∀ᵐ c ∂(μ.restrict (unitSet v)),
        (∫ b, G (b * ideleOf v c) ∂(NumberField.Idele.productMeasureData K T).νS)
          = ∫ b, G b ∂(NumberField.Idele.productMeasureData K T).νS := by
      filter_upwards [ae_restrict_mem hmeasU] with c hc
      exact integral_mul_ideleOf_eq T hv hc G
    rw [integral_congr_ae hae, integral_const, measureReal_restrict_apply_univ]
  have hm : ((μ.real (unitSet v) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (real_unitSet_pos μ).ne'
  refine ⟨hint.div_const _, ?_⟩
  show ∫ b, (∫ u in unitSet v, G (b * ideleOf v u) ∂μ) / ((μ.real (unitSet v) : ℝ) : ℂ)
      ∂(NumberField.Idele.productMeasureData K T).νS = _
  rw [integral_div, hval, Complex.real_smul]
  exact mul_div_cancel_left₀ _ hm

private theorem integrable_avgList_and_integral_avgList (T : Finset (HeightOneSpectrum (𝓞 K)))
    [hM : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [hB : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
    [hμ : ∀ v : HeightOneSpectrum (𝓞 K), (μ v).IsAddHaarMeasure]
    (L : List (HeightOneSpectrum (𝓞 K))) (hLT : ∀ v ∈ L, v ∈ T) {G : (AdeleRing (𝓞 K) K)ˣ → ℂ}
    (hG : Integrable G (NumberField.Idele.productMeasureData K T).νS) :
    Integrable (avgList μ L G) (NumberField.Idele.productMeasureData K T).νS ∧
      ∫ b, avgList μ L G b ∂(NumberField.Idele.productMeasureData K T).νS
        = ∫ b, G b ∂(NumberField.Idele.productMeasureData K T).νS := by
  induction L with
  | nil => exact ⟨hG, rfl⟩
  | cons v L ih =>
    obtain ⟨h1, h2⟩ := ih fun w hw => hLT w (List.mem_cons_of_mem v hw)
    obtain ⟨h3, h4⟩ := integrable_avgAt_and_integral_avgAt T (hLT v (List.mem_cons_self ..)) (μ v) h1
    exact ⟨by rw [avgList_cons]; exact h3, by rw [avgList_cons, h4, h2]⟩

private theorem integral_eq_setIntegral_partAt (T : Finset (HeightOneSpectrum (𝓞 K))) {H : (AdeleRing (𝓞 K) K)ˣ → ℂ}
    (hH : AEStronglyMeasurable H (NumberField.Idele.productMeasureData K T).νS) :
    ∫ b, H b ∂(NumberField.Idele.productMeasureData K T).νS
      = ∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑T : Set (HeightOneSpectrum (𝓞 K))) :
          Set (AdeleRing (𝓞 K) K)ˣ), H (NumberField.Idele.partAt K T a) ∂(NumberField.Idele.idelicHaar K) :=
  integral_map (NumberField.Idele.measurable_partAt K T).aemeasurable hH

end Averaging

section Shells

variable (ϖ : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
  (hπ : ∀ v : HeightOneSpectrum (𝓞 K),
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ≠ 0)

private noncomputable def piUnit (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ :=
  Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v)

private noncomputable def shell (v : HeightOneSpectrum (𝓞 K)) (k : ℤ) : (AdeleRing (𝓞 K) K)ˣ :=
  finIdele v (piUnit ϖ hπ v) ^ k

private theorem finIdele_zpow (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) (k : ℤ) :
    finIdele v (t ^ k) = finIdele v t ^ k := by
  unfold finIdele
  rw [map_zpow, map_zpow]

private theorem finIdele_mul (v : HeightOneSpectrum (𝓞 K)) (t t' : (v.adicCompletion K)ˣ) :
    finIdele v (t * t') = finIdele v t * finIdele v t' := by
  unfold finIdele
  rw [map_mul, map_mul]

private theorem shell_add (v : HeightOneSpectrum (𝓞 K)) (k k' : ℤ) :
    shell ϖ hπ v (k + k') = shell ϖ hπ v k * shell ϖ hπ v k' := by
  unfold shell
  exact zpow_add _ k k'

private theorem shell_val_fst (v : HeightOneSpectrum (𝓞 K)) (k : ℤ) :
    ((shell ϖ hπ v k : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := by
  unfold shell
  rw [← finIdele_zpow]
  exact funext (finIdele_val_fst_apply v _)

private theorem shell_val_snd_self (v : HeightOneSpectrum (𝓞 K)) (k : ℤ) :
    ((shell ϖ hπ v k : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v
      = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ^ k := by
  unfold shell
  rw [← finIdele_zpow, finIdele_val_snd_self, Units.val_zpow_eq_zpow_val]
  rfl

private theorem shell_val_snd_of_ne (v : HeightOneSpectrum (𝓞 K)) (k : ℤ) {w : HeightOneSpectrum (𝓞 K)}
    (hw : w ≠ v) : ((shell ϖ hπ v k : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 := by
  unfold shell
  rw [← finIdele_zpow, finIdele_val_snd_of_ne v _ hw]

private theorem valued_pi_zpow {v : HeightOneSpectrum (𝓞 K)}
    (hv : Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ^ k) = WithZero.exp (-k) := by
  have h : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) = WithZero.exp (-1 : ℤ) :=
    hv
  rw [map_zpow₀, h, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one]

end Shells

section ProductComponents

private theorem list_prod_val_fst_eq_one (L : List (HeightOneSpectrum (𝓞 K)))
    (F : HeightOneSpectrum (𝓞 K) → (AdeleRing (𝓞 K) K)ˣ)
    (hF : ∀ w ∈ L, ((F w : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1) :
    (((L.map F).prod : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := by
  induction L with
  | nil => rfl
  | cons w L ih =>
    rw [List.map_cons, List.prod_cons, val_mul_fst, hF w (List.mem_cons_self ..),
      ih fun w' hw' => hF w' (List.mem_cons_of_mem _ hw'), one_mul]

private theorem list_prod_val_snd_eq_one (L : List (HeightOneSpectrum (𝓞 K)))
    (F : HeightOneSpectrum (𝓞 K) → (AdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hF : ∀ w ∈ L, ((F w : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1) :
    (((L.map F).prod : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 := by
  induction L with
  | nil => rfl
  | cons w L ih =>
    rw [List.map_cons, List.prod_cons, val_mul_snd_apply, hF w (List.mem_cons_self ..),
      ih fun w' hw' => hF w' (List.mem_cons_of_mem _ hw'), one_mul]

private theorem list_prod_val_snd_of_mem {L : List (HeightOneSpectrum (𝓞 K))} (hL : L.Nodup)
    (F : HeightOneSpectrum (𝓞 K) → (AdeleRing (𝓞 K) K)ˣ)
    (hF : ∀ w ∈ L, ∀ v, v ≠ w → ((F w : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ L) :
    (((L.map F).prod : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v
      = ((F v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v := by
  induction L with
  | nil => exact (List.not_mem_nil hv).elim
  | cons w L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, val_mul_snd_apply]
    rcases List.mem_cons.mp hv with rfl | hvL
    · rw [list_prod_val_snd_eq_one L F v fun w' hw' => hF w' (List.mem_cons_of_mem _ hw') v
        fun h => hL.1 (h ▸ hw'), mul_one]
    · have hvw : v ≠ w := fun h => hL.1 (h ▸ hvL)
      rw [hF w (List.mem_cons_self ..) v hvw, one_mul]
      exact ih hL.2 (fun w' hw' => hF w' (List.mem_cons_of_mem _ hw')) hvL

private theorem list_prod_val_snd_of_not_mem (L : List (HeightOneSpectrum (𝓞 K)))
    (F : HeightOneSpectrum (𝓞 K) → (AdeleRing (𝓞 K) K)ˣ)
    (hF : ∀ w ∈ L, ∀ v, v ≠ w → ((F w : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ L) :
    (((L.map F).prod : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 :=
  list_prod_val_snd_eq_one L F v fun w hw => hF w hw v fun h => hv (h ▸ hw)

private theorem finitePartUnits_list_prod_mem (L : List (HeightOneSpectrum (𝓞 K)))
    (F : HeightOneSpectrum (𝓞 K) → (AdeleRing (𝓞 K) K)ˣ)
    (hF : ∀ w ∈ L, finitePartUnits (𝓞 K) K (F w) ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K) :
    finitePartUnits (𝓞 K) K (L.map F).prod ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K := by
  rw [map_list_prod]
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  rw [List.map_map, List.mem_map] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact hF w hw

end ProductComponents

section Dilation

variable (ϖ : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
  (hπ : ∀ v : HeightOneSpectrum (𝓞 K),
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ≠ 0)

private noncomputable def lev (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v)

private noncomputable def dilator (L : List (HeightOneSpectrum (𝓞 K))) : (AdeleRing (𝓞 K) K)ˣ :=
  (L.map fun v => shell ϖ hπ v (-lev (K := K) v)).prod

private noncomputable def dilateChar (δ : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    AddChar (v.adicCompletion K) ℂ :=
  (StandardAddChar.psiLocal K v).compAddMonoidHom
    (AddMonoidHom.mulLeft (((δ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v))

private theorem dilateChar_apply (δ : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletion K) :
    dilateChar δ v y
      = StandardAddChar.psiLocal K v (((δ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v * y) := rfl

private theorem psiLocal_level_facts (v : HeightOneSpectrum (𝓞 K)) :
    (∀ y : v.adicCompletion K, Valued.v y ≤ WithZero.exp (lev (K := K) v) → StandardAddChar.psiLocal K v y = 1) ∧
      ∃ y : v.adicCompletion K, Valued.v y ≤ WithZero.exp (lev (K := K) v + 1) ∧
        StandardAddChar.psiLocal K v y ≠ 1 := by
  unfold lev
  exact LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel K v (StandardAddChar.psiLocal K v)
    ⟨0, fun y hy => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers K v y
      ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (by simpa using hy))⟩
    (LanglandsTunnell.TateLocal.psiLocal_ne_one K v)

private theorem dilator_val_snd {L : List (HeightOneSpectrum (𝓞 K))} (hL : L.Nodup) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ L) :
    ((dilator ϖ hπ L : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v
      = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ^ (-lev (K := K) v) := by
  unfold dilator
  rw [list_prod_val_snd_of_mem hL _ (fun w _ v' hv' => shell_val_snd_of_ne ϖ hπ w _ hv') hv, shell_val_snd_self]

private theorem dilateChar_dilator_eq_one {L : List (HeightOneSpectrum (𝓞 K))} (hL : L.Nodup)
    (hϖ : ∀ v ∈ L, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ L) (r : v.adicCompletionIntegers K) :
    dilateChar (dilator ϖ hπ L) v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1 := by
  rw [dilateChar_apply, dilator_val_snd ϖ hπ hL hv]
  refine (psiLocal_level_facts v).1 _ ?_
  rw [map_mul, valued_pi_zpow ϖ (hϖ v hv), neg_neg]
  have hr : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) ≤ 1 :=
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp r.2
  exact mul_le_of_le_one_right' hr

private theorem exists_dilateChar_dilator_ne_one {L : List (HeightOneSpectrum (𝓞 K))} (hL : L.Nodup)
    (hϖ : ∀ v ∈ L, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ L) :
    ∃ r : v.adicCompletionIntegers K,
      dilateChar (dilator ϖ hπ L) v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) ≠ 1 := by
  obtain ⟨y, hy, hy1⟩ := (psiLocal_level_facts (K := K) v).2
  set π : v.adicCompletion K := algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) with hπdef
  have hπ0 : π ≠ 0 := hπ v
  have hπval : ∀ k : ℤ, Valued.v (π ^ k) = WithZero.exp (-k) := valued_pi_zpow ϖ (hϖ v hv)

  have hr : y * π ^ (lev (K := K) v + 1) ∈ v.adicCompletionIntegers K := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hπval]
    calc Valued.v y * WithZero.exp (-(lev (K := K) v + 1))
        ≤ WithZero.exp (lev (K := K) v + 1) * WithZero.exp (-(lev (K := K) v + 1)) := mul_le_mul' hy le_rfl
      _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  refine ⟨⟨y * π ^ (lev (K := K) v + 1), hr⟩, ?_⟩
  rw [dilateChar_apply, dilator_val_snd ϖ hπ hL hv]

  have hcalc : π ^ (-lev (K := K) v) * (y * π ^ (lev (K := K) v + 1) / π) = y := by
    have hl : π ^ lev (K := K) v ≠ 0 := zpow_ne_zero _ hπ0
    rw [zpow_add_one₀ hπ0, _root_.zpow_neg]
    field_simp
  have hcoe : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (⟨y * π ^ (lev (K := K) v + 1), hr⟩ : v.adicCompletionIntegers K) = y * π ^ (lev (K := K) v + 1) := rfl
  rw [hcoe, ← hπdef, hcalc]
  exact hy1

private theorem diagOne_mul_placeEmbed_of_snd_eq_one {t : (AdeleRing (𝓞 K) K)ˣ} {v : HeightOneSpectrum (𝓞 K)}
    (ht : ((t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1) (h : GL (Fin 2) (v.adicCompletion K)) :
    (diagOne t : AdelicGL2 (𝓞 K) K) * placeEmbed K v h = placeEmbed K v h * diagOne t := by
  have hunit : unitAt v t = 1 := Units.ext (by rw [unitAt_val, ht]; rfl)
  refine ext_of_glArch_of_compAt ?_ fun w => ?_
  · rw [map_mul, map_mul, glArch_placeEmbed, mul_one, one_mul]
  · rw [map_mul, map_mul]
    by_cases hw : w = v
    · subst hw
      rw [compAt_placeEmbed_self, compAt_diagOne, hunit, map_one, mul_one, one_mul]
    · rw [compAt_placeEmbed_of_ne hw, mul_one, one_mul]

private theorem diagZ_eq_diagOne_piUnit (v : HeightOneSpectrum (𝓞 K)) (k : ℤ) :
    diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v) k
      = diagOne (piUnit ϖ hπ v ^ k) := by
  ext i j
  rw [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [diagZ, piUnit, Units.val_zpow_eq_zpow_val]

private theorem diagOne_shell (v : HeightOneSpectrum (𝓞 K)) (k : ℤ) :
    (diagOne (shell ϖ hπ v k) : AdelicGL2 (𝓞 K) K)
      = placeEmbed K v (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v) k) := by
  rw [diagZ_eq_diagOne_piUnit, ← diagOne_finIdele, shell, finIdele_zpow]

private theorem apply_diagOne_mul_prod_shell (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (lam om : HeightOneSpectrum (𝓞 K) → ℂ)
    {I : HeightOneSpectrum (𝓞 K) → Type} [∀ v, Fintype (I v)] [∀ v, Nonempty (I v)]
    (b : ∀ v : HeightOneSpectrum (𝓞 K), I v → v.adicCompletionIntegers K)
    {L : List (HeightOneSpectrum (𝓞 K))} (hL : L.Nodup)
    (hϖ : ∀ v ∈ L, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (hN : ∀ v ∈ L, ∀ (y : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (placeEmbed K v (unipotent y) * g) = StandardAddChar.psiLocal K v y * W g)
    (hK : ∀ v ∈ L, ∀ (r : v.adicCompletionIntegers K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (g * placeEmbed K v (unipotent
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r))) = W g)
    (hT : ∀ v ∈ L, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v)
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b v i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v))) =
        lam v * W g)
    (hZ : ∀ v ∈ L, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v))) =
        om v * W g)
    {t : (AdeleRing (𝓞 K) K)ˣ} (ht : ∀ v ∈ L, ((t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1)
    (m : HeightOneSpectrum (𝓞 K) → ℤ) :
    W (diagOne (t * (L.map fun v => shell ϖ hπ v (m v)).prod))
      = W (diagOne (dilator ϖ hπ L) * diagOne t)
          * (L.map fun v => torusFactor (Fintype.card (I v)) (lam v) (om v) (m v + lev (K := K) v)).prod := by

  set Wd : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ := fun g => W (diagOne (dilator ϖ hπ L) * g) with hWd
  have hchild := UnramifiedWhittaker.apply_mul_prod_placeEmbed_diagZ_eq_mul_prod_torusFactor Wd
    (fun v => dilateChar (dilator ϖ hπ L) v) ϖ hπ lam om b L hL
    (fun v hv r => dilateChar_dilator_eq_one ϖ hπ hL hϖ hv r)
    (fun v hv => exists_dilateChar_dilator_ne_one ϖ hπ hL hϖ hv)
    (fun v hv y g => by
      simp only [hWd]
      rw [← mul_assoc, diagOne_mul_placeEmbed_unipotent, mul_assoc, hN v hv, dilateChar_apply])
    (fun v hv r g => by
      simp only [hWd]
      rw [← mul_assoc]
      exact hK v hv r (diagOne (dilator ϖ hπ L) * g))
    (fun v hv g => by
      simp only [hWd]
      have h := hT v hv (diagOne (dilator ϖ hπ L) * g)
      simp only [mul_assoc] at h
      exact h)
    (fun v hv g => by
      simp only [hWd]
      have h := hZ v hv (diagOne (dilator ϖ hπ L) * g)
      rw [mul_assoc] at h
      exact h)
    (diagOne t) (fun v hv h => diagOne_mul_placeEmbed_of_snd_eq_one (ht v hv) h)
    (fun v => m v + lev (K := K) v)
  simp only [hWd] at hchild

  have hpoint : (diagOne (dilator ϖ hπ L) : AdelicGL2 (𝓞 K) K) * (diagOne t *
      (L.map fun v => placeEmbed K v (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v))
        (hπ v) (m v + lev (K := K) v))).prod)
      = diagOne (t * (L.map fun v => shell ϖ hπ v (m v)).prod) := by
    have hshells : (L.map fun v => placeEmbed K v (diagZ (algebraMap (v.adicCompletionIntegers K)
        (v.adicCompletion K) (ϖ v)) (hπ v) (m v + lev (K := K) v))).prod
        = diagOne (L.map fun v => shell ϖ hπ v (m v + lev (K := K) v)).prod := by
      rw [map_list_prod, List.map_map]
      congr 1
      exact List.map_congr_left fun v _ => (diagOne_shell ϖ hπ v _).symm
    have hdil : dilator ϖ hπ L * (L.map fun v => shell ϖ hπ v (m v + lev (K := K) v)).prod
        = (L.map fun v => shell ϖ hπ v (m v)).prod := by
      unfold dilator
      rw [← List.prod_map_mul]
      congr 1
      refine List.map_congr_left fun v _ => ?_
      rw [← shell_add]
      congr 1
      ring
    rw [hshells, ← map_mul, ← map_mul, mul_left_comm, hdil]
  rw [← hpoint]
  exact hchild

end Dilation

section AveragingFactor

private theorem avgList_eq_of_forall [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
    (h : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K → ℂ) (L : List (HeightOneSpectrum (𝓞 K))) :
    L.Nodup → ∀ (Φ : (AdeleRing (𝓞 K) K)ˣ → ℂ) (b₀ : (AdeleRing (𝓞 K) K)ˣ) (C : ℂ),
      (∀ u : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K, (∀ w ∈ L, u w ∈ unitSet w) →
        Φ (b₀ * (L.map fun w => ideleOf w (u w)).prod) = C * (L.map fun w => h w (u w)).prod) →
      avgList μ L Φ b₀
        = C * (L.map fun w => (∫ t in unitSet w, h w t ∂(μ w)) / (((μ w).real (unitSet w) : ℝ) : ℂ)).prod := by
  induction L with
  | nil =>
    intro _ Φ b₀ C hΦ
    have h0 := hΦ (fun _ => 1) fun w hw => (List.not_mem_nil hw).elim
    simp only [List.map_nil, List.prod_nil, mul_one] at h0
    rw [avgList_nil]
    simp only [List.map_nil, List.prod_nil, mul_one]
    exact h0
  | cons v L ih =>
    intro hL Φ b₀ C hΦ
    classical
    rw [List.nodup_cons] at hL
    rw [avgList_cons]
    show (∫ t in unitSet v, avgList μ L Φ (b₀ * ideleOf v t) ∂(μ v)) / (((μ v).real (unitSet v) : ℝ) : ℂ) = _
    have hinner : ∀ t ∈ unitSet v, avgList μ L Φ (b₀ * ideleOf v t)
        = (C * (L.map fun w => (∫ r in unitSet w, h w r ∂(μ w)) / (((μ w).real (unitSet w) : ℝ) : ℂ)).prod)
            * h v t := by
      intro t ht
      refine (ih hL.2 Φ (b₀ * ideleOf v t) (C * h v t) fun u hu => ?_).trans (mul_right_comm _ _ _)
      have hu' : ∀ w ∈ v :: L, Function.update u v t w ∈ unitSet w := by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hwL
        · rw [Function.update_self]
          exact ht
        · rw [Function.update_of_ne fun h' : w = v => hL.1 (h' ▸ hwL)]
          exact hu w hwL
      have h1 := hΦ (Function.update u v t) hu'
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, Function.update_self] at h1
      have hmap1 : (L.map fun w => ideleOf w (Function.update u v t w)) = L.map fun w => ideleOf w (u w) :=
        List.map_congr_left fun w hw => by rw [Function.update_of_ne fun h' : w = v => hL.1 (h' ▸ hw)]
      have hmap2 : (L.map fun w => h w (Function.update u v t w)) = L.map fun w => h w (u w) :=
        List.map_congr_left fun w hw => by rw [Function.update_of_ne fun h' : w = v => hL.1 (h' ▸ hw)]
      rw [hmap1, hmap2, ← mul_assoc, ← mul_assoc] at h1
      exact h1
    rw [setIntegral_congr_fun measurableSet_unitSet fun t ht => hinner t ht, integral_const_mul,
      List.map_cons, List.prod_cons]
    ring

end AveragingFactor

section NormOfShells

private noncomputable def ideleNormHom : (AdeleRing (𝓞 K) K)ˣ →* ℝ where
  toFun := ideleNorm K
  map_one' := by
    have h := ideleNorm_mul (1 : (AdeleRing (𝓞 K) K)ˣ) 1
    rw [mul_one] at h
    exact mul_left_cancel₀ (ideleNorm_pos (1 : (AdeleRing (𝓞 K) K)ˣ)).ne' (h.symm.trans (mul_one _).symm)
  map_mul' := ideleNorm_mul

private theorem ideleNormHom_apply (z : (AdeleRing (𝓞 K) K)ˣ) : ideleNormHom z = ideleNorm K z := rfl

variable (ϖ : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
  (hπ : ∀ v : HeightOneSpectrum (𝓞 K),
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ≠ 0)

private theorem finIdele_one_eq (v : HeightOneSpectrum (𝓞 K)) : finIdele v 1 = 1 := by
  unfold finIdele
  rw [map_one, map_one]

private theorem ideleNorm_finIdele_piUnit {v : HeightOneSpectrum (𝓞 K)}
    (hv : Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    ideleNorm K (finIdele v (piUnit ϖ hπ v)) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  set e : (v.adicCompletion K)ˣ := (uniformizerUnit K v)⁻¹ * piUnit ϖ hπ v with he
  have hsplit : finIdele v (piUnit ϖ hπ v) = uniformizerIdele K v * finIdele v e := by
    have hu : uniformizerIdele K v = finIdele v (uniformizerUnit K v) := rfl
    rw [hu, he, finIdele_mul, ← mul_assoc, ← finIdele_mul, mul_inv_cancel, finIdele_one_eq, one_mul]
  have he_unit : (e : v.adicCompletion K) ∈ unitSet v := by
    show Valued.v ((e : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1
    have hpi : Valued.v ((piUnit ϖ hπ v : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := hv
    rw [he, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, valued_uniformizerUnit K v, hpi,
      inv_mul_cancel₀ WithZero.exp_ne_zero]
  have hnorm_e : ideleNorm K (finIdele v e) = 1 := by
    have h := ideleNorm_ideleOf v he_unit
    rwa [ideleOf_of_ne_zero v (ne_zero_of_mem_unitSet he_unit), Units.mk0_val] at h
  rw [hsplit, ideleNorm_mul, hnorm_e, mul_one]
  exact NumberField.TateGlobal.ideleNorm_uniformizerIdele K v

include hπ in

private theorem absNorm_pos_of_piUnit {v : HeightOneSpectrum (𝓞 K)}
    (hv : Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h := ideleNorm_pos (finIdele v (piUnit ϖ hπ v))
  rw [ideleNorm_finIdele_piUnit ϖ hπ hv] at h
  exact inv_pos.mp h

end NormOfShells

section ComplexPowers

private theorem ofReal_inv_zpow_cpow {n : ℕ} (hn : (0 : ℝ) < (n : ℝ)) (m : ℤ) (s : ℂ) :
    ((((n : ℝ))⁻¹ ^ m : ℝ) : ℂ) ^ (s - 1) = ((n : ℂ) ^ (1 - s)) ^ m := by
  have hn0 : ((n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  have hbase : ((((n : ℝ))⁻¹ ^ m : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zpow_ne_zero m (inv_ne_zero hn.ne'))
  have hlog : Complex.log ((((n : ℝ))⁻¹ ^ m : ℝ) : ℂ) = -(m : ℂ) * (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log (zpow_nonneg (inv_nonneg.mpr hn.le) m), Real.log_zpow, Real.log_inv]
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_intCast]
    ring
  rw [← Complex.ofReal_natCast, Complex.cpow_def_of_ne_zero hbase, Complex.cpow_def_of_ne_zero hn0,
    ← Complex.ofReal_log hn.le, hlog, ← Complex.exp_int_mul]
  congr 1
  ring

omit [NumberField K] in

private theorem ofReal_list_prod_cpow (L : List (HeightOneSpectrum (𝓞 K))) (f : HeightOneSpectrum (𝓞 K) → ℝ)
    (hf : ∀ w ∈ L, 0 ≤ f w) (r : ℂ) :
    (((L.map f).prod : ℝ) : ℂ) ^ r = (L.map fun w => ((f w : ℝ) : ℂ) ^ r).prod := by
  induction L with
  | nil => simp
  | cons w L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf w (List.mem_cons_self ..))
        (List.prod_nonneg fun y hy => by
          rw [List.mem_map] at hy
          obtain ⟨w', hw', rfl⟩ := hy
          exact hf w' (List.mem_cons_of_mem _ hw')),
      ih fun w' hw' => hf w' (List.mem_cons_of_mem _ hw')]

end ComplexPowers

section Factorisation

variable (ϖ : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
  (hπ : ∀ v : HeightOneSpectrum (𝓞 K),
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ≠ 0)

private noncomputable def ecomp (v : HeightOneSpectrum (𝓞 K)) (a : (AdeleRing (𝓞 K) K)ˣ) : v.adicCompletion K :=
  ((a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v
    * algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ^ (-NumberField.Idele.ord K v a)

private theorem ecomp_mem_unitSet {v : HeightOneSpectrum (𝓞 K)}
    (hv : Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) (a : (AdeleRing (𝓞 K) K)ˣ) :
    ecomp ϖ v a ∈ unitSet v := by
  show Valued.v (_ * _) = 1
  rw [map_mul, NumberField.Idele.valued_snd_eq_exp_neg_ord, valued_pi_zpow ϖ hv, neg_neg, ← WithZero.exp_add,
    neg_add_cancel, WithZero.exp_zero]

private theorem mul_mul_inv_mul_eq {F : Type} [Field F] {p : F} (hp : p ≠ 0) (c d : F) :
    p * (c * p⁻¹ * d) = c * d := by
  calc p * (c * p⁻¹ * d) = c * d * (p * p⁻¹) := by ring
    _ = c * d := by rw [mul_inv_cancel₀ hp, mul_one]

private theorem partAt_mul_prod_ideleOf_eq (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : S ⊆ T)
    {L : List (HeightOneSpectrum (𝓞 K))} (hL : L.Nodup)
    (hLT : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ L ↔ v ∈ T ∧ v ∉ S)
    (hϖ : ∀ v ∈ L, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (a : (AdeleRing (𝓞 K) K)ˣ) (u : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K)
    (hu : ∀ w ∈ L, u w ∈ unitSet w) :
    NumberField.Idele.partAt K T a * (L.map fun w => ideleOf w (u w)).prod
      = NumberField.Idele.partAt K S a
          * ((L.map fun w => shell ϖ hπ w (NumberField.Idele.ord K w a)).prod
              * (L.map fun w => ideleOf w (ecomp ϖ w a * u w)).prod) := by
  have hsupp_u : ∀ w ∈ L, ∀ v, v ≠ w → ((ideleOf w (u w) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 :=
    fun w _ v hv => ideleOf_val_snd_of_ne w _ hv
  have hsupp_sh : ∀ w ∈ L, ∀ v, v ≠ w →
      ((shell ϖ hπ w (NumberField.Idele.ord K w a) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 :=
    fun w _ v hv => shell_val_snd_of_ne ϖ hπ w _ hv
  have hsupp_e : ∀ w ∈ L, ∀ v, v ≠ w →
      ((ideleOf w (ecomp ϖ w a * u w) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 :=
    fun w _ v hv => ideleOf_val_snd_of_ne w _ hv
  apply Units.ext
  apply Prod.ext
  · rw [val_mul_fst, val_mul_fst, val_mul_fst,
      NumberField.Idele.partAt_fst, NumberField.Idele.partAt_fst,
      list_prod_val_fst_eq_one L _ fun w _ => ideleOf_val_fst w (u w),
      list_prod_val_fst_eq_one L _ fun w _ => shell_val_fst ϖ hπ w (NumberField.Idele.ord K w a),
      list_prod_val_fst_eq_one L _ fun w _ => ideleOf_val_fst w (ecomp ϖ w a * u w)]
    simp
  · apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro w
    rw [val_mul_snd_apply, val_mul_snd_apply, val_mul_snd_apply]
    by_cases hwL : w ∈ L
    · obtain ⟨hwT, hwS⟩ := (hLT w).mp hwL
      have hne : algebraMap (w.adicCompletionIntegers K) (w.adicCompletion K) (ϖ w)
          ^ NumberField.Idele.ord K w a ≠ 0 := zpow_ne_zero _ (hπ w)
      rw [NumberField.Idele.partAt_snd_of_mem K T a hwT, NumberField.Idele.partAt_snd_of_not_mem K S a hwS,
        list_prod_val_snd_of_mem hL _ hsupp_u hwL, list_prod_val_snd_of_mem hL _ hsupp_sh hwL,
        list_prod_val_snd_of_mem hL _ hsupp_e hwL, ideleOf_val_snd_self w (ne_zero_of_mem_unitSet (hu w hwL)),
        shell_val_snd_self, ideleOf_val_snd_self w (ne_zero_of_mem_unitSet
          (mul_mem_unitSet (ecomp_mem_unitSet ϖ (hϖ w hwL) a) (hu w hwL))), one_mul]
      unfold ecomp
      rw [_root_.zpow_neg]
      exact (mul_mul_inv_mul_eq hne _ _).symm
    · rw [list_prod_val_snd_of_not_mem L _ hsupp_u hwL, list_prod_val_snd_of_not_mem L _ hsupp_sh hwL,
        list_prod_val_snd_of_not_mem L _ hsupp_e hwL]
      by_cases hwS : w ∈ S
      · rw [NumberField.Idele.partAt_snd_of_mem K T a (hST hwS), NumberField.Idele.partAt_snd_of_mem K S a hwS]
        simp
      · have hwT : w ∉ T := fun hwT => hwL ((hLT w).mpr ⟨hwT, hwS⟩)
        rw [NumberField.Idele.partAt_snd_of_not_mem K T a hwT, NumberField.Idele.partAt_snd_of_not_mem K S a hwS]
        simp

private theorem diagOne_mul_prod_placeEmbed_unipotent (t : (AdeleRing (𝓞 K) K)ˣ) (L : List (HeightOneSpectrum (𝓞 K)))
    (y : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) :
    (diagOne t : AdelicGL2 (𝓞 K) K) * (L.map fun v => placeEmbed K v (unipotent (y v))).prod
      = (L.map fun v => placeEmbed K v (unipotent (((t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v * y v))).prod
          * diagOne t := by
  induction L with
  | nil => simp
  | cons v L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← mul_assoc, diagOne_mul_placeEmbed_unipotent,
      mul_assoc, ih, mul_assoc]

private theorem apply_prod_placeEmbed_unipotent_mul (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    {L : List (HeightOneSpectrum (𝓞 K))}
    (hN : ∀ v ∈ L, ∀ (y : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (placeEmbed K v (unipotent y) * g) = StandardAddChar.psiLocal K v y * W g)
    (y : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    W ((L.map fun v => placeEmbed K v (unipotent (y v))).prod * g)
      = (L.map fun v => StandardAddChar.psiLocal K v (y v)).prod * W g := by
  induction L with
  | nil => simp
  | cons v L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, mul_assoc, hN v (List.mem_cons_self ..),
      ih fun w hw => hN w (List.mem_cons_of_mem _ hw), mul_assoc]

private theorem coe_apply_ideleOf (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    {c : v.adicCompletion K} (hc : c ≠ 0) :
    ((χ (ideleOf v c) : ℂˣ) : ℂ) = LanglandsTunnell.TateLocal.charExt (localChar χ v) c := by
  rw [ideleOf_of_ne_zero v hc]
  exact (LanglandsTunnell.TateLocal.charExt_coe_units (localChar χ v) (Units.mk0 c hc)).symm

private noncomputable def shellTerm (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ)
    (x : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) (lam om : HeightOneSpectrum (𝓞 K) → ℂ)
    (N : HeightOneSpectrum (𝓞 K) → ℂ) (a : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K))
    (t : v.adicCompletion K) : ℂ :=
  torusFactor (N v) (lam v) (om v) (NumberField.Idele.ord K v a + lev (K := K) v)
    * ((((χ (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))) : ℂˣ) : ℂ)
          * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (1 - s)) ^ NumberField.Idele.ord K v a)
    * (StandardAddChar.psiLocal K v
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ^ NumberField.Idele.ord K v a * x v
            * (ecomp ϖ v a * t))
        * LanglandsTunnell.TateLocal.charExt (localChar χ v) (ecomp ϖ v a * t))

private theorem zetaIntegrand_partAt_mul_prod_ideleOf (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : S ⊆ T)
    {L : List (HeightOneSpectrum (𝓞 K))} (hL : L.Nodup)
    (hLT : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ L ↔ v ∈ T ∧ v ∉ S)
    (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (hϖ : ∀ v ∈ L, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (lam om : HeightOneSpectrum (𝓞 K) → ℂ)
    {I : HeightOneSpectrum (𝓞 K) → Type} [∀ v, Fintype (I v)] [∀ v, Nonempty (I v)]
    (b : ∀ v : HeightOneSpectrum (𝓞 K), I v → v.adicCompletionIntegers K)
    (hN : ∀ v ∈ L, ∀ (y : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (placeEmbed K v (unipotent y) * g) = StandardAddChar.psiLocal K v y * W g)
    (hK : ∀ v ∈ L, ∀ (r : v.adicCompletionIntegers K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (g * placeEmbed K v (unipotent
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r))) = W g)
    (hU : ∀ u : (AdeleRing (𝓞 K) K)ˣ,
      (u : AdeleRing (𝓞 K) K).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 K) K).2 v = 1) →
      finitePartUnits (𝓞 K) K u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K), W (g * diagOne u) = W g)
    (hT : ∀ v ∈ L, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v)
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b v i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v))) =
        lam v * W g)
    (hZ : ∀ v ∈ L, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v))) =
        om v * W g)
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) (x : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)
    (a : (AdeleRing (𝓞 K) K)ˣ) (u : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K)
    (hu : ∀ w ∈ L, u w ∈ unitSet w) :
    zetaIntegrand (fun g => W (g * (L.map fun v => placeEmbed K v (unipotent (x v))).prod)) χ s
        (NumberField.Idele.partAt K T a * (L.map fun w => ideleOf w (u w)).prod)
      = zetaIntegrand (fun g => W (diagOne (dilator ϖ hπ L) * g)) χ s (NumberField.Idele.partAt K S a)
          * (L.map fun v => shellTerm ϖ hπ χ s x lam om (fun v => (Fintype.card (I v) : ℂ)) a v (u v)).prod := by
  rw [partAt_mul_prod_ideleOf_eq ϖ hπ S T hST hL hLT hϖ a u hu]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = NumberField.Idele.partAt K S a := ⟨_, rfl⟩
  obtain ⟨Sh, hSh⟩ : ∃ Sh, Sh = (L.map fun w => shell ϖ hπ w (NumberField.Idele.ord K w a)).prod := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = (L.map fun w => ideleOf w (ecomp ϖ w a * u w)).prod := ⟨_, rfl⟩
  rw [← hQ, ← hSh, ← hE]
  have heu : ∀ w ∈ L, ecomp ϖ w a * u w ∈ unitSet w :=
    fun w hw => mul_mem_unitSet (ecomp_mem_unitSet ϖ (hϖ w hw) a) (hu w hw)

  have hQL : ∀ v ∈ L, ((Q : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 := fun v hv => by
    rw [hQ]
    exact NumberField.Idele.partAt_snd_of_not_mem K S a ((hLT v).mp hv).2
  have hpt : ∀ v ∈ L, ((Q * (Sh * E) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v
      = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ^ NumberField.Idele.ord K v a
          * (ecomp ϖ v a * u v) := fun v hv => by
    rw [val_mul_snd_apply, val_mul_snd_apply, hQL v hv, one_mul, hSh, hE,
      list_prod_val_snd_of_mem hL _ (fun w _ v' hv' => shell_val_snd_of_ne ϖ hπ w _ hv') hv, shell_val_snd_self,
      list_prod_val_snd_of_mem hL _ (fun w _ v' hv' => ideleOf_val_snd_of_ne w _ hv') hv,
      ideleOf_val_snd_self v (ne_zero_of_mem_unitSet (heu v hv))]
  have hE1 : ((E : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := by
    rw [hE]
    exact list_prod_val_fst_eq_one L _ fun w _ => ideleOf_val_fst w _
  have hE2 : ∀ v ∈ S, ((E : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 := fun v hv => by
    rw [hE]
    exact list_prod_val_snd_of_not_mem L _ (fun w _ v' hv' => ideleOf_val_snd_of_ne w _ hv')
      fun hvL => ((hLT v).mp hvL).2 hv
  have hE3 : finitePartUnits (𝓞 K) K E ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K := by
    rw [hE]
    exact finitePartUnits_list_prod_mem L _ fun w hw => finitePartUnits_ideleOf_mem_unitIdeles w (heu w hw)

  have hW : W (diagOne (Q * (Sh * E)) * (L.map fun v => placeEmbed K v (unipotent (x v))).prod)
      = (L.map fun v => StandardAddChar.psiLocal K v
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ^ NumberField.Idele.ord K v a * x v
              * (ecomp ϖ v a * u v))).prod
          * (W (diagOne (dilator ϖ hπ L) * diagOne Q)
              * (L.map fun v => torusFactor (Fintype.card (I v)) (lam v) (om v)
                  (NumberField.Idele.ord K v a + lev (K := K) v)).prod) := by
    rw [diagOne_mul_prod_placeEmbed_unipotent, apply_prod_placeEmbed_unipotent_mul W hN]
    refine congrArg₂ (· * ·) ?_ ?_
    · exact congrArg List.prod (List.map_congr_left fun v hv => by rw [hpt v hv, mul_right_comm])
    · rw [← mul_assoc, map_mul, hU E hE1 hE2 hE3, hSh,
        apply_diagOne_mul_prod_shell ϖ hπ W lam om b hL hϖ hN hK hT hZ hQL]

  have hχ : ((χ (Q * (Sh * E)) : ℂˣ) : ℂ)
      = ((χ Q : ℂˣ) : ℂ)
          * ((L.map fun v => ((χ (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))) : ℂˣ) : ℂ)
                ^ NumberField.Idele.ord K v a).prod
              * (L.map fun v => LanglandsTunnell.TateLocal.charExt (localChar χ v) (ecomp ϖ v a * u v)).prod) := by
    have hkey : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ((χ z : ℂˣ) : ℂ) = ((Units.coeHom ℂ).comp χ) z := fun _ => rfl
    rw [hkey, map_mul, map_mul, hSh, hE, map_list_prod, map_list_prod, List.map_map, List.map_map, ← hkey]
    refine congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) ?_ ?_)
    · exact congrArg List.prod
        (List.map_congr_left fun v _ => map_zpow ((Units.coeHom ℂ).comp χ) (finIdele v (piUnit ϖ hπ v)) _)
    · exact congrArg List.prod
        (List.map_congr_left fun v hv => coe_apply_ideleOf χ v (ne_zero_of_mem_unitSet (heu v hv)))

  have hnorm : ((ideleNorm K (Q * (Sh * E)) : ℝ) : ℂ) ^ (s - 1)
      = ((ideleNorm K Q : ℝ) : ℂ) ^ (s - 1)
          * (L.map fun v => (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (1 - s)) ^ NumberField.Idele.ord K v a).prod := by
    have hEn : (L.map fun w => ideleNormHom (ideleOf w (ecomp ϖ w a * u w))).prod = (1 : ℝ) :=
      List.prod_eq_one fun y hy => by
        rw [List.mem_map] at hy
        obtain ⟨w, hw, rfl⟩ := hy
        exact ideleNorm_ideleOf w (heu w hw)
    have hShn : (L.map fun w => ideleNormHom (shell ϖ hπ w (NumberField.Idele.ord K w a)))
        = L.map fun w => ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)⁻¹ ^ NumberField.Idele.ord K w a :=
      List.map_congr_left fun w hw => by
        rw [shell, map_zpow, ideleNormHom_apply, ideleNorm_finIdele_piUnit ϖ hπ (hϖ w hw)]
    have hpos : ∀ w ∈ L, (0 : ℝ) ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)⁻¹ ^ NumberField.Idele.ord K w a :=
      fun w hw => zpow_nonneg (inv_nonneg.mpr (absNorm_pos_of_piUnit ϖ hπ (hϖ w hw)).le) _
    rw [← ideleNormHom_apply, map_mul, map_mul, hSh, hE, map_list_prod, map_list_prod, List.map_map, List.map_map]
    simp only [Function.comp_def]
    rw [hEn, mul_one, hShn, ideleNormHom_apply, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (ideleNorm_pos Q).le (List.prod_nonneg fun y hy => by
        rw [List.mem_map] at hy
        obtain ⟨w, hw, rfl⟩ := hy
        exact hpos w hw),
      ofReal_list_prod_cpow L _ hpos]
    refine congrArg₂ (· * ·) rfl ?_
    exact congrArg List.prod (List.map_congr_left fun w hw =>
      ofReal_inv_zpow_cpow (absNorm_pos_of_piUnit ϖ hπ (hϖ w hw)) _ s)

  simp only [zetaIntegrand]
  rw [hW, hχ, hnorm]
  simp only [shellTerm, mul_zpow, List.prod_map_mul]
  ring

end Factorisation

omit [NumberField K] in
private theorem coe_union_setOf_mem_eq (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : S ⊆ T)
    (L : List (HeightOneSpectrum (𝓞 K))) (hLT : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ L ↔ v ∈ T ∧ v ∉ S) :
    ((↑S : Set (HeightOneSpectrum (𝓞 K))) ∪ {v | v ∈ L}) = (↑T : Set (HeightOneSpectrum (𝓞 K))) := by
  ext w
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, hLT]
  constructor
  · rintro (hw | ⟨hw, -⟩)
    · exact hST hw
    · exact hw
  · intro hw
    by_cases hwS : w ∈ S
    · exact Or.inl hwS
    · exact Or.inr ⟨hw, hwS⟩

end Furniture

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel in

private theorem avgList_zetaIntegrand_partAt_eq
    (K : Type) [Field K] [NumberField K]
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : S ⊆ T)
    (L : List (HeightOneSpectrum (𝓞 K))) (hL : L.Nodup) (hLT : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ L ↔ v ∈ T ∧ v ∉ S)
    (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 K),
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ≠ 0)
    (hϖ : ∀ v ∈ L, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (lam om : HeightOneSpectrum (𝓞 K) → ℂ)
    {I : HeightOneSpectrum (𝓞 K) → Type} [hIf : ∀ v, Fintype (I v)] [hIn : ∀ v, Nonempty (I v)]
    (b : ∀ v : HeightOneSpectrum (𝓞 K), I v → v.adicCompletionIntegers K)
    (hN : ∀ v ∈ L, ∀ (y : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (placeEmbed K v (unipotent y) * g) = StandardAddChar.psiLocal K v y * W g)
    (hK : ∀ v ∈ L, ∀ (r : v.adicCompletionIntegers K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (g * placeEmbed K v (unipotent
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r))) = W g)
    (hU : ∀ u : (AdeleRing (𝓞 K) K)ˣ,
      (u : AdeleRing (𝓞 K) K).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 K) K).2 v = 1) →
      finitePartUnits (𝓞 K) K u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K), W (g * diagOne u) = W g)
    (hT : ∀ v ∈ L, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v)
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b v i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v))) =
        lam v * W g)
    (hZ : ∀ v ∈ L, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v))) =
        om v * W g)
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ)
    (x : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)
    [hM : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [hB : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
    [hμ : ∀ v : HeightOneSpectrum (𝓞 K), (μ v).IsAddHaarMeasure]
    (a : (AdeleRing (𝓞 K) K)ˣ)
    (_ha : a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑T : Set (HeightOneSpectrum (𝓞 K)))) :
    avgList μ L
        (zetaIntegrand (fun g => W (g * (L.map fun v => placeEmbed K v (unipotent (x v))).prod)) χ s)
        (NumberField.Idele.partAt K T a)
      = (zetaIntegrand
        (fun g => W (diagOne ((L.map fun v =>
            Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))
              ^ (-(LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v)))).prod) * g)) χ s)
          ((NumberField.Idele.productMeasureData K S).projS a)
        * (L.map fun v =>
            (fun (v : HeightOneSpectrum (𝓞 K)) (m : ℤ) =>
      torusFactor (Fintype.card (I v)) (lam v) (om v)
                  (m + LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v))
                * ((((χ (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))) : ℂˣ) : ℂ)
                      * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (1 - s)) ^ m)
                * ((∫ u in {u : v.adicCompletion K | Valued.v u = 1},
                        StandardAddChar.psiLocal K v
                            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ^ m * x v * u)
                          * LanglandsTunnell.TateLocal.charExt (localChar χ v) u ∂(μ v))
                      / (((μ v).real {u : v.adicCompletion K | Valued.v u = 1} : ℝ) : ℂ)))
              v ((NumberField.Idele.productMeasureData K S).ord v a)).prod := by
  dsimp only [NumberField.Idele.productMeasureData]
  rw [avgList_eq_of_forall μ (shellTerm ϖ hπ χ s x lam om (fun v => (Fintype.card (I v) : ℂ)) a) L hL
    (zetaIntegrand (fun g => W (g * (L.map fun v => placeEmbed K v (unipotent (x v))).prod)) χ s)
    (NumberField.Idele.partAt K T a)
    (zetaIntegrand (fun g => W (diagOne (dilator ϖ hπ L) * g)) χ s (NumberField.Idele.partAt K S a))
    fun u hu => zetaIntegrand_partAt_mul_prod_ideleOf ϖ hπ S T hST hL hLT W hϖ lam om b hN hK hU hT hZ χ s x a u hu]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact rfl
  refine congrArg List.prod (List.map_congr_left fun v hv => ?_)
  have he : ecomp ϖ v a ∈ unitSet v := ecomp_mem_unitSet ϖ (hϖ v hv) a
  simp only [shellTerm]
  rw [integral_const_mul, setIntegral_unitSet_mul_left (μ v) he fun t => StandardAddChar.psiLocal K v
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ^ NumberField.Idele.ord K v a * x v * t)
      * LanglandsTunnell.TateLocal.charExt (localChar χ v) t, mul_div_assoc]
  exact rfl

end UnramifiedWhittaker.PartMeasureFactorisation

open _root_.UnramifiedWhittaker _root_.P2MW.S_UnramifiedWhittaker_integral_zetaIntegrand_unipotent_partMeasure_eq_mul_prod_tsum_torusFactor_mul_setIntegral.UnramifiedWhittaker UnramifiedWhittaker.PartMeasureFactorisation in
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : S ⊆ T)
    (L : List (HeightOneSpectrum (𝓞 K))) (hL : L.Nodup) (hLT : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ L ↔ v ∈ T ∧ v ∉ S)
    (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 K),
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ≠ 0)
    (hϖ : ∀ v ∈ L, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (lam om : HeightOneSpectrum (𝓞 K) → ℂ)
    {I : HeightOneSpectrum (𝓞 K) → Type} [hIf : ∀ v, Fintype (I v)] [hIn : ∀ v, Nonempty (I v)]
    (b : ∀ v : HeightOneSpectrum (𝓞 K), I v → v.adicCompletionIntegers K)
    (hN : ∀ v ∈ L, ∀ (y : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (placeEmbed K v (unipotent y) * g) = StandardAddChar.psiLocal K v y * W g)
    (hK : ∀ v ∈ L, ∀ (r : v.adicCompletionIntegers K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (g * placeEmbed K v (unipotent
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r))) = W g)
    (hU : ∀ u : (AdeleRing (𝓞 K) K)ˣ,
      (u : AdeleRing (𝓞 K) K).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 K) K).2 v = 1) →
      finitePartUnits (𝓞 K) K u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K), W (g * diagOne u) = W g)
    (hT : ∀ v ∈ L, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v)
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b v i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v))) =
        lam v * W g)
    (hZ : ∀ v ∈ L, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v))) =
        om v * W g)
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ)
    (x : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)
    [hM : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [hB : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
    [hμ : ∀ v : HeightOneSpectrum (𝓞 K), (μ v).IsAddHaarMeasure]
    (hTint : Integrable
      (zetaIntegrand (fun g => W (g * (L.map fun v => placeEmbed K v (unipotent (x v))).prod)) χ s)
      (NumberField.Idele.productMeasureData K T).νS)
    (hSint : Integrable
      (zetaIntegrand
        (fun g => W (diagOne ((L.map fun v =>
            Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))
              ^ (-(LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v)))).prod) * g)) χ s)
      (NumberField.Idele.productMeasureData K S).νS)
    (hsum : ∀ v ∈ L, Summable fun m : ℤ =>
      ‖torusFactor (Fintype.card (I v)) (lam v) (om v)
          (m + LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v))
        * ((((χ (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (1 - s)) ^ m)
        * ((∫ u in {u : v.adicCompletion K | Valued.v u = 1},
                StandardAddChar.psiLocal K v
                    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ^ m * x v * u)
                  * LanglandsTunnell.TateLocal.charExt (localChar χ v) u ∂(μ v))
              / (((μ v).real {u : v.adicCompletion K | Valued.v u = 1} : ℝ) : ℂ))‖) :
    (∫ a, zetaIntegrand (fun g => W (g * (L.map fun v => placeEmbed K v (unipotent (x v))).prod)) χ s a
        ∂(NumberField.Idele.productMeasureData K T).νS)
      = (∫ a,
          zetaIntegrand
            (fun g => W (diagOne ((L.map fun v =>
                Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))
                  ^ (-(LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v)))).prod) * g)) χ s a
            ∂(NumberField.Idele.productMeasureData K S).νS)
        * (L.map fun v => ∑' m : ℤ,
            torusFactor (Fintype.card (I v)) (lam v) (om v)
                (m + LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v))
              * ((((χ (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (1 - s)) ^ m)
              * ((∫ u in {u : v.adicCompletion K | Valued.v u = 1},
                      StandardAddChar.psiLocal K v
                          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ^ m * x v * u)
                        * LanglandsTunnell.TateLocal.charExt (localChar χ v) u ∂(μ v))
                    / (((μ v).real {u : v.adicCompletion K | Valued.v u = 1} : ℝ) : ℂ))).prod := by
  have hLS : ∀ v ∈ L, v ∉ S := fun v hv => ((hLT v).1 hv).2
  have hLT' : ∀ v ∈ L, v ∈ T := fun v hv => ((hLT v).1 hv).1
  have hset := coe_union_setOf_mem_eq S T hST L hLT
  obtain ⟨hint, havg⟩ := integrable_avgList_and_integral_avgList T μ L hLT' hTint
  rw [← havg, integral_eq_setIntegral_partAt T hint.aestronglyMeasurable]
  have htonelli := (NumberField.Idele.productMeasureData K S).tonelli L hLS hL
    (zetaIntegrand
        (fun g => W (diagOne ((L.map fun v =>
            Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))
              ^ (-(LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v)))).prod) * g)) χ s)
    (fun (v : HeightOneSpectrum (𝓞 K)) (m : ℤ) =>
      torusFactor (Fintype.card (I v)) (lam v) (om v)
                  (m + LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v))
                * ((((χ (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 _ (hπ v)))) : ℂˣ) : ℂ)
                      * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (1 - s)) ^ m)
                * ((∫ u in {u : v.adicCompletion K | Valued.v u = 1},
                        StandardAddChar.psiLocal K v
                            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ^ m * x v * u)
                          * LanglandsTunnell.TateLocal.charExt (localChar χ v) u ∂(μ v))
                      / (((μ v).real {u : v.adicCompletion K | Valued.v u = 1} : ℝ) : ℂ)))
    hSint (fun v hv => hsum v hv)
  have h2 := htonelli.2
  rw [show (NumberField.Idele.productMeasureData K S).c = (1 : ℝ) from rfl, Complex.ofReal_one, one_mul, hset] at h2
  refine (setIntegral_congr_fun (NumberField.Idele.isOpen_unitIdelesOutside K _).measurableSet
    fun a ha =>
      avgList_zetaIntegrand_partAt_eq K S T hST L hL hLT W ϖ hπ hϖ lam om b hN hK hU hT hZ χ s x μ a ha).trans ?_
  exact h2

end

end S_UnramifiedWhittaker_integral_zetaIntegrand_unipotent_partMeasure_eq_mul_prod_tsum_torusFactor_mul_setIntegral
end P2MW
export P2MW.S_UnramifiedWhittaker_integral_zetaIntegrand_unipotent_partMeasure_eq_mul_prod_tsum_torusFactor_mul_setIntegral (solution)
