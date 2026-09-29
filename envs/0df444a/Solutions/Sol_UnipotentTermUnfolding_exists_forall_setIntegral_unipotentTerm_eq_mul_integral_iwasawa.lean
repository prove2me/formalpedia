-- Prove2me | solution 1 for UnipotentTermUnfolding.exists_forall_setIntegral_unipotentTerm_eq_mul_integral_iwasawa
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/cb359c47-5707-5262-a08a-3037ef19e4a3

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_AutomorphicForm_ideleNorm_det_sigmaAdelicAct
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero
import Theorems.Thm_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap
import Theorems.Thm_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa
import Theorems.Thm_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UnipotentTermUnfolding_exists_forall_setIntegral_unipotentTerm_eq_mul_integral_iwasawa
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_UnipotentTermUnfolding_exists_forall_setIntegral_unipotentTerm_eq_mul_integral_iwasawa.AutomorphicForm"
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

section BlockISections
section KernelSplitting

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.adeleBorel

namespace KernelSplitting

section Kernel

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (S : Finset (HeightOneSpectrum (𝓞 K))) {φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ}
  {φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} {φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
  {φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}

private theorem isFactorizableTestFn_of_isSemiLocalFactorization
    (h : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS) :
    AutomorphicForm.IsFactorizableTestFn L φ :=
  ⟨φa, φf, h.1, h.2.1, h.2.2.2.2.2⟩

private theorem continuous_and_hasCompactSupport_of_isSemiLocalFactorization
    (h : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS) :
    Continuous φ ∧ HasCompactSupport φ :=
  AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ
    (isFactorizableTestFn_of_isSemiLocalFactorization K L S h)

end Kernel

end KernelSplitting

end KernelSplitting

section CellScalar

set_option autoImplicit false

namespace CellScalarStability

section Charpoly

open Polynomial

variable {R : Type*} [Field R]

private theorem charpoly_smul_fin_two {a : R} (ha : a ≠ 0) (M : Matrix (Fin 2) (Fin 2) R) :
    (a • M).charpoly = C (a ^ 2) * M.charpoly.comp (C a⁻¹ * X) := by
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two, Matrix.trace_smul, Matrix.det_smul,
    Fintype.card_fin, smul_eq_mul]
  simp only [add_comp, sub_comp, pow_comp, mul_comp, X_comp, C_comp]
  have hinv : C a * C a⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ ha, C_1]
  rw [C_mul, C_mul, C_pow]
  linear_combination (-(C a * C a⁻¹ + 1) * X ^ 2 + C a * C M.trace * X) * hinv

private theorem sq_X_sub_C_mul_eq {a : R} (ha : a ≠ 0) (c : R) :
    (X - C (a * c)) ^ 2 = C (a ^ 2) * (C a⁻¹ * X - C c) ^ 2 := by
  have h : X - C (a * c) = C a * (C a⁻¹ * X - C c) := by
    rw [mul_sub, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul, ← C_mul]
  rw [h, mul_pow, C_pow]

private theorem X_sub_C_mul_mul_eq {a : R} (ha : a ≠ 0) (b c : R) :
    (X - C (a * b)) * (X - C (a * c)) = C (a ^ 2) * ((C a⁻¹ * X - C b) * (C a⁻¹ * X - C c)) := by
  have h : ∀ d : R, X - C (a * d) = C a * (C a⁻¹ * X - C d) := fun d => by
    rw [mul_sub, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul, ← C_mul]
  rw [h b, h c, C_pow]
  ring

private theorem not_isCentralType_smul {a : R} (ha : a ≠ 0) {M : Matrix (Fin 2) (Fin 2) R}
    (hM : ¬AutomorphicForm.IsCentralType M) : ¬AutomorphicForm.IsCentralType (a • M) := by
  rintro ⟨d, hd⟩
  exact hM ⟨a⁻¹ * d, by rw [← smul_smul, ← hd, smul_smul, inv_mul_cancel₀ ha, one_smul]⟩

private theorem isUnipotentType_smul {a : R} (ha : a ≠ 0) {M : Matrix (Fin 2) (Fin 2) R}
    (hM : AutomorphicForm.IsUnipotentType M) : AutomorphicForm.IsUnipotentType (a • M) := by
  obtain ⟨hnc, c, hc⟩ := hM
  refine ⟨not_isCentralType_smul ha hnc, a * c, ?_⟩
  rw [charpoly_smul_fin_two ha, hc, sq_X_sub_C_mul_eq ha]
  simp only [pow_comp, sub_comp, X_comp, C_comp]

private theorem isHyperbolicType_smul {a : R} (ha : a ≠ 0) {M : Matrix (Fin 2) (Fin 2) R}
    (hM : AutomorphicForm.IsHyperbolicType M) : AutomorphicForm.IsHyperbolicType (a • M) := by
  obtain ⟨b, c, hbc, hM⟩ := hM
  refine ⟨a * b, a * c, fun h => hbc (mul_left_cancel₀ ha h), ?_⟩
  rw [charpoly_smul_fin_two ha, hM, X_sub_C_mul_mul_eq ha]
  simp only [mul_comp, sub_comp, X_comp, C_comp]

end Charpoly

section Cells

variable {R : Type*} [Field R]

private theorem coe_scalar (s : Rˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) s : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
      = Matrix.scalar (Fin 2) (s : R) := rfl

private theorem coe_mul_scalar (γ : GL (Fin 2) R) (s : Rˣ) :
    ((γ * Matrix.GeneralLinearGroup.scalar (Fin 2) s : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
      = (s : R) • (γ : Matrix (Fin 2) (Fin 2) R) := by
  rw [Units.val_mul, coe_scalar, Matrix.scalar_apply]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem isCentralType_smul (a : R) {M : Matrix (Fin 2) (Fin 2) R}
    (hM : AutomorphicForm.IsCentralType M) : AutomorphicForm.IsCentralType (a • M) := by
  obtain ⟨c, hc⟩ := hM
  exact ⟨a * c, by rw [hc, smul_smul]⟩

private theorem isEllipticType_smul {a : R} (ha : a ≠ 0) {M : Matrix (Fin 2) (Fin 2) R}
    (hM : AutomorphicForm.IsEllipticType M) : AutomorphicForm.IsEllipticType (a • M) := by
  intro b hb
  apply hM (b / a)
  rw [Matrix.charpoly_fin_two] at hb ⊢
  simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Matrix.trace_smul, Matrix.det_smul,
    Fintype.card_fin, smul_eq_mul] at hb ⊢
  have key : (b / a) ^ 2 - M.trace * (b / a) + M.det
      = (b ^ 2 - a * M.trace * b + a ^ 2 * M.det) / a ^ 2 := by
    field_simp
  rw [key, hb, zero_div]

private theorem mul_scalar_mem_centralCell {γ : GL (Fin 2) R} (hγ : γ ∈ AutomorphicForm.centralCell R)
    (s : Rˣ) : γ * Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ AutomorphicForm.centralCell R := by
  show AutomorphicForm.IsCentralType _
  rw [coe_mul_scalar]
  exact isCentralType_smul _ hγ

private theorem mul_scalar_mem_ellipticCell {γ : GL (Fin 2) R} (hγ : γ ∈ AutomorphicForm.ellipticCell R)
    (s : Rˣ) : γ * Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ AutomorphicForm.ellipticCell R := by
  show AutomorphicForm.IsEllipticType _
  rw [coe_mul_scalar]
  exact isEllipticType_smul s.ne_zero hγ

private theorem mul_scalar_mem_unipotentCell {γ : GL (Fin 2) R} (hγ : γ ∈ AutomorphicForm.unipotentCell R)
    (s : Rˣ) : γ * Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ AutomorphicForm.unipotentCell R := by
  show AutomorphicForm.IsUnipotentType _
  rw [coe_mul_scalar]
  exact isUnipotentType_smul s.ne_zero hγ

private theorem mul_scalar_mem_hyperbolicCell {γ : GL (Fin 2) R} (hγ : γ ∈ AutomorphicForm.hyperbolicCell R)
    (s : Rˣ) : γ * Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ AutomorphicForm.hyperbolicCell R := by
  show AutomorphicForm.IsHyperbolicType _
  rw [coe_mul_scalar]
  exact isHyperbolicType_smul s.ne_zero hγ

end Cells

section Scalars

private theorem _root_.CellScalarStability.map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (s : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) s)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) s) := by
  apply Units.ext
  ext i j
  show f ((Matrix.scalar (Fin 2) (s : R)) i j) = (Matrix.scalar (Fin 2) (f (s : R))) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

p2m_export "CellScalarStability" "map_scalar"
private theorem _root_.CellScalarStability.scalar_commute {R : Type*} [CommRing R] (s : Rˣ) (g : GL (Fin 2) R) :
    Commute (Matrix.GeneralLinearGroup.scalar (Fin 2) s) g := by
  show Matrix.GeneralLinearGroup.scalar (Fin 2) s * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) s
  exact Units.ext
    (Matrix.scalar_commute (s : R) (fun r => Commute.all _ r) (g : Matrix (Fin 2) (Fin 2) R)).eq

p2m_export "CellScalarStability" "scalar_commute"
private theorem sigmaPartialNorm_mul_of_commute {G : Type*} [Group G] (σ : G →* G) {s : G}
    (hs : ∀ g : G, Commute s g) (x : G) (r : ℕ) :
    LT.TwistedNorm.sigmaPartialNorm σ (x * s) r
      = LT.TwistedNorm.sigmaPartialNorm σ x r * LT.TwistedNorm.sigmaPartialNorm σ s r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [LT.TwistedNorm.sigmaPartialNorm_succ', LT.TwistedNorm.sigmaPartialNorm_succ',
        LT.TwistedNorm.sigmaPartialNorm_succ', ih, map_mul]
      have hc := (hs (σ (LT.TwistedNorm.sigmaPartialNorm σ x r))).eq
      simp only [mul_assoc]
      rw [← mul_assoc s, hc, mul_assoc]

private theorem sigmaNormPow_mul_of_commute {G : Type*} [Group G] (σ : G →* G) {s : G}
    (hs : ∀ g : G, Commute s g) (ℓ : ℕ) (x : G) :
    LT.TwistedNorm.sigmaNormPow σ ℓ (x * s)
      = LT.TwistedNorm.sigmaNormPow σ ℓ x * LT.TwistedNorm.sigmaNormPow σ ℓ s :=
  sigmaPartialNorm_mul_of_commute σ hs x ℓ

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

private theorem sigmaNormPow_scalar (σ : L ≃ₐ[F] L) (ℓ : ℕ) (a : Lˣ) :
    LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) ℓ
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a)
      = Matrix.GeneralLinearGroup.scalar (Fin 2)
          (LT.TwistedNorm.sigmaNormPow (Units.map ((σ : L →+* L) : L →* L)) ℓ a) :=
  (LT.TwistedNorm.hom_sigmaNormPow (Units.map ((σ : L →+* L) : L →* L))
    (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Matrix.GeneralLinearGroup.scalar (Fin 2))
    (fun b => (map_scalar (σ : L →+* L) b).symm) ℓ a).symm

variable [FiniteDimensional F L] [IsGalois F L]

private theorem sigmaNormPow_mul_scalar {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) (a : Lˣ) :
    LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L)
        (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a)
      = LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L))
          (Module.finrank F L) δ *
        Matrix.GeneralLinearGroup.map (algebraMap F L)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (Algebra.norm F : L →* F) a)) := by
  rw [sigmaNormPow_mul_of_commute _ (scalar_commute a), sigmaNormPow_scalar, map_scalar]
  congr 2
  apply Units.ext
  rw [LT.TwistedNorm.coe_sigmaNormPow_units_eq_algebraMap_norm hgen]
  simp only [Units.coe_map, MonoidHom.coe_coe]

private theorem isNormRep_mul_scalar {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {γ : GL (Fin 2) F} {δ : GL (Fin 2) L} (h : LT.TwistedNorm.IsNormRep σ γ δ) (a : Lˣ) :
    LT.TwistedNorm.IsNormRep σ
      (γ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (Algebra.norm F : L →* F) a))
      (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, ?_⟩
  rw [sigmaNormPow_mul_scalar hgen, map_mul, ← hP, map_scalar]
  have hc := (scalar_commute (Units.map ((algebraMap F L : F →+* L) : F →* L)
    (Units.map (Algebra.norm F : L →* F) a)) P).eq
  simp only [mul_assoc]
  rw [hc]

private theorem normClassMap_mk_mul_scalar {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (h : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ)
    (a : Lˣ) :
    LT.TwistedNorm.normClassMap hgen
        (LT.TwistedNorm.SigmaConjClasses.mk σ (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a))
      = ConjClasses.mk
          (γ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (Algebra.norm F : L →* F) a)) := by
  rw [LT.TwistedNorm.normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at h
  obtain ⟨Q, hQ⟩ := h
  obtain ⟨P, hP⟩ := LT.TwistedNorm.isNormRep_normRep hgen δ
  have hγ : LT.TwistedNorm.IsNormRep σ γ δ :=
    ⟨P * Matrix.GeneralLinearGroup.map (algebraMap F L) Q⁻¹, by
      rw [← hQ, map_mul, map_mul, map_inv, ← hP]
      group⟩
  exact LT.TwistedNorm.normClassMap_mk_eq_of_isNormRep hgen (isNormRep_mul_scalar hgen hγ a)

private theorem mul_scalar_mem_centralElliptic {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L}
    (hδ : δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) F,
      (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ})
    (a : Lˣ) :
    δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) F,
      (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} := by
  obtain ⟨γ, hγ, hclass⟩ := hδ
  refine ⟨γ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (Algebra.norm F : L →* F) a), ?_,
    normClassMap_mk_mul_scalar hgen hclass a⟩
  rcases hγ with hγ | hγ
  · exact Or.inl (mul_scalar_mem_ellipticCell hγ _)
  · exact Or.inr (mul_scalar_mem_centralCell hγ _)

end Scalars

section IndexSets

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

private theorem mul_scalar_mem_setOf_unipotent {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L}
    (hδ : δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) F, γ ∈ AutomorphicForm.unipotentCell F ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ})
    (a : Lˣ) :
    δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) F,
      γ ∈ AutomorphicForm.unipotentCell F ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} := by
  obtain ⟨γ, hγ, hclass⟩ := hδ
  exact ⟨_, mul_scalar_mem_unipotentCell hγ _, normClassMap_mk_mul_scalar hgen hclass a⟩

private theorem mul_scalar_mem_setOf_hyperbolic {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L}
    (hδ : δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) F, γ ∈ AutomorphicForm.hyperbolicCell F ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ})
    (a : Lˣ) :
    δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) F,
      γ ∈ AutomorphicForm.hyperbolicCell F ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} := by
  obtain ⟨γ, hγ, hclass⟩ := hδ
  exact ⟨_, mul_scalar_mem_hyperbolicCell hγ _, normClassMap_mk_mul_scalar hgen hclass a⟩

end IndexSets

end CellScalarStability

end CellScalar

section KernelShell

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct Pointwise

namespace KernelShell

section Scalars

private theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (s : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) s)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) s) := by
  apply Units.ext
  ext i j
  show f ((Matrix.scalar (Fin 2) (s : R)) i j) = (Matrix.scalar (Fin 2) (f (s : R))) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

end Scalars

section Reindex

variable {L : Type*} [Field L]

private theorem finsum_mem_mul_scalar_eq {M : Type*} [AddCommMonoid M] (T : Set (GL (Fin 2) L))
    (hT : ∀ δ ∈ T, ∀ a : Lˣ, δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ T)
    (G : GL (Fin 2) L → M) (a : Lˣ) :
    ∑ᶠ δ ∈ T, G (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a) = ∑ᶠ δ ∈ T, G δ := by
  refine finsum_mem_eq_of_bijOn (fun δ => δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a)
    ⟨fun δ hδ => hT δ hδ a, ?_, ?_⟩ fun δ _ => rfl
  · intro δ₁ _ δ₂ _ h
    exact mul_right_cancel h
  · intro δ hδ
    refine ⟨δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹, hT δ hδ a⁻¹, ?_⟩
    show δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a = δ
    rw [map_inv, inv_mul_cancel_right]

end Reindex

section Kernel

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

private theorem centralScalar_map_algebraMap (ζ : Lˣ) :
    AutomorphicForm.centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* _) ζ)
      = AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ) := by
  show Matrix.GeneralLinearGroup.scalar (Fin 2) _
    = Matrix.GeneralLinearGroup.map (algebraMap L (AdeleRing (𝓞 L) L))
        (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ)
  rw [map_scalar]

private theorem ideleNorm_one' : NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) = 1 := by
  have h : NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) *
      NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ)
        = NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) := by
    rw [← NumberField.TateGlobal.ideleNorm_mul, mul_one]
  exact mul_left_cancel₀ (NumberField.TateGlobal.ideleNorm_pos (1 : (AdeleRing (𝓞 L) L)ˣ)).ne'
    (h.trans (mul_one _).symm)

private theorem ideleNorm_inv' (u : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L u⁻¹ = (NumberField.TateGlobal.ideleNorm L u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← NumberField.TateGlobal.ideleNorm_mul, inv_mul_cancel, ideleNorm_one']

private theorem ideleNorm_sq_mem_of_ne_zero (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (z : (AdeleRing (𝓞 L) L)ˣ) (δ : GL (Fin 2) L)
    (hne : φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ≠ 0) :
    NumberField.TateGlobal.ideleNorm L z * NumberField.TateGlobal.ideleNorm L z ∈
      (fun g : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) '' Function.support φ := by
  refine ⟨_, hne, ?_⟩
  have hx : NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det x) ≠ 0 :=
    (NumberField.TateGlobal.ideleNorm_pos _).ne'
  have hdet : Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 L) L z) = z * z := by
    apply Units.ext
    show Matrix.det (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L)) = (z : AdeleRing (𝓞 L) L) * z
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]
  dsimp only
  rw [map_mul, map_mul, map_inv, NumberField.TateGlobal.ideleNorm_mul,
    NumberField.TateGlobal.ideleNorm_mul, ideleNorm_inv', AutomorphicForm.ideleNorm_det_globalPoints,
    AutomorphicForm.ideleNorm_det_sigmaAdelicAct K L D σ, map_mul,
    NumberField.TateGlobal.ideleNorm_mul, hdet, NumberField.TateGlobal.ideleNorm_mul]
  field_simp

private theorem finsum_mem_centralScalar_map_mul (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (T : Set (GL (Fin 2) L))
    (hT : ∀ δ ∈ T, ∀ a : Lˣ, δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ T)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (ζ : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L
          (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* _) ζ * z) * x))
      = ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) := by
  have hσ : AutomorphicForm.sigmaAdelicAct K L D σ
        (AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ))
      = AutomorphicForm.globalPoints (𝓞 L) L
          (Matrix.GeneralLinearGroup.map (σ : L →+* L) (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ)) :=
    AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ _
  refine Eq.trans ?_ (finsum_mem_mul_scalar_eq T hT
    (fun δ => φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)))
    (Units.map ((σ : L →+* L) : L →* L) ζ))
  refine finsum_mem_congr rfl fun δ _ => ?_
  beta_reduce
  simp only [map_mul, centralScalar_map_algebraMap, hσ, map_scalar, mul_assoc]

end Kernel

end KernelShell

end KernelShell

section FoldBounds

set_option autoImplicit false

open MeasureTheory NumberField Topology
open IsDedekindDomain
open scoped TensorProduct Pointwise NNReal

namespace KernelFoldBounds

section Generic

variable (L : Type) [Field L] [NumberField L]

private theorem exists_finite_forall_ne_zero_mem (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ)
    {X Y : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)} (hX : IsCompact X) (hY : IsCompact Y) :
    ∃ Γ : Set (GL (Fin 2) L), Γ.Finite ∧ ∀ x ∈ X, ∀ y ∈ Y, ∀ δ : GL (Fin 2) L,
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * y) ≠ 0 → δ ∈ Γ := by
  have hC : IsCompact (X * tsupport φ * Y⁻¹) := (hX.mul hφs).mul hY.inv
  refine ⟨{δ | (1 : AutomorphicForm.AdelicGL2 (𝓞 L) L)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * 1 ∈
    X * tsupport φ * Y⁻¹}, hfin _ hC 1 1, ?_⟩
  intro x hx y hy δ hδ
  have hmem : x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * y ∈ tsupport φ := subset_tsupport φ hδ
  have h : AutomorphicForm.globalPoints (𝓞 L) L δ
      = x * (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * y) * y⁻¹ := by group
  change (1 : AutomorphicForm.AdelicGL2 (𝓞 L) L)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * 1 ∈
    X * tsupport φ * Y⁻¹
  rw [inv_one, one_mul, mul_one, h]
  exact Set.mul_mem_mul (Set.mul_mem_mul hx hmem) (Set.inv_mem_inv.mpr hy)

private theorem finsum_mem_eq_sum_of_mem (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ) (T : Set (GL (Fin 2) L))
    {X Y : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)} (hX : IsCompact X) (hY : IsCompact Y) :
    ∃ t : Finset (GL (Fin 2) L), (t : Set (GL (Fin 2) L)) ⊆ T ∧ ∀ x ∈ X, ∀ y ∈ Y,
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * y)
        = ∑ δ ∈ t, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * y) := by
  obtain ⟨Γ, hΓ, hmem⟩ := exists_finite_forall_ne_zero_mem L hfin φ hφs hX hY
  have hΓT : (Γ ∩ T).Finite := hΓ.subset Set.inter_subset_left
  refine ⟨hΓT.toFinset, fun δ hδ => (hΓT.mem_toFinset.mp hδ).2, fun x hx y hy => ?_⟩
  apply finsum_mem_eq_sum_of_subset
  · rintro δ ⟨hδT, hδs⟩
    exact hΓT.mem_toFinset.mpr ⟨hmem x hx y hy δ hδs, hδT⟩
  · intro δ hδ
    exact (hΓT.mem_toFinset.mp hδ).2

private theorem continuous_finsum_mem (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (T : Set (GL (Fin 2) L)) :
    Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      ∑ᶠ δ ∈ T, φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨X, hX, hXn⟩ := exists_compact_mem_nhds p.1
  obtain ⟨Y, hY, hYn⟩ := exists_compact_mem_nhds p.2
  obtain ⟨t, -, ht⟩ := finsum_mem_eq_sum_of_mem L hfin φ hφs T hX hY
  have hsum : Continuous fun q : AutomorphicForm.AdelicGL2 (𝓞 L) L × AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      ∑ δ ∈ t, φ (q.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * q.2) := by
    refine continuous_finsetSum t fun δ _ => hφc.comp ?_
    exact (continuous_fst.inv.mul continuous_const).mul continuous_snd
  refine ((hsum.continuousOn (s := X ×ˢ Y)).congr fun q hq => ht q.1 hq.1 q.2 hq.2).continuousAt ?_
  exact prod_mem_nhds hXn hYn

private theorem exists_forall_norm_finsum_mem_le (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (T : Set (GL (Fin 2) L)) {X Y : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)} (hX : IsCompact X)
    (hY : IsCompact Y) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ X, ∀ y ∈ Y,
      ‖∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * y)‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hX.prod hY).exists_bound_of_continuousOn
    (continuous_finsum_mem L hfin φ hφc hφs T).continuousOn
  exact ⟨max M 0, le_max_right _ _, fun x hx y hy => (hM (x, y) ⟨hx, hy⟩).trans (le_max_left _ _)⟩

end Generic

section Fold

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

private theorem continuous_glMap'' {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B)
    (hf : Continuous f) : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map f)

private theorem continuous_sigmaAdelicAct'' : Continuous (AutomorphicForm.sigmaAdelicAct K L D σ) :=
  continuous_glMap'' (D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom (D.continuous_act σ)

private theorem continuous_centralScalar : Continuous (AutomorphicForm.centralScalar (𝓞 L) L) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    change Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact Units.continuous_val
    · exact continuous_const
  · refine continuous_matrix fun i j => ?_
    change Continuous fun z : (AdeleRing (𝓞 L) L)ˣ =>
      Matrix.scalar (Fin 2) ((z⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact Units.continuous_coe_inv
    · exact continuous_const

private theorem continuous_sigmaAdelicAct_centralScalar_mul :
    Continuous fun q : (AdeleRing (𝓞 L) L)ˣ × AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L q.1 * q.2) :=
  (continuous_sigmaAdelicAct'' K L D σ).comp
    (((continuous_centralScalar L).comp continuous_fst).mul continuous_snd)

private theorem continuous_finsum_mem_centralScalar (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (T : Set (GL (Fin 2) L)) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    Continuous fun z : (AdeleRing (𝓞 L) L)ˣ =>
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) := by
  have hzx : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => (z, x) := continuous_id.prodMk continuous_const
  have hact := (continuous_sigmaAdelicAct_centralScalar_mul K L D σ).comp hzx
  have hpair := (continuous_const (y := x)).prodMk hact
  have h := (continuous_finsum_mem L hfin φ hφc hφs T).comp hpair
  exact h

private theorem exists_forall_norm_mul_finsum_mem_le (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (T : Set (GL (Fin 2) L)) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (Z : Set (AdeleRing (𝓞 L) L)ˣ) {W : Set (AdeleRing (𝓞 L) L)ˣ} (hW : IsCompact W)
    (hrep : ∀ z ∈ Z, ∃ η : Lˣ, ∃ w ∈ W,
      z = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w)
    (hZ : ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L), ∀ z ∉ Z,
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) = 0)
    (hper : ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (ζ : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ),
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L
          (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) ζ * z) * x))
      = ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)))
    {X : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)} (hX : IsCompact X) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ X, ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))‖ ≤ M := by
  have hY : IsCompact ((fun q : (AdeleRing (𝓞 L) L)ˣ × AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L q.1 * q.2)) ''
        (W ×ˢ X)) :=
    (hW.prod hX).image (continuous_sigmaAdelicAct_centralScalar_mul K L D σ)
  obtain ⟨MK, hMK0, hMK⟩ := exists_forall_norm_finsum_mem_le L hfin φ hφc hφs T hX hY
  obtain ⟨Mξ, hMξ⟩ := hW.exists_bound_of_continuousOn hξc.continuousOn
  refine ⟨max Mξ 0 * MK, mul_nonneg (le_max_right _ _) hMK0, fun x hx z => ?_⟩
  by_cases hz : z ∈ Z
  · obtain ⟨η, w, hw, rfl⟩ := hrep z hz
    have hξ : ξL ⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w,
          Subgroup.mem_top _⟩ = ξL ⟨w, Subgroup.mem_top w⟩ := by
      rw [show (⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w, Subgroup.mem_top _⟩ :
            (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ))
          = ⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η, Subgroup.mem_top _⟩ *
            ⟨w, Subgroup.mem_top w⟩ from rfl,
        map_mul, hξt _ (MonoidHom.mem_range.mpr ⟨η, rfl⟩), one_mul]
    rw [hper x η w, hξ, norm_mul]
    exact mul_le_mul ((hMξ w hw).trans (le_max_left _ _)) (hMK x hx _ ⟨(w, x), ⟨hw, hx⟩, rfl⟩)
      (norm_nonneg _) (le_max_right _ _)
  · rw [hZ x z hz, mul_zero, norm_zero]
    exact mul_nonneg (le_max_right _ _) hMK0

private theorem integrableOn_mul_finsum_mem [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
    [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ) (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (T : Set (GL (Fin 2) L)) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (Z : Set (AdeleRing (𝓞 L) L)ˣ) (hZm : MeasurableSet Z) (hvol : νZL (Z ∩ ΩL) < ⊤)
    {W : Set (AdeleRing (𝓞 L) L)ˣ} (hW : IsCompact W)
    (hrep : ∀ z ∈ Z, ∃ η : Lˣ, ∃ w ∈ W,
      z = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w)
    (hZ : ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L), ∀ z ∉ Z,
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) = 0)
    (hper : ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (ζ : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ),
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L
          (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) ζ * z) * x))
      = ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)))
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL := by
  obtain ⟨M, -, hM⟩ := exists_forall_norm_mul_finsum_mem_le K L D σ hfin φ hφc hφs T ξL hξc hξt Z hW
    hrep hZ hper isCompact_singleton (X := {x})
  have hg : Integrable (Z.indicator fun _ => M) (νZL.restrict ΩL) := by
    rw [integrable_indicator_iff hZm]
    exact integrableOn_const (by rw [Measure.restrict_apply hZm]; exact hvol.ne)
  have hmeas : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) :=
    hξc.mul (continuous_finsum_mem_centralScalar K L D σ hfin φ hφc hφs T x)
  show Integrable _ (νZL.restrict ΩL)
  refine Integrable.mono' hg hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ Z
  · rw [Set.indicator_of_mem hz]
    exact hM x (Set.mem_singleton x) z
  · have h0 := hZ x z hz
    simp only [Set.indicator_of_notMem hz, h0, mul_zero, norm_zero, le_refl]

end Fold

section Representatives

variable (L : Type) [Field L] [NumberField L]

private theorem ideleNorm_one'' : NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) = 1 := by
  have h : NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) *
      NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ)
        = NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) := by
    rw [← NumberField.TateGlobal.ideleNorm_mul, mul_one]
  exact mul_left_cancel₀ (NumberField.TateGlobal.ideleNorm_pos (1 : (AdeleRing (𝓞 L) L)ˣ)).ne'
    (h.trans (mul_one _).symm)

private theorem ideleNorm_inv'' (u : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L u⁻¹ = (NumberField.TateGlobal.ideleNorm L u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← NumberField.TateGlobal.ideleNorm_mul, inv_mul_cancel, ideleNorm_one'']

private theorem exists_isCompact_forall_mem_shell_exists_eq_mul
    (hK : ∃ Kc : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact Kc ∧
      Kc ⊆ (NumberField.TateGlobal.normOneIdeles L : Set (AdeleRing (𝓞 L) L)ˣ) ∧
      ∀ x ∈ NumberField.TateGlobal.normOneIdeles L, ∃ (η : Lˣ) (κ : (AdeleRing (𝓞 L) L)ˣ), κ ∈ Kc ∧
        x = Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom η * κ)
    (hs : ∃ s : ℝ≥0ˣ →* (AdeleRing (𝓞 L) L)ˣ, Continuous s ∧
      (∀ r : ℝ≥0ˣ, NumberField.TateGlobal.ideleNorm L (s r) = ((r : ℝ≥0) : ℝ)) ∧
      ∀ r : ℝ≥0ˣ, ((s r : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 = 1)
    {a b : ℝ≥0} (ha : 0 < a) :
    ∃ W : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact W ∧
      ∀ z : (AdeleRing (𝓞 L) L)ˣ, NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (a : ℝ) b →
        ∃ η : Lˣ, ∃ w ∈ W, z = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w := by
  obtain ⟨Kc, hKc, -, hKrep⟩ := hK
  obtain ⟨s, hsc, hsn, -⟩ := hs
  haveI : CompactSpace (Set.Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let F : Set.Icc a b → (AdeleRing (𝓞 L) L)ˣ := fun t =>
    s (Units.mk0 (t : ℝ≥0) (ha.trans_le t.2.1).ne')
  have hF : Continuous F := by
    refine hsc.comp (Units.continuous_iff.mpr ⟨continuous_subtype_val, ?_⟩)
    exact continuous_subtype_val.inv₀ fun t => (ha.trans_le t.2.1).ne'
  refine ⟨Set.range F * Kc, (isCompact_range hF).mul hKc, fun z hz => ?_⟩

  have hr0 : 0 ≤ NumberField.TateGlobal.ideleNorm L z := (NumberField.TateGlobal.ideleNorm_pos z).le
  have hz' : (⟨NumberField.TateGlobal.ideleNorm L z, hr0⟩ : ℝ≥0) ∈ Set.Icc a b :=
    ⟨NNReal.coe_le_coe.mp hz.1, NNReal.coe_le_coe.mp hz.2⟩
  set t : Set.Icc a b := ⟨_, hz'⟩ with ht
  have hFt : NumberField.TateGlobal.ideleNorm L (F t) = NumberField.TateGlobal.ideleNorm L z :=
    hsn (Units.mk0 ⟨NumberField.TateGlobal.ideleNorm L z, hr0⟩ (ha.trans_le hz'.1).ne')

  have hnorm : z * (F t)⁻¹ ∈ NumberField.TateGlobal.normOneIdeles L := by
    rw [NumberField.TateGlobal.mem_normOneIdeles_iff, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_inv'',
      hFt]
    exact mul_inv_cancel₀ (NumberField.TateGlobal.ideleNorm_pos z).ne'
  obtain ⟨η, κ, hκ, hzκ⟩ := hKrep _ hnorm
  refine ⟨η, F t * κ, Set.mul_mem_mul ⟨t, rfl⟩ hκ, ?_⟩
  have hz'' : z = z * (F t)⁻¹ * F t := by rw [inv_mul_cancel_right]
  rw [hz'', hzκ]
  simp only [RingHom.toMonoidHom_eq_coe, mul_assoc, mul_comm κ (F t)]

end Representatives

end KernelFoldBounds

end FoldBounds

section ShellVolume

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal

namespace ShellVolume

section Shell

variable (L : Type) [Field L] [NumberField L]

private theorem continuous_det_gl :
    Continuous fun g : AutomorphicForm.AdelicGL2 (𝓞 L) L => Matrix.GeneralLinearGroup.det g := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_det
  · exact Units.continuous_coe_inv.matrix_det

private theorem exists_forall_ideleNorm_det_mem_Icc (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ)
    (hφs : HasCompactSupport φ) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ g : AutomorphicForm.AdelicGL2 (𝓞 L) L, φ g ≠ 0 →
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b := by
  set N : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℝ :=
    fun g => NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) with hN
  have hNc : Continuous N := (NumberField.TateGlobal.continuous_ideleNorm L).comp (continuous_det_gl L)
  have hS : IsCompact (N '' tsupport φ) := hφs.image hNc
  by_cases hne : (N '' tsupport φ).Nonempty
  · obtain ⟨a, haS, ha⟩ := hS.exists_isLeast hne
    obtain ⟨b, hbS, hb⟩ := hS.exists_isGreatest hne
    obtain ⟨ga, -, hga⟩ := haS
    have ha_pos : 0 < a := by
      rw [← hga]
      exact NumberField.TateGlobal.ideleNorm_pos _
    refine ⟨a, b, ha_pos, ha hbS, fun g hg => ?_⟩
    have hgN : N g ∈ N '' tsupport φ := ⟨g, subset_tsupport φ hg, rfl⟩
    exact ⟨ha hgN, hb hgN⟩
  · refine ⟨1, 1, one_pos, le_rfl, fun g hg => ?_⟩
    exact (hne ⟨N g, g, subset_tsupport φ hg, rfl⟩).elim

private theorem measurableSet_shell [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (a b : ℝ) :
    MeasurableSet {z : (AdeleRing (𝓞 L) L)ˣ | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc a b} :=
  (NumberField.TateGlobal.continuous_ideleNorm L).measurable measurableSet_Icc

private theorem mem_shell_of_mul_self_mem {a b : ℝ} (z : (AdeleRing (𝓞 L) L)ˣ)
    (h : NumberField.TateGlobal.ideleNorm L z * NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc a b) :
    NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b) := by
  have h0 : 0 ≤ NumberField.TateGlobal.ideleNorm L z := (NumberField.TateGlobal.ideleNorm_pos z).le
  constructor
  · calc Real.sqrt a ≤ Real.sqrt (NumberField.TateGlobal.ideleNorm L z * NumberField.TateGlobal.ideleNorm L z) :=
          Real.sqrt_le_sqrt h.1
      _ = NumberField.TateGlobal.ideleNorm L z := Real.sqrt_mul_self h0
  · calc NumberField.TateGlobal.ideleNorm L z
          = Real.sqrt (NumberField.TateGlobal.ideleNorm L z * NumberField.TateGlobal.ideleNorm L z) :=
          (Real.sqrt_mul_self h0).symm
      _ ≤ Real.sqrt b := Real.sqrt_le_sqrt h.2

private theorem preimage_smul_shell_eq
    (hn : ∀ η : Lˣ, NumberField.TateGlobal.ideleNorm L
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η) = 1)
    (a b : ℝ) (c : (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range) :
    (fun z : (AdeleRing (𝓞 L) L)ˣ => c • z) ⁻¹'
        {z : (AdeleRing (𝓞 L) L)ˣ | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc a b}
      = {z : (AdeleRing (𝓞 L) L)ˣ | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc a b} := by
  obtain ⟨η, hη⟩ := MonoidHom.mem_range.mp c.2
  ext z
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul,
    NumberField.TateGlobal.ideleNorm_mul, ← hη, hn, one_mul]

end Shell

section Volume

variable (L : Type) [Field L] [NumberField L]
private theorem countable_range_map_algebraMap :
    Countable (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range := by
  haveI : Countable L := Countable.of_equiv _ (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.symm
  haveI : Countable Lˣ := Units.val_injective.countable
  exact (Set.countable_range _).to_subtype

variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]

private theorem smulInvariantMeasure_range (μ : Measure (AdeleRing (𝓞 L) L)ˣ) [μ.IsMulLeftInvariant] :
    SMulInvariantMeasure (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range
      (AdeleRing (𝓞 L) L)ˣ μ := by
  refine ⟨fun c s _ => ?_⟩
  exact measure_preimage_mul μ (c : (AdeleRing (𝓞 L) L)ˣ) s

private theorem measure_shell_inter_lt_top (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    (hn : ∀ η : Lˣ, NumberField.TateGlobal.ideleNorm L
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η) = 1)
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (Dm : Set (AdeleRing (𝓞 L) L)ˣ)
    (hDm : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range Dm νZL)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (k : ℕ)
    (hint : IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => min (NumberField.TateGlobal.ideleNorm L z)
      (NumberField.TateGlobal.ideleNorm L z)⁻¹ ^ k * NumberField.TateGlobal.ideleNorm L z ^ (0 : ℝ)) Dm νZL) :
    νZL ({z : (AdeleRing (𝓞 L) L)ˣ |
      NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b)} ∩ ΩL) < ⊤ := by
  haveI := countable_range_map_algebraMap L
  haveI : MeasurableConstSMul
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range (AdeleRing (𝓞 L) L)ˣ :=
    ⟨fun c => (continuous_const.mul continuous_id).measurable⟩
  haveI := smulInvariantMeasure_range L νZL
  set Z : Set (AdeleRing (𝓞 L) L)ˣ :=
    {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b)} with hZ
  have hZm : MeasurableSet Z := measurableSet_shell L _ _
  rw [hΩL.measure_set_eq hDm hZm (preimage_smul_shell_eq L hn _ _)]

  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr (ha.trans_le hab)
  set ε : ℝ := min (Real.sqrt a) (Real.sqrt b)⁻¹ ^ k with hε
  have hε0 : 0 < ε := pow_pos (lt_min hsa (inv_pos.mpr hsb)) k
  have hsub : Z ⊆ {z : (AdeleRing (𝓞 L) L)ˣ | ε ≤ ‖min (NumberField.TateGlobal.ideleNorm L z)
      (NumberField.TateGlobal.ideleNorm L z)⁻¹ ^ k * NumberField.TateGlobal.ideleNorm L z ^ (0 : ℝ)‖} := by
    intro z hz
    obtain ⟨h₁, h₂⟩ := hz
    have hz0 : 0 < NumberField.TateGlobal.ideleNorm L z := NumberField.TateGlobal.ideleNorm_pos z
    have hmin : min (Real.sqrt a) (Real.sqrt b)⁻¹
        ≤ min (NumberField.TateGlobal.ideleNorm L z) (NumberField.TateGlobal.ideleNorm L z)⁻¹ :=
      le_min ((min_le_left _ _).trans h₁) ((min_le_right _ _).trans (inv_anti₀ hz0 h₂))
    have hpow : ε ≤ min (NumberField.TateGlobal.ideleNorm L z) (NumberField.TateGlobal.ideleNorm L z)⁻¹ ^ k :=
      pow_le_pow_left₀ (le_min hsa.le (inv_pos.mpr hsb).le) hmin k
    show ε ≤ ‖_‖
    rw [Real.rpow_zero, mul_one]
    exact hpow.trans (le_abs_self _)
  calc νZL (Z ∩ Dm) = νZL.restrict Dm Z := (Measure.restrict_apply hZm).symm
    _ ≤ νZL.restrict Dm {z | ε ≤ ‖min (NumberField.TateGlobal.ideleNorm L z)
          (NumberField.TateGlobal.ideleNorm L z)⁻¹ ^ k * NumberField.TateGlobal.ideleNorm L z ^ (0 : ℝ)‖} :=
        measure_mono hsub
    _ < ⊤ := Integrable.measure_norm_ge_lt_top hint hε0

end Volume

end ShellVolume

end ShellVolume

section IdeleTopology

set_option autoImplicit false

namespace IdeleTopology

variable (F : Type) [Field F] [NumberField F]

private theorem secondCountableTopology_units_adeleRing : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

end IdeleTopology

end IdeleTopology

section Assembly

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHeight

namespace KernelFoldAssembly

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

private theorem ideleNorm_map_algebraMap (η : Lˣ) :
    NumberField.TateGlobal.ideleNorm L
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η) = 1 := by
  have hpos : 0 < NumberField.TateGlobal.ideleNorm L
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η) :=
    NumberField.TateGlobal.ideleNorm_pos _
  have hdet : Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 L) L
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η))
      = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η *
          Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η := by
    apply Units.ext
    show Matrix.det (Matrix.scalar (Fin 2)
        ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η : AdeleRing (𝓞 L) L)))
      = (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η : AdeleRing (𝓞 L) L) *
          (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η : AdeleRing (𝓞 L) L)
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]
  have h1 : NumberField.TateGlobal.ideleNorm L
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η) *
      NumberField.TateGlobal.ideleNorm L
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η) = 1 := by
    rw [← NumberField.TateGlobal.ideleNorm_mul, ← hdet, KernelShell.centralScalar_map_algebraMap L η,
      AutomorphicForm.ideleNorm_det_globalPoints]
  rcases mul_self_eq_one_iff.mp h1 with h | h
  · exact h
  · rw [h] at hpos
    norm_num at hpos

variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

private theorem finsum_mem_eq_zero_of_notMem_shell (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) {a b : ℝ}
    (hsupp : ∀ g : AutomorphicForm.AdelicGL2 (𝓞 L) L, φ g ≠ 0 →
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b)
    (T : Set (GL (Fin 2) L)) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ)
    (hz : z ∉ {z : (AdeleRing (𝓞 L) L)ˣ |
      NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b)}) :
    ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) = 0 := by
  refine finsum_mem_of_eqOn_zero fun δ _ => ?_
  show φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) = 0
  by_contra hne
  obtain ⟨g, hg, hgeq⟩ := KernelShell.ideleNorm_sq_mem_of_ne_zero K L D σ φ x z δ hne
  have h2 : NumberField.TateGlobal.ideleNorm L z * NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc a b := by
    rw [← hgeq]
    exact hsupp g hg
  exact hz (ShellVolume.mem_shell_of_mul_self_mem L z h2)

private theorem integrableOn_mul_finsum_mem_of_stable
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ)
    (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) :
    ∀ T' : Set (GL (Fin 2) L),
      (∀ δ ∈ T', ∀ c : Lˣ, δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈ T') →
      ∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ δ ∈ T', φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL := by
  have hobt2 := ShellVolume.exists_forall_ideleNorm_det_mem_Icc L φ hφs
  obtain ⟨a, b, ha, hab, hsupp⟩ := hobt2
  have hZm : MeasurableSet {z : (AdeleRing (𝓞 L) L)ˣ |
      NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b)} :=
    ShellVolume.measurableSet_shell L _ _
  have hobt3 :=
    NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
      L νZL
  obtain ⟨Dm, _, hDm, htemp⟩ := hobt3
  have hobt4 := htemp 0
  obtain ⟨k, hk⟩ := hobt4
  have hvol : νZL ({z : (AdeleRing (𝓞 L) L)ˣ |
      NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b)} ∩ ΩL) < ⊤ :=
    ShellVolume.measure_shell_inter_lt_top L νZL (KernelFoldAssembly.ideleNorm_map_algebraMap L) ΩL hΩL
      Dm hDm ha hab k hk
  have hobt5 := KernelFoldBounds.exists_isCompact_forall_mem_shell_exists_eq_mul L
    (NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul L)
    (NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq L)
    (a := ⟨Real.sqrt a, Real.sqrt_nonneg a⟩) (b := ⟨Real.sqrt b, Real.sqrt_nonneg b⟩)
    (by rw [← NNReal.coe_pos]; exact Real.sqrt_pos.mpr ha)
  obtain ⟨W, hW, hrepW⟩ := hobt5
  have hrep : ∀ z ∈ {z : (AdeleRing (𝓞 L) L)ˣ |
      NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b)}, ∃ η : Lˣ, ∃ w ∈ W,
        z = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w :=
    fun z hz => hrepW z hz
  have hZ := KernelFoldAssembly.finsum_mem_eq_zero_of_notMem_shell K L D σ φ hsupp
  have hper : ∀ T' : Set (GL (Fin 2) L),
      (∀ δ ∈ T', ∀ c : Lˣ, δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈ T') →
      ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (ζ : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ),
        ∑ᶠ δ ∈ T', φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L
            (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) ζ * z) * x))
        = ∑ᶠ δ ∈ T', φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) :=
    fun T' hT' x ζ z => KernelShell.finsum_mem_centralScalar_map_mul K L D σ φ T' hT' x ζ z
  intro T' hT' x
  exact KernelFoldBounds.integrableOn_mul_finsum_mem K L D σ νZL ΩL hfin φ hφc hφs T' ξL hξc hξt _
      hZm hvol hW hrep (hZ T') (hper T' hT') x

end KernelFoldAssembly

end Assembly

section TruncationFold

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace TruncationFold

section Scalars

variable {K L : Type} [Field K] [Field L] [Algebra K L]

private theorem mul_scalar_mem_setOf_borelNormOne {δ : GL (Fin 2) L}
    (hδ : δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1}) (a : Lˣ) :
    δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1} := by
  obtain ⟨h10, hnorm⟩ := hδ
  have hcoe := CellScalarStability.coe_mul_scalar δ a
  refine ⟨?_, ?_⟩
  · show ((δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0
    rw [hcoe, Matrix.smul_apply, h10, smul_zero]
  · show Algebra.norm K
        (((δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 /
          ((δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1) = 1
    rw [hcoe, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_div_mul_left _ _ (Units.ne_zero a)]
    exact hnorm

variable [NumberField L]

private theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 L) L)ˣ) (h : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.centralScalar (𝓞 L) L z * h = h * AutomorphicForm.centralScalar (𝓞 L) L z := by
  have hcoe : ((AutomorphicForm.centralScalar (𝓞 L) L z : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) := rfl
  ext i j
  have hc := (Matrix.scalar_commute (z : AdeleRing (𝓞 L) L) (fun r => Commute.all _ r)
    ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq
  rw [Units.val_mul, Units.val_mul, hcoe, hc]

private theorem det_unipotentGL2 (q : AdeleRing (𝓞 L) L) :
    Matrix.GeneralLinearGroup.det (AutomorphicForm.unipotentGL2 q : AutomorphicForm.AdelicGL2 (𝓞 L) L) = 1 := by
  apply Units.ext
  show Matrix.det ((AutomorphicForm.unipotentGL2 q : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = 1
  rw [AutomorphicForm.unipotentGL2_coe, Matrix.det_fin_two_of]
  ring

private theorem ideleNorm_det_unipotentGL2_mul (q : AdeleRing (𝓞 L) L) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det x) =
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (AutomorphicForm.unipotentGL2 q * x)) := by
  rw [map_mul, det_unipotentGL2, one_mul]

private theorem unipotentGL2_inv (q : AdeleRing (𝓞 L) L) :
    (AutomorphicForm.unipotentGL2 q : AutomorphicForm.AdelicGL2 (𝓞 L) L)⁻¹ = AutomorphicForm.unipotentGL2 (-q) :=
  Units.ext rfl

private theorem _root_.TruncationFold.continuous_unipotentGL2 :
    Continuous fun q : AdeleRing (𝓞 L) L => (AutomorphicForm.unipotentGL2 q : AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  have hval : Continuous fun q : AdeleRing (𝓞 L) L =>
      ((AutomorphicForm.unipotentGL2 q : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) := by
    simp only [AutomorphicForm.unipotentGL2_coe]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> (try simp) <;> fun_prop
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [unipotentGL2_inv]
  exact hval.comp continuous_neg

p2m_export "TruncationFold" "continuous_unipotentGL2"
end Scalars

section Kernel

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

private theorem ideleNorm_sq_mem_of_ne_zero_of_ideleNorm_det_eq (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ)
    (p y : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (hpy : NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det p) =
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y))
    (z : (AdeleRing (𝓞 L) L)ˣ) (δ : GL (Fin 2) L)
    (hne : φ (p⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ≠ 0) :
    NumberField.TateGlobal.ideleNorm L z * NumberField.TateGlobal.ideleNorm L z ∈
      (fun g : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) '' Function.support φ := by
  refine ⟨_, hne, ?_⟩
  have hp : NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det p) ≠ 0 :=
    (NumberField.TateGlobal.ideleNorm_pos _).ne'
  have hdet : Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 L) L z) = z * z := by
    apply Units.ext
    show Matrix.det (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L)) = (z : AdeleRing (𝓞 L) L) * z
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]
  dsimp only
  rw [map_mul, map_mul, map_inv, NumberField.TateGlobal.ideleNorm_mul,
    NumberField.TateGlobal.ideleNorm_mul, KernelShell.ideleNorm_inv', AutomorphicForm.ideleNorm_det_globalPoints,
    AutomorphicForm.ideleNorm_det_sigmaAdelicAct K L D σ, map_mul,
    NumberField.TateGlobal.ideleNorm_mul, hdet, NumberField.TateGlobal.ideleNorm_mul, ← hpy]
  field_simp

private theorem finsum_mem_centralScalar_map_mul_of_stable (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ)
    (T : Set (GL (Fin 2) L)) (hT : ∀ δ ∈ T, ∀ a : Lˣ, δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ T)
    (p y : AutomorphicForm.AdelicGL2 (𝓞 L) L) (ζ : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ∑ᶠ δ ∈ T, φ (p⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L
          (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* _) ζ * z) * y))
      = ∑ᶠ δ ∈ T, φ (p⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * y)) := by
  have hσ : AutomorphicForm.sigmaAdelicAct K L D σ
        (AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ))
      = AutomorphicForm.globalPoints (𝓞 L) L
          (Matrix.GeneralLinearGroup.map (σ : L →+* L) (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ)) :=
    AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ _
  refine Eq.trans ?_ (KernelShell.finsum_mem_mul_scalar_eq T hT
    (fun δ => φ (p⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * y)))
    (Units.map ((σ : L →+* L) : L →* L) ζ))
  refine finsum_mem_congr rfl fun δ _ => ?_
  beta_reduce
  simp only [map_mul, KernelShell.centralScalar_map_algebraMap, hσ, KernelShell.map_scalar, mul_assoc]

private theorem continuous_finsum_mem_centralScalar_mul_unipotentGL2_mul
    (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L) (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) (T : Set (GL (Fin 2) L))
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    Continuous fun r : (AdeleRing (𝓞 L) L)ˣ × AdeleRing (𝓞 L) L =>
      ∑ᶠ δ ∈ T, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ
          (AutomorphicForm.centralScalar (𝓞 L) L r.1 * (AutomorphicForm.unipotentGL2 r.2 * x))) := by
  have hpt : Continuous fun r : (AdeleRing (𝓞 L) L)ˣ × AdeleRing (𝓞 L) L =>
      AutomorphicForm.sigmaAdelicAct K L D σ
        (AutomorphicForm.centralScalar (𝓞 L) L r.1 * (AutomorphicForm.unipotentGL2 r.2 * x)) :=
    (KernelFoldBounds.continuous_sigmaAdelicAct'' K L D σ).comp
      (((KernelFoldBounds.continuous_centralScalar L).comp continuous_fst).mul
        ((continuous_unipotentGL2.comp continuous_snd).mul continuous_const))
  have h := (KernelFoldBounds.continuous_finsum_mem L hfin φ hφc hφs T).comp ((continuous_const (y := x)).prodMk hpt)
  exact h

private theorem integrableOn_of_forall_norm_le_of_eq_zero [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) (ΩL : Set (AdeleRing (𝓞 L) L)ˣ) (G : (AdeleRing (𝓞 L) L)ˣ → ℂ)
    (hG : AEStronglyMeasurable G (νZL.restrict ΩL)) (Z : Set (AdeleRing (𝓞 L) L)ˣ) (hZm : MeasurableSet Z)
    (hvol : νZL (Z ∩ ΩL) < ⊤) (M : ℝ) (hM : ∀ z ∈ Z, ‖G z‖ ≤ M) (hZ : ∀ z ∉ Z, G z = 0) :
    IntegrableOn G ΩL νZL := by
  have hg : Integrable (Z.indicator fun _ => M) (νZL.restrict ΩL) := by
    rw [integrable_indicator_iff hZm]
    exact integrableOn_const (by rw [Measure.restrict_apply hZm]; exact hvol.ne)
  show Integrable _ (νZL.restrict ΩL)
  refine Integrable.mono' hg hG (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ Z
  · rw [Set.indicator_of_mem hz]
    exact hM z hz
  · simp only [Set.indicator_of_notMem hz, hZ z hz, norm_zero, le_refl]

private theorem constantTerm_cond_adelicBox (f : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
        (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
        (fun t => AutomorphicForm.unipotentGL2 t) f g =
      ∫ q, f (AutomorphicForm.unipotentGL2 q * g)
        ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) :=
  rfl

private theorem ae_cond_adelicBox_mem :
    ∀ᵐ q ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)), q ∈ adelicBox L := by
  unfold ProbabilityTheory.cond
  exact MeasureTheory.Measure.ae_smul_measure (ae_restrict_mem (measurableSet_adelicBox L)) _

open _root_.AutomorphicForm in
open scoped TensorProduct.RightActions in

private theorem integrableOn_mul_indicator_constantTerm_finsum_borelNormOne
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L) (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 L) L)
            (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ΩL νZL := by

  have hhigh : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      AutomorphicForm.centralScalar (𝓞 L) L z * x ∈
          AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R) ↔
        x ∈ AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R) := by
    intro z
    rw [AutomorphicForm.mem_highSet_iff, AutomorphicForm.mem_highSet_iff,
      (NumberField.AdelicHeight.adelicHeight_unipotentGL2_mul_and_centralScalar_mul L).2 z x]
  by_cases hx : x ∈ AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
  swap
  · have hnot : ∀ z : (AdeleRing (𝓞 L) L)ˣ, AutomorphicForm.centralScalar (𝓞 L) L z * x ∉
        AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R) :=
      fun z h => hx ((hhigh z).1 h)
    simp only [Set.indicator_of_notMem (hnot _), mul_zero]
    exact integrableOn_zero
  have hmem : ∀ z : (AdeleRing (𝓞 L) L)ˣ, AutomorphicForm.centralScalar (𝓞 L) L z * x ∈
      AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R) :=
    fun z => (hhigh z).2 hx

  have hpt : ∀ (z : (AdeleRing (𝓞 L) L)ˣ) (q : AdeleRing (𝓞 L) L),
      AutomorphicForm.unipotentGL2 q * (AutomorphicForm.centralScalar (𝓞 L) L z * x) =
        AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 q * x) := by
    intro z q
    rw [← mul_assoc, ← TruncationFold.centralScalar_mul_comm z (AutomorphicForm.unipotentGL2 q), mul_assoc]
  simp only [Set.indicator_of_mem (hmem _), TruncationFold.constantTerm_cond_adelicBox, hpt]

  have hT : ∀ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
        Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
      ∀ a : Lˣ, δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ {γ : GL (Fin 2) L |
        (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
        Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1} :=
    fun δ hδ a => TruncationFold.mul_scalar_mem_setOf_borelNormOne hδ a

  obtain ⟨a, b, ha, hab, hsupp⟩ := ShellVolume.exists_forall_ideleNorm_det_mem_Icc L φ hφs
  have hZm : MeasurableSet {z : (AdeleRing (𝓞 L) L)ˣ |
      NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b)} :=
    ShellVolume.measurableSet_shell L _ _
  obtain ⟨Dm, _, hDm, htemp⟩ :=
    NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
      L νZL
  obtain ⟨k, hk⟩ := htemp 0
  have hvol : νZL ({z : (AdeleRing (𝓞 L) L)ˣ |
      NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b)} ∩ ΩL) < ⊤ :=
    ShellVolume.measure_shell_inter_lt_top L νZL (KernelFoldAssembly.ideleNorm_map_algebraMap L) ΩL hΩL
      Dm hDm ha hab k hk
  obtain ⟨W, hW, hrepW⟩ := KernelFoldBounds.exists_isCompact_forall_mem_shell_exists_eq_mul L
    (NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul L)
    (NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq L)
    (a := ⟨Real.sqrt a, Real.sqrt_nonneg a⟩) (b := ⟨Real.sqrt b, Real.sqrt_nonneg b⟩)
    (by rw [← NNReal.coe_pos]; exact Real.sqrt_pos.mpr ha)
  have hrep : ∀ z ∈ {z : (AdeleRing (𝓞 L) L)ˣ |
      NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b)}, ∃ η : Lˣ, ∃ w ∈ W,
        z = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w :=
    fun z hz => hrepW z hz

  obtain ⟨C, hC, hboxC⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset L
  have hY : IsCompact ((fun r : (AdeleRing (𝓞 L) L)ˣ × AdeleRing (𝓞 L) L =>
      AutomorphicForm.sigmaAdelicAct K L D σ
        (AutomorphicForm.centralScalar (𝓞 L) L r.1 * (AutomorphicForm.unipotentGL2 r.2 * x))) '' (W ×ˢ C)) :=
    (hW.prod hC).image ((KernelFoldBounds.continuous_sigmaAdelicAct'' K L D σ).comp
      (((KernelFoldBounds.continuous_centralScalar L).comp continuous_fst).mul
        (((TruncationFold.continuous_unipotentGL2 (L := L)).comp continuous_snd).mul continuous_const)))
  obtain ⟨MK, -, hMK⟩ := KernelFoldBounds.exists_forall_norm_finsum_mem_le L hfin φ hφc hφs
    {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1}
    isCompact_singleton hY (X := {x})
  obtain ⟨Mξ, hMξ⟩ := hW.exists_bound_of_continuousOn hξc.continuousOn
  haveI : IsFiniteMeasure
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) := inferInstance
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := IdeleTopology.secondCountableTopology_units_adeleRing L
  have hsm : StronglyMeasurable fun z : (AdeleRing (𝓞 L) L)ˣ =>
      ∫ q, (fun r : (AdeleRing (𝓞 L) L)ˣ × AdeleRing (𝓞 L) L =>
        ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
          Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.centralScalar (𝓞 L) L r.1 * (AutomorphicForm.unipotentGL2 r.2 * x)))) (z, q)
        ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) :=
    (TruncationFold.continuous_finsum_mem_centralScalar_mul_unipotentGL2_mul K L D σ hfin φ hφc hφs _
      x).stronglyMeasurable.integral_prod_right'
  refine TruncationFold.integrableOn_of_forall_norm_le_of_eq_zero L νZL ΩL _ ?_ _ hZm hvol
    (max Mξ 0 * (MK * (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L)
      (adelicBox L)).real Set.univ)) ?_ ?_
  · exact hξc.aestronglyMeasurable.mul hsm.aestronglyMeasurable
  ·
    intro z hz
    obtain ⟨η, w, hw, rfl⟩ := hrep z hz
    have hξ : ξL ⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w,
          Subgroup.mem_top _⟩ = ξL ⟨w, Subgroup.mem_top w⟩ := by
      rw [show (⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η * w, Subgroup.mem_top _⟩ :
            (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ))
          = ⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η, Subgroup.mem_top _⟩ *
            ⟨w, Subgroup.mem_top w⟩ from rfl,
        map_mul, hξt _ (MonoidHom.mem_range.mpr ⟨η, rfl⟩), one_mul]
    simp only [hξ, TruncationFold.finsum_mem_centralScalar_map_mul_of_stable K L D σ φ _ hT, norm_mul]
    refine mul_le_mul ((hMξ w hw).trans (le_max_left _ _)) ?_ (norm_nonneg _) (le_max_right _ _)
    refine norm_integral_le_of_norm_le_const ((TruncationFold.ae_cond_adelicBox_mem L).mono fun q hq => ?_)
    exact hMK x (Set.mem_singleton x) _ ⟨(w, q), ⟨hw, hboxC hq⟩, rfl⟩
  ·
    intro z hz
    have h0 : ∀ q : AdeleRing (𝓞 L) L,
        ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
          Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 q * x))) = 0 := by
      intro q
      refine finsum_mem_of_eqOn_zero fun δ _ => ?_
      by_contra hne
      obtain ⟨g, hg, hgeq⟩ := TruncationFold.ideleNorm_sq_mem_of_ne_zero_of_ideleNorm_det_eq K L D σ φ x _
        (TruncationFold.ideleNorm_det_unipotentGL2_mul q x) z δ hne
      have h2 : NumberField.TateGlobal.ideleNorm L z * NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc a b := by
        rw [← hgeq]
        exact hsupp g hg
      exact hz (ShellVolume.mem_shell_of_mul_self_mem L z h2)
    simp only [h0, integral_zero, mul_zero]

end Kernel

end TruncationFold

end TruncationFold
end BlockISections

section TwistedBruhatProofs

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_UnipotentTermUnfolding_exists_forall_setIntegral_unipotentTerm_eq_mul_integral_iwasawa.AutomorphicForm"
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsSemiLocalFactorization IsFactorizableTestFn WindowedSiegel.centreCutSiegelSet AdelicGL2 globalPoints centralScalar unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm sigmaAdelicAct sigmaAdelicAct_globalPoints IsCentralType IsUnipotentType IsHyperbolicType IsEllipticType centralCell unipotentCell hyperbolicCell ellipticCell highSet mem_highSet_iff AdelicKernelLocalFiniteness borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd globalPoints_apply adelicMaximalCompact maximalCompactHaar TwistedBruhat.normUnipotentSet TwistedBruhat.borelNormOneSet TwistedBruhat.IsCuspTransversal TwistedBruhat.cuspKernel TwistedBruhat.cuspTruncation adelicKernelLocalFiniteness continuous_and_hasCompactSupport_of_isFactorizableTestFn ideleNorm_det_globalPoints ideleNorm_det_sigmaAdelicAct WindowedSiegel.exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet continuous_unipotentGL2"
namespace TwistedBruhat
p2m_export "AutomorphicForm.TwistedBruhat" "normUnipotentSet borelNormOneSet IsCuspTransversal cuspKernel cuspTruncation"
p2m_open "AutomorphicForm.TwistedBruhat AutomorphicForm"

private theorem cuspTruncation_apply (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) (x : AdelicGL2 (𝓞 L) L) :
    cuspTruncation K L D σ R φ z x =
      Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 L) L)
            (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x) :=
  rfl

namespace HeightShapeInvariance

open AutomorphicForm.WindowedSiegel NumberField.AdelicHeight

section Local

variable {K₀ : Type*} [NormedField K₀]

private theorem det_unipotent_shape {s : GL (Fin 2) K₀}
    (h00 : (s : Matrix (Fin 2) (Fin 2) K₀) 0 0 = 1) (h10 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 1 = 1) : (s : Matrix (Fin 2) (Fin 2) K₀).det = 1 := by
  rw [Matrix.det_fin_two, h00, h10, h11]
  ring

private theorem localHeight_unipotent_shape_mul {s : GL (Fin 2) K₀}
    (h00 : (s : Matrix (Fin 2) (Fin 2) K₀) 0 0 = 1) (h10 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 1 = 1) (g : GL (Fin 2) K₀) :
    localHeight (s * g) = localHeight g := by
  have hcoe : ((s * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)
      = (s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀) := rfl
  unfold localHeight
  rw [rowNormSq_scalar_entries_mul h10 h11 g, norm_one, one_pow, one_mul, hcoe, Matrix.det_mul,
    det_unipotent_shape h00 h10 h11, one_mul]

private theorem rowMaxNorm_unipotent_shape_mul {s : GL (Fin 2) K₀}
    (h10 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 1 = 1)
    (g : GL (Fin 2) K₀) :
    rowMaxNorm ((s * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)
      = rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K₀) := by
  have hcoe : ((s * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)
      = (s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀) := rfl
  have e10 : ((s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀)) 1 0
      = (g : Matrix (Fin 2) (Fin 2) K₀) 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  have e11 : ((s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀)) 1 1
      = (g : Matrix (Fin 2) (Fin 2) K₀) 1 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  unfold rowMaxNorm
  rw [hcoe, e10, e11]

private theorem finLocalHeight_unipotent_shape_mul {s : GL (Fin 2) K₀}
    (h00 : (s : Matrix (Fin 2) (Fin 2) K₀) 0 0 = 1) (h10 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 1 = 1) (g : GL (Fin 2) K₀) :
    finLocalHeight (s * g) = finLocalHeight g := by
  have hcoe : ((s * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)
      = (s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀) := rfl
  unfold finLocalHeight
  rw [rowMaxNorm_unipotent_shape_mul h10 h11 g, hcoe, Matrix.det_mul, det_unipotent_shape h00 h10 h11,
    one_mul]

private theorem rowMaxNorm_scalar_shape_mul {s : GL (Fin 2) K₀} {z : K₀}
    (h10 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 1 = z)
    (g : GL (Fin 2) K₀) :
    rowMaxNorm ((s * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)
      = ‖z‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K₀) := by
  have hcoe : ((s * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)
      = (s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀) := rfl
  have e10 : ((s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀)) 1 0
      = z * (g : Matrix (Fin 2) (Fin 2) K₀) 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  have e11 : ((s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀)) 1 1
      = z * (g : Matrix (Fin 2) (Fin 2) K₀) 1 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  unfold rowMaxNorm
  rw [hcoe, e10, e11, norm_mul, norm_mul, mul_max_of_nonneg _ _ (norm_nonneg z)]

private theorem finLocalHeight_scalar_shape_mul {s : GL (Fin 2) K₀} {z : K₀} (hz : z ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K₀) 0 0 = z) (h01 : (s : Matrix (Fin 2) (Fin 2) K₀) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 1 = z)
    (g : GL (Fin 2) K₀) :
    finLocalHeight (s * g) = finLocalHeight g := by
  have hcoe : ((s * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)
      = (s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀) := rfl
  have hdets : (s : Matrix (Fin 2) (Fin 2) K₀).det = z ^ 2 := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11]
    ring
  have hz2 : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  unfold finLocalHeight
  rw [rowMaxNorm_scalar_shape_mul h10 h11 g, hcoe, Matrix.det_mul, hdets, norm_mul, norm_pow, mul_pow,
    mul_div_mul_left _ _ hz2]

end Local

section Adelic

variable (L : Type) [Field L] [NumberField L]

private theorem adelicHeight_unipotent_shape_mul {n : AutomorphicForm.AdelicGL2 (𝓞 L) L}
    (h00 : (n : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = 1)
    (h10 : (n : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0)
    (h11 : (n : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = 1)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    adelicHeight L (n * g) = adelicHeight L g := by
  unfold adelicHeight
  rw [map_mul, map_mul]
  have harch : archHeight L (glArch (𝓞 L) L n * glArch (𝓞 L) L g) = archHeight L (glArch (𝓞 L) L g) := by
    unfold archHeight
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_mul]
    congr 1
    refine localHeight_unipotent_shape_mul ?_ ?_ ?_ (archComponent L w (glArch (𝓞 L) L g))
    · rw [archComponent_apply, glArch_apply, h00]
      rfl
    · rw [archComponent_apply, glArch_apply, h10]
      rfl
    · rw [archComponent_apply, glArch_apply, h11]
      rfl
  have hfin : finHeight L (glFin (𝓞 L) L n * glFin (𝓞 L) L g) = finHeight L (glFin (𝓞 L) L g) := by
    unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul]
    refine finLocalHeight_unipotent_shape_mul ?_ ?_ ?_ (finComponent (𝓞 L) L v (glFin (𝓞 L) L g))
    · rw [finComponent_apply, glFin_apply, h00]
      rfl
    · rw [finComponent_apply, glFin_apply, h10]
      rfl
    · rw [finComponent_apply, glFin_apply, h11]
      rfl
  rw [harch, hfin]

private theorem adelicHeight_scalar_shape_mul {s : AutomorphicForm.AdelicGL2 (𝓞 L) L} {ζ : AdeleRing (𝓞 L) L}
    (h00 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = ζ)
    (h01 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = ζ)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    adelicHeight L (s * g) = adelicHeight L g := by
  have hdets : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).det = ζ * ζ := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11, mul_zero, sub_zero]
  have hζ : IsUnit ζ := by
    have hu := Matrix.isUnits_det_units s
    rw [hdets] at hu
    exact (IsUnit.mul_iff.mp hu).1
  unfold adelicHeight
  rw [map_mul, map_mul]
  have harch : archHeight L (glArch (𝓞 L) L s * glArch (𝓞 L) L g) = archHeight L (glArch (𝓞 L) L g) := by
    refine archHeight_scalar_entries_mul L (z := ζ.1) ?_ ?_ ?_ ?_ ?_ (glArch (𝓞 L) L g)
    · intro w
      exact ((hζ.map (adeleArch (𝓞 L) L)).map (archEval L w)).ne_zero
    · rw [glArch_apply, h00]
    · rw [glArch_apply, h01]
      rfl
    · rw [glArch_apply, h10]
      rfl
    · rw [glArch_apply, h11]
  have hfin : finHeight L (glFin (𝓞 L) L s * glFin (𝓞 L) L g) = finHeight L (glFin (𝓞 L) L g) := by
    unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul]
    refine finLocalHeight_scalar_shape_mul (z := ζ.2 v) ?_ ?_ ?_ ?_ ?_
      (finComponent (𝓞 L) L v (glFin (𝓞 L) L g))
    · exact ((hζ.map (RingHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))).map
        (finAdeleEval (𝓞 L) L v)).ne_zero
    · rw [finComponent_apply, glFin_apply, h00]
    · rw [finComponent_apply, glFin_apply, h01]
      rfl
    · rw [finComponent_apply, glFin_apply, h10]
      rfl
    · rw [finComponent_apply, glFin_apply, h11]
  rw [harch, hfin]

private theorem adelicHeight_unipotentGL2_mul (t : AdeleRing (𝓞 L) L) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    adelicHeight L (AutomorphicForm.unipotentGL2 t * g) = adelicHeight L g :=
  adelicHeight_unipotent_shape_mul L (by simp [AutomorphicForm.unipotentGL2_coe])
    (by simp [AutomorphicForm.unipotentGL2_coe]) (by simp [AutomorphicForm.unipotentGL2_coe]) g

private theorem adelicHeight_centralScalar_mul (z : (AdeleRing (𝓞 L) L)ˣ) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    adelicHeight L (AutomorphicForm.centralScalar (𝓞 L) L z * g) = adelicHeight L g := by
  have hcoe : ((AutomorphicForm.centralScalar (𝓞 L) L z : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) := rfl
  refine adelicHeight_scalar_shape_mul L (ζ := (z : AdeleRing (𝓞 L) L)) ?_ ?_ ?_ ?_ g <;>
    simp [hcoe, Matrix.scalar_apply]
end Adelic

end HeightShapeInvariance

private theorem exists_isCuspTransversal (L : Type) [Field L] :
    ∃ reps : Set (GL (Fin 2) L), IsCuspTransversal L reps := by
  refine ⟨Set.range fun q : Quotient (QuotientGroup.rightRel (AutomorphicForm.borelSubgroup L)) => q.out, fun g => ?_⟩
  refine ⟨(Quotient.mk (QuotientGroup.rightRel (AutomorphicForm.borelSubgroup L)) g).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · exact (QuotientGroup.rightRel_apply (s := AutomorphicForm.borelSubgroup L)).mp (Quotient.mk_out g)
  · rintro ρ ⟨⟨q, rfl⟩, hq⟩
    have h1 : Quotient.mk (QuotientGroup.rightRel (AutomorphicForm.borelSubgroup L)) q.out =
        Quotient.mk (QuotientGroup.rightRel (AutomorphicForm.borelSubgroup L)) g :=
      Quotient.sound ((QuotientGroup.rightRel_apply (s := AutomorphicForm.borelSubgroup L)).mpr hq)
    rw [Quotient.out_eq] at h1
    rw [h1]

section Bruhat

open LT.TwistedNorm
open scoped Matrix

private theorem map_mem_borel' {L : Type} [Field L] (f : L →+* L) {b : GL (Fin 2) L}
    (hb : b ∈ AutomorphicForm.borelSubgroup L) :
    Matrix.GeneralLinearGroup.map f b ∈ AutomorphicForm.borelSubgroup L := by
  rw [AutomorphicForm.mem_borelSubgroup_iff] at hb ⊢
  rw [coe_generalLinearGroup_map, Matrix.map_apply, hb, map_zero]

private theorem twistedConj_mem_normUnipotentSet' {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (b : GL (Fin 2) L)
    {δ : GL (Fin 2) L} (hδ : δ ∈ normUnipotentSet K L σ hgen) :
    b⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b ∈ normUnipotentSet K L σ hgen := by
  obtain ⟨γ, hγ, hclass⟩ := hδ
  refine ⟨γ, hγ, ?_⟩
  have hmk : SigmaConjClasses.mk σ δ =
      SigmaConjClasses.mk σ (b⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) :=
    SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨b, rfl⟩
  rw [← hmk]
  exact hclass

private theorem centralScalar_mul_comm' {L : Type} [Field L] [NumberField L] (z : (AdeleRing (𝓞 L) L)ˣ)
    (h : AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.centralScalar (𝓞 L) L z * h = h * AutomorphicForm.centralScalar (𝓞 L) L z := by
  have hcoe : ((AutomorphicForm.centralScalar (𝓞 L) L z : AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) := rfl
  ext i j
  have hc := (Matrix.scalar_commute (z : AdeleRing (𝓞 L) L) (fun r => Commute.all _ r)
    ((h : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq
  rw [Units.val_mul, Units.val_mul, hcoe, hc]

private theorem sigmaAdelicAct_globalPoints_mul' {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) L)
    (w : AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.globalPoints (𝓞 L) L γ * w) =
      AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ) *
        AutomorphicForm.sigmaAdelicAct K L D σ w := by
  rw [map_mul]
  congr 1
  exact AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ γ

private theorem coe_map_algebraMap {K L : Type} [Field K] [Field L] [Algebra K L] (γ : GL (Fin 2) K) :
    ((Matrix.GeneralLinearGroup.map (algebraMap K L) γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      (γ : Matrix (Fin 2) (Fin 2) K).map (algebraMap K L) := by
  ext i j
  rfl

private theorem isUnipotentType_conj {L : Type} [Field L] {m : GL (Fin 2) L}
    (hm : AutomorphicForm.IsUnipotentType (m : Matrix (Fin 2) (Fin 2) L)) (Q : GL (Fin 2) L) :
    AutomorphicForm.IsUnipotentType ((Q * m * Q⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
  obtain ⟨hnc, a, ha⟩ := hm
  refine ⟨?_, a, ?_⟩
  · rintro ⟨c, hc⟩
    apply hnc
    refine ⟨c, ?_⟩
    have h1 : (m : Matrix (Fin 2) (Fin 2) L) =
        ((Q⁻¹ * (Q * m * Q⁻¹) * Q : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
      congr 1
      group
    rw [h1, Units.val_mul, Units.val_mul, hc, Matrix.mul_smul, Matrix.smul_mul, mul_one, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  · have hcoe : ((Q * m * Q⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
        (Q : Matrix (Fin 2) (Fin 2) L) * (m : Matrix (Fin 2) (Fin 2) L) * (Q : Matrix (Fin 2) (Fin 2) L)⁻¹ := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    rw [hcoe, Matrix.charpoly_units_conj]
    exact ha

private theorem isUnipotentType_map {K L : Type} [Field K] [Field L] [Algebra K L] {γ : GL (Fin 2) K}
    (hγ : AutomorphicForm.IsUnipotentType (γ : Matrix (Fin 2) (Fin 2) K)) :
    AutomorphicForm.IsUnipotentType
      ((Matrix.GeneralLinearGroup.map (algebraMap K L) γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
  obtain ⟨hnc, a, ha⟩ := hγ
  rw [coe_map_algebraMap]
  refine ⟨?_, algebraMap K L a, ?_⟩
  · rintro ⟨c, hc⟩
    apply hnc
    have hent : ∀ i j,
        algebraMap K L ((γ : Matrix (Fin 2) (Fin 2) K) i j) = c * (1 : Matrix (Fin 2) (Fin 2) L) i j := by
      intro i j
      have h := congrFun (congrFun hc i) j
      simpa [Matrix.map_apply] using h
    have h00 : algebraMap K L ((γ : Matrix (Fin 2) (Fin 2) K) 0 0) = c := by simpa using hent 0 0
    refine ⟨(γ : Matrix (Fin 2) (Fin 2) K) 0 0, ?_⟩
    ext i j
    apply (algebraMap K L).injective
    rw [hent i j, Matrix.smul_apply, smul_eq_mul, map_mul, h00]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  · rw [Matrix.charpoly_map, ha]
    simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

private theorem isUnipotentType_sigmaNormPow {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {δ : GL (Fin 2) L}
    (hδ : δ ∈ normUnipotentSet K L σ hgen) :
    AutomorphicForm.IsUnipotentType
      ((sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L) δ : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) := by
  obtain ⟨γ, hγ, hclass⟩ := hδ
  obtain ⟨P, hP⟩ := isNormRep_normRep hgen δ
  have hclass' : ConjClasses.mk (normRep hgen δ) = ConjClasses.mk γ := by
    rw [← normClassMap_mk hgen δ]
    exact hclass
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hclass')
  have hN : sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L) δ =
      (P * (Matrix.GeneralLinearGroup.map (algebraMap K L) c)⁻¹) * Matrix.GeneralLinearGroup.map (algebraMap K L) γ *
        (P * (Matrix.GeneralLinearGroup.map (algebraMap K L) c)⁻¹)⁻¹ := by
    rw [← hc, map_mul, map_mul, map_inv, ← hP]
    group
  rw [hN]
  exact isUnipotentType_conj (isUnipotentType_map hγ) _

private theorem mulVec_vecOne {L : Type} [Field L] (M : Matrix (Fin 2) (Fin 2) L) :
    M *ᵥ (![1, 0] : Fin 2 → L) = ![M 0 0, M 1 0] := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem mulVec_eq_smul_iff {L : Type} [Field L] (M : Matrix (Fin 2) (Fin 2) L) (w : Fin 2 → L) (c : L) :
    M *ᵥ w = c • w ↔ M 0 0 * w 0 + M 0 1 * w 1 = c * w 0 ∧ M 1 0 * w 0 + M 1 1 * w 1 = c * w 1 := by
  constructor
  · intro h
    exact ⟨by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 0,
      by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1]

private theorem vec_eq_zero_of {L : Type} [Field L] {w : Fin 2 → L} (h0 : w 0 = 0) (h1 : w 1 = 0) : w = 0 := by
  funext i
  fin_cases i <;> simp [h0, h1]

private theorem eigenline {L : Type} [Field L] (M : Matrix (Fin 2) (Fin 2) L)
    (hM : AutomorphicForm.IsUnipotentType M) :
    ∃ v : Fin 2 → L, v ≠ 0 ∧ (∃ c : L, M *ᵥ v = c • v) ∧
      ∀ w : Fin 2 → L, (∃ c : L, M *ᵥ w = c • w) → ∃ t : L, w = t • v := by
  obtain ⟨hnc, a, ha⟩ := hM
  rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two] at ha
  have hexp : ((Polynomial.X : Polynomial L) - Polynomial.C a) ^ 2 =
      Polynomial.X ^ 2 - Polynomial.C (2 * a) * Polynomial.X + Polynomial.C (a * a) := by
    simp only [sub_sq, map_mul, map_ofNat]
    ring
  rw [hexp] at ha
  have h1 := congrArg (fun P : Polynomial L => P.coeff 1) ha
  have h0 := congrArg (fun P : Polynomial L => P.coeff 0) ha
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_X_zero, Polynomial.coeff_C] at h1 h0
  have htr : M 0 0 + M 1 1 = 2 * a := by linear_combination -h1
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = a * a := by linear_combination h0

  have heig : ∀ (w : Fin 2 → L) (c : L), M *ᵥ w = c • w → w ≠ 0 → c = a := by
    intro w c hw hw0
    obtain ⟨e0, e1⟩ := (mulVec_eq_smul_iff M w c).mp hw
    by_contra hca
    have hD : (a - c) * (a - c) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hca)) (sub_ne_zero.mpr (Ne.symm hca))
    have hw0' : (a - c) * (a - c) * w 0 = 0 := by
      linear_combination (M 1 1 - c) * e0 - M 0 1 * e1 - w 0 * hdet + (c * w 0) * htr
    have hw1' : (a - c) * (a - c) * w 1 = 0 := by
      linear_combination (M 0 0 - c) * e1 - M 1 0 * e0 - w 1 * hdet + (c * w 1) * htr
    exact hw0 (vec_eq_zero_of ((mul_eq_zero.mp hw0').resolve_left hD) ((mul_eq_zero.mp hw1').resolve_left hD))
  by_cases hcase : M 0 1 = 0 ∧ M 0 0 = a
  ·
    obtain ⟨hq, hp⟩ := hcase
    have hs : M 1 1 = a := by linear_combination htr - hp
    have hr : M 1 0 ≠ 0 := by
      intro hr
      apply hnc
      refine ⟨a, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, hs]
    refine ⟨![0, 1], ?_, ⟨a, ?_⟩, ?_⟩
    · intro h
      simpa using congrFun h 1
    · rw [mulVec_eq_smul_iff]
      simp [hq, hs]
    · rintro w ⟨c, hw⟩
      by_cases hw0 : w = 0
      · exact ⟨0, by rw [hw0, zero_smul]⟩
      · have hca := heig w c hw hw0
        rw [hca] at hw
        obtain ⟨-, e1⟩ := (mulVec_eq_smul_iff M w a).mp hw
        have hw00 : w 0 = 0 := by
          have h' : M 1 0 * w 0 = 0 := by linear_combination e1 - w 1 * hs
          exact (mul_eq_zero.mp h').resolve_left hr
        refine ⟨w 1, ?_⟩
        funext i
        fin_cases i <;> simp [hw00]
  ·
    refine ⟨![M 0 1, a - M 0 0], ?_, ⟨a, ?_⟩, ?_⟩
    · intro h
      apply hcase
      have h0' := congrFun h 0
      have h1' := congrFun h 1
      simp at h0' h1'
      exact ⟨h0', by linear_combination -h1'⟩
    · rw [mulVec_eq_smul_iff]
      constructor
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        linear_combination a * htr - hdet
    · rintro w ⟨c, hw⟩
      by_cases hw0 : w = 0
      · exact ⟨0, by rw [hw0, zero_smul]⟩
      · have hca := heig w c hw hw0
        rw [hca] at hw
        obtain ⟨e0, -⟩ := (mulVec_eq_smul_iff M w a).mp hw
        by_cases hq : M 0 1 = 0
        · have hp : M 0 0 ≠ a := fun hp => hcase ⟨hq, hp⟩
          have hw00 : w 0 = 0 := by
            have h' : (M 0 0 - a) * w 0 = 0 := by linear_combination e0 - w 1 * hq
            exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hp)
          have hap : a - M 0 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
          refine ⟨w 1 / (a - M 0 0), ?_⟩
          funext i
          fin_cases i
          · simp [hw00, hq]
          · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul]
            rw [div_mul_cancel₀ _ hap]
        · refine ⟨w 0 / M 0 1, ?_⟩
          funext i
          fin_cases i
          · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
            rw [div_mul_cancel₀ _ hq]
          · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul]
            rw [div_mul_eq_mul_div, eq_div_iff hq]
            linear_combination e0

private theorem sigmaNormPow_mem_borel {K L : Type} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)
    {b : GL (Fin 2) L} (hb : b ∈ AutomorphicForm.borelSubgroup L) (ℓ : ℕ) :
    sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) ℓ b ∈ AutomorphicForm.borelSubgroup L := by
  rw [sigmaNormPow_def]
  induction ℓ with
  | zero =>
    rw [sigmaPartialNorm_zero]
    exact (AutomorphicForm.borelSubgroup L).one_mem
  | succ r ih =>
    rw [sigmaPartialNorm_succ']
    exact (AutomorphicForm.borelSubgroup L).mul_mem hb (map_mem_borel' _ ih)

private theorem mulVec_vecOne_of_mem_borel {L : Type} [Field L] {x : GL (Fin 2) L}
    (hx : x ∈ AutomorphicForm.borelSubgroup L) :
    (x : Matrix (Fin 2) (Fin 2) L) *ᵥ (![1, 0] : Fin 2 → L) =
      (x : Matrix (Fin 2) (Fin 2) L) 0 0 • (![1, 0] : Fin 2 → L) := by
  have hx10 : (x : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := hx
  rw [mulVec_vecOne, hx10]
  funext i
  fin_cases i <;> simp

private theorem inv_mulVec_vecOne_ne_zero {L : Type} [Field L] (ρ : GL (Fin 2) L) :
    ((ρ⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) *ᵥ (![1, 0] : Fin 2 → L) ≠ 0 := by
  intro h
  have h' := congrArg (fun w : Fin 2 → L => (ρ : Matrix (Fin 2) (Fin 2) L) *ᵥ w) h
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h'
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h'
  simpa using congrFun h' 0

private theorem exists_sigmaNormPow_mulVec_eq_smul {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {β : GL (Fin 2) L}
    (hβ : β ∈ AutomorphicForm.borelSubgroup L) (ρ : GL (Fin 2) L) :
    ∃ c : L,
      ((sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L)
            (ρ⁻¹ * β * Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) *ᵥ
          (((ρ⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) *ᵥ (![1, 0] : Fin 2 → L)) =
        c • (((ρ⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) *ᵥ (![1, 0] : Fin 2 → L)) := by
  rw [sigmaNormPow_sigmaConj_generalLinearGroup (n := Fin 2) (σ := (σ : L →+* L))
    (fun a => iterate_finrank_apply_of_generator hgen a) ρ β]
  have hNβ := sigmaNormPow_mem_borel σ hβ (Module.finrank K L)
  refine ⟨((sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L) β : GL (Fin 2) L) :
    Matrix (Fin 2) (Fin 2) L) 0 0, ?_⟩
  have hρρ : (ρ : Matrix (Fin 2) (Fin 2) L) * ((ρ⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, mul_assoc _ (ρ : Matrix (Fin 2) (Fin 2) L), hρρ, mul_one,
    ← Matrix.mulVec_mulVec, mulVec_vecOne_of_mem_borel hNβ, Matrix.mulVec_smul]

private theorem mul_inv_mem_borel_of_decomps {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {δ : GL (Fin 2) L}
    (hδ : δ ∈ normUnipotentSet K L σ hgen) {ρ₁ ρ₂ : GL (Fin 2) L}
    (h₁ : ρ₁ * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ₁)⁻¹ ∈ AutomorphicForm.borelSubgroup L)
    (h₂ : ρ₂ * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ₂)⁻¹ ∈ AutomorphicForm.borelSubgroup L) :
    ρ₂ * ρ₁⁻¹ ∈ AutomorphicForm.borelSubgroup L := by
  obtain ⟨v, -, -, huniq⟩ := eigenline _ (isUnipotentType_sigmaNormPow σ hgen hδ)
  have e₁ : ρ₁⁻¹ * (ρ₁ * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ₁)⁻¹) *
      Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ₁ = δ := by group
  have e₂ : ρ₂⁻¹ * (ρ₂ * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ₂)⁻¹) *
      Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ₂ = δ := by group
  obtain ⟨c₁, hc₁⟩ := exists_sigmaNormPow_mulVec_eq_smul σ hgen h₁ ρ₁
  obtain ⟨c₂, hc₂⟩ := exists_sigmaNormPow_mulVec_eq_smul σ hgen h₂ ρ₂
  rw [e₁] at hc₁
  rw [e₂] at hc₂
  obtain ⟨t₁, ht₁⟩ := huniq _ ⟨c₁, hc₁⟩
  obtain ⟨t₂, ht₂⟩ := huniq _ ⟨c₂, hc₂⟩
  have ht₂0 : t₂ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht₂
    exact inv_mulVec_vecOne_ne_zero ρ₂ ht₂
  have hkey : ((ρ₂ * ρ₁⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) *ᵥ (![1, 0] : Fin 2 → L) =
      (t₁ / t₂) • (![1, 0] : Fin 2 → L) := by
    have hv' : t₁ • v = (t₁ / t₂) • (t₂ • v) := by rw [smul_smul, div_mul_cancel₀ _ ht₂0]
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ht₁, hv', ← ht₂, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have h10 : ((ρ₂ * ρ₁⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    have h := congrFun hkey 1
    rw [mulVec_vecOne] at h
    simpa using h
  exact h10

private theorem eigen_transport {L : Type} [Field L] (f : L →+* L) {n δ : GL (Fin 2) L}
    (hσn : Matrix.GeneralLinearGroup.map f n = δ⁻¹ * n * δ) {v : Fin 2 → L} {c : L}
    (hc : (n : Matrix (Fin 2) (Fin 2) L) *ᵥ v = c • v) :
    (n : Matrix (Fin 2) (Fin 2) L) *ᵥ ((δ : Matrix (Fin 2) (Fin 2) L) *ᵥ (⇑f ∘ v)) =
      f c • ((δ : Matrix (Fin 2) (Fin 2) L) *ᵥ (⇑f ∘ v)) := by
  have hmap : ((Matrix.GeneralLinearGroup.map f n : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) *ᵥ (⇑f ∘ v) =
      f c • (⇑f ∘ v) := by
    rw [coe_generalLinearGroup_map]
    funext i
    rw [← RingHom.map_mulVec, hc]
    simp [map_mul]
  have hnδ : n * δ = δ * Matrix.GeneralLinearGroup.map f n := by
    rw [hσn]
    group
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, hnδ, Units.val_mul, ← Matrix.mulVec_mulVec, hmap, Matrix.mulVec_smul]

private theorem exists_mulVec_vecOne_eq {L : Type} [Field L] {v : Fin 2 → L} (hv : v ≠ 0) :
    ∃ P : GL (Fin 2) L, (P : Matrix (Fin 2) (Fin 2) L) *ᵥ (![1, 0] : Fin 2 → L) = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (vec_eq_zero_of h0 h1)
    have hdet : (!![v 0, 1; v 1, 0] : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      simpa [h0] using h1
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩
    rw [show ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      !![v 0, 1; v 1, 0] from rfl, mulVec_vecOne]
    funext i
    fin_cases i <;> simp
  · have hdet : (!![v 0, 0; v 1, 1] : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      simpa using h0
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩
    rw [show ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      !![v 0, 0; v 1, 1] from rfl, mulVec_vecOne]
    funext i
    fin_cases i <;> simp

private theorem map_mulVec_vecOne {L : Type} [Field L] (f : L →+* L) (P : GL (Fin 2) L) :
    ((Matrix.GeneralLinearGroup.map f P : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) *ᵥ (![1, 0] : Fin 2 → L) =
      ⇑f ∘ ((P : Matrix (Fin 2) (Fin 2) L) *ᵥ (![1, 0] : Fin 2 → L)) := by
  have he : (⇑f ∘ (![1, 0] : Fin 2 → L)) = ![1, 0] := by
    funext i
    fin_cases i <;> simp
  rw [coe_generalLinearGroup_map]
  funext i
  rw [Function.comp_apply, RingHom.map_mulVec, he]

private theorem exists_mul_mul_inv_mem_borel {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {δ : GL (Fin 2) L}
    (hδ : δ ∈ normUnipotentSet K L σ hgen) :
    ∃ ρ : GL (Fin 2) L,
      ρ * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ)⁻¹ ∈ AutomorphicForm.borelSubgroup L := by
  obtain ⟨v, hv0, ⟨c, hc⟩, huniq⟩ := eigenline _ (isUnipotentType_sigmaNormPow σ hgen hδ)
  have hσN := map_sigmaNormPow_generalLinearGroup (n := Fin 2) (σ := (σ : L →+* L))
    (fun a => iterate_finrank_apply_of_generator hgen a) δ
  have hw := eigen_transport (σ : L →+* L) hσN hc
  obtain ⟨t, ht⟩ := huniq _ ⟨_, hw⟩
  obtain ⟨P, hP⟩ := exists_mulVec_vecOne_eq hv0
  refine ⟨P⁻¹, ?_⟩
  rw [map_inv, inv_inv]
  have hcol : ((P⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) P : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) *ᵥ
      (![1, 0] : Fin 2 → L) = t • (![1, 0] : Fin 2 → L) := by
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, map_mulVec_vecOne, hP, ht,
      Matrix.mulVec_smul, ← hP, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have h10 : ((P⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) P : GL (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    have h := congrFun hcol 1
    rw [mulVec_vecOne] at h
    simpa using h
  exact h10

end Bruhat

private theorem
    existsUnique_mem_mul_mul_inv_mem_borelSubgroup
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {reps : Set (GL (Fin 2) L)} (hreps : IsCuspTransversal L reps) {δ : GL (Fin 2) L}
    (hδ : δ ∈ normUnipotentSet K L σ hgen) :
    ∃! ρ : GL (Fin 2) L, ρ ∈ reps ∧
      ρ * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ)⁻¹ ∈ AutomorphicForm.borelSubgroup L := by
  obtain ⟨ρ₀, hρ₀⟩ := exists_mul_mul_inv_mem_borel σ hgen hδ
  obtain ⟨ρ, ⟨hρ, hb⟩, -⟩ := hreps ρ₀
  have hdec : ρ * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ)⁻¹ =
      (ρ₀ * ρ⁻¹)⁻¹ * (ρ₀ * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ₀)⁻¹) *
        Matrix.GeneralLinearGroup.map (σ : L →+* L) (ρ₀ * ρ⁻¹) := by
    rw [map_mul, map_inv]
    group
  have hβ : ρ * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ)⁻¹ ∈ AutomorphicForm.borelSubgroup L := by
    rw [hdec]
    exact (AutomorphicForm.borelSubgroup L).mul_mem
      ((AutomorphicForm.borelSubgroup L).mul_mem ((AutomorphicForm.borelSubgroup L).inv_mem hb) hρ₀)
      (map_mem_borel' _ hb)
  refine ⟨ρ, ⟨hρ, hβ⟩, ?_⟩
  rintro ρ' ⟨hρ', hβ'⟩
  have hmem : ρ' * ρ⁻¹ ∈ AutomorphicForm.borelSubgroup L := mul_inv_mem_borel_of_decomps σ hgen hδ hβ hβ'
  exact (hreps ρ').unique ⟨hρ', by rw [mul_inv_cancel]; exact (AutomorphicForm.borelSubgroup L).one_mem⟩ ⟨hρ, hmem⟩

section BruhatRegrouping

open Classical in

private noncomputable def cuspRep {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {reps : Set (GL (Fin 2) L)}
    (hreps : IsCuspTransversal L reps) (δ : GL (Fin 2) L) : GL (Fin 2) L :=
  if h : δ ∈ normUnipotentSet K L σ hgen then
    (existsUnique_mem_mul_mul_inv_mem_borelSubgroup K L σ hgen hreps h).exists.choose
  else 1

private theorem cuspRep_spec {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {reps : Set (GL (Fin 2) L)}
    (hreps : IsCuspTransversal L reps) {δ : GL (Fin 2) L} (hδ : δ ∈ normUnipotentSet K L σ hgen) :
    cuspRep hgen hreps δ ∈ reps ∧
      cuspRep hgen hreps δ * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (cuspRep hgen hreps δ))⁻¹ ∈
        AutomorphicForm.borelSubgroup L := by
  unfold cuspRep
  rw [dif_pos hδ]
  exact (existsUnique_mem_mul_mul_inv_mem_borelSubgroup K L σ hgen hreps hδ).exists.choose_spec

private theorem cuspRep_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {reps : Set (GL (Fin 2) L)}
    (hreps : IsCuspTransversal L reps) {δ : GL (Fin 2) L} (hδ : δ ∈ normUnipotentSet K L σ hgen) {ρ : GL (Fin 2) L}
    (hρ : ρ ∈ reps)
    (hβ : ρ * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ)⁻¹ ∈ AutomorphicForm.borelSubgroup L) :
    cuspRep hgen hreps δ = ρ :=
  (existsUnique_mem_mul_mul_inv_mem_borelSubgroup K L σ hgen hreps hδ).unique (cuspRep_spec hgen hreps hδ) ⟨hρ, hβ⟩

private theorem finsum_mem_normUnipotentSet_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {reps : Set (GL (Fin 2) L)} (hreps : IsCuspTransversal L reps) (f : GL (Fin 2) L → ℂ)
    (hfin : (normUnipotentSet K L σ hgen ∩ Function.support f).Finite) :
    ∑ᶠ δ ∈ normUnipotentSet K L σ hgen, f δ =
      ∑ᶠ ρ ∈ reps, ∑ᶠ β ∈ normUnipotentSet K L σ hgen ∩ (AutomorphicForm.borelSubgroup L : Set (GL (Fin 2) L)),
        f (ρ⁻¹ * β * Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ) := by
  classical
  have hinner : ∀ ρ ∈ reps,
      (∑ᶠ β ∈ normUnipotentSet K L σ hgen ∩ (AutomorphicForm.borelSubgroup L : Set (GL (Fin 2) L)),
          f (ρ⁻¹ * β * Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ)) =
        ∑ δ ∈ hfin.toFinset with cuspRep hgen hreps δ = ρ, f δ := by
    intro ρ hρ
    have hbij : Set.BijOn (fun β => ρ⁻¹ * β * Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ)
        (normUnipotentSet K L σ hgen ∩ (AutomorphicForm.borelSubgroup L : Set (GL (Fin 2) L)))
        {δ | δ ∈ normUnipotentSet K L σ hgen ∧ cuspRep hgen hreps δ = ρ} := by
      refine ⟨?_, ?_, ?_⟩
      · rintro β ⟨hβA, hβB⟩
        refine ⟨twistedConj_mem_normUnipotentSet' σ hgen ρ hβA, ?_⟩
        refine cuspRep_eq hgen hreps (twistedConj_mem_normUnipotentSet' σ hgen ρ hβA) hρ ?_
        have h : ρ * (ρ⁻¹ * β * Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ) *
            (Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ)⁻¹ = β := by group
        show ρ * (ρ⁻¹ * β * Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ) *
          (Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ)⁻¹ ∈ AutomorphicForm.borelSubgroup L
        rw [h]
        exact hβB
      · intro β₁ _ β₂ _ h
        simpa using h
      · rintro δ ⟨hδA, hδρ⟩
        have hβA : ρ⁻¹⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ⁻¹ ∈ normUnipotentSet K L σ hgen :=
          twistedConj_mem_normUnipotentSet' σ hgen ρ⁻¹ hδA
        rw [inv_inv, map_inv] at hβA
        have hβB : ρ * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ)⁻¹ ∈ AutomorphicForm.borelSubgroup L := by
          have h := (cuspRep_spec hgen hreps hδA).2
          rwa [hδρ] at h
        refine ⟨ρ * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ)⁻¹, ⟨hβA, hβB⟩, ?_⟩
        show ρ⁻¹ * (ρ * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ)⁻¹) *
          Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ = δ
        group
    rw [show (∑ᶠ β ∈ normUnipotentSet K L σ hgen ∩ (AutomorphicForm.borelSubgroup L : Set (GL (Fin 2) L)),
          f (ρ⁻¹ * β * Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ)) =
        ∑ᶠ δ ∈ {δ | δ ∈ normUnipotentSet K L σ hgen ∧ cuspRep hgen hreps δ = ρ}, f δ from
      finsum_mem_eq_of_bijOn _ hbij fun β _ => rfl]
    refine finsum_mem_eq_sum_of_subset f ?_ ?_
    · rintro δ ⟨⟨hδA, hδρ⟩, hδf⟩
      have hδS : δ ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hδA, hδf⟩
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hδS, hδρ⟩)
    · intro δ hδ
      have hδ' := Finset.mem_filter.mp (Finset.mem_coe.mp hδ)
      exact ⟨(hfin.mem_toFinset.mp hδ'.1).1, hδ'.2⟩
  have hmaps : ∀ δ ∈ hfin.toFinset, cuspRep hgen hreps δ ∈ hfin.toFinset.image (cuspRep hgen hreps) := fun δ hδ =>
    Finset.mem_image_of_mem _ hδ
  have hsub₁ : reps ∩ Function.support (fun ρ => ∑ δ ∈ hfin.toFinset with cuspRep hgen hreps δ = ρ, f δ) ⊆
      ↑(hfin.toFinset.image (cuspRep hgen hreps)) := by
    rintro ρ ⟨-, hρ⟩
    rw [Function.mem_support] at hρ
    by_contra hno
    apply hρ
    apply Finset.sum_eq_zero
    intro δ hδ
    rw [Finset.mem_filter] at hδ
    have hin := hmaps δ hδ.1
    rw [hδ.2] at hin
    exact absurd (Finset.mem_coe.mpr hin) hno
  have hsub₂ : (↑(hfin.toFinset.image (cuspRep hgen hreps)) : Set (GL (Fin 2) L)) ⊆ reps := by
    intro ρ hρ
    rw [Finset.mem_coe, Finset.mem_image] at hρ
    obtain ⟨δ, hδ, rfl⟩ := hρ
    rw [Set.Finite.mem_toFinset] at hδ
    exact (cuspRep_spec hgen hreps hδ.1).1
  rw [← finsum_mem_inter_support f (normUnipotentSet K L σ hgen), finsum_mem_eq_finite_toFinset_sum f hfin,
    finsum_mem_congr rfl hinner, finsum_mem_eq_sum_of_subset _ hsub₁ hsub₂, Finset.sum_fiberwise_of_maps_to hmaps]

end BruhatRegrouping

private theorem finsum_normUnipotent_eq_finsum_cuspKernel (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (reps : Set (GL (Fin 2) L))
    (hreps : IsCuspTransversal L reps) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (x : AdelicGL2 (𝓞 L) L)
    (hfin : (normUnipotentSet K L σ hgen ∩ Function.support fun δ : GL (Fin 2) L =>
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))).Finite) :
    (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        γ ∈ AutomorphicForm.unipotentCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
        φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) =
      ∑ᶠ ρ ∈ reps, cuspKernel K L D σ hgen φ z (AutomorphicForm.globalPoints (𝓞 L) L ρ * x) := by
  have hcomm : ∀ ρ : GL (Fin 2) L,
      AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.globalPoints (𝓞 L) L ρ * x) =
        AutomorphicForm.globalPoints (𝓞 L) L ρ * (AutomorphicForm.centralScalar (𝓞 L) L z * x) := fun ρ => by
    rw [← mul_assoc, centralScalar_mul_comm', mul_assoc]
  show (∑ᶠ δ ∈ normUnipotentSet K L σ hgen,
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) = _
  rw [finsum_mem_normUnipotentSet_eq hgen hreps _ hfin]
  refine finsum_mem_congr rfl fun ρ _ => ?_
  unfold cuspKernel
  refine finsum_mem_congr rfl fun β _ => ?_
  rw [hcomm, sigmaAdelicAct_globalPoints_mul']
  simp only [map_mul, map_inv, mul_inv_rev]
  congr 1
  group

section Invariance

private theorem generalLinearGroup_map_mem_borel {L : Type} [Field L] (f : L →+* L) {b : GL (Fin 2) L}
    (hb : b ∈ AutomorphicForm.borelSubgroup L) :
    Matrix.GeneralLinearGroup.map f b ∈ AutomorphicForm.borelSubgroup L := by
  rw [AutomorphicForm.mem_borelSubgroup_iff] at hb ⊢
  rw [LT.TwistedNorm.coe_generalLinearGroup_map, Matrix.map_apply, hb, map_zero]

private theorem generalLinearGroup_map_unipotentGL2 {L : Type} [Field L] (f : L →+* L) (k : L) :
    Matrix.GeneralLinearGroup.map f (AutomorphicForm.unipotentGL2 k) = AutomorphicForm.unipotentGL2 (f k) := by
  ext i j
  rw [LT.TwistedNorm.coe_generalLinearGroup_map, AutomorphicForm.unipotentGL2_coe, AutomorphicForm.unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem twistedConj_mem_normUnipotent_inter_borel {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {b : GL (Fin 2) L} (hb : b ∈ AutomorphicForm.borelSubgroup L) {δ : GL (Fin 2) L}
    (hδ : δ ∈ normUnipotentSet K L σ hgen ∩ (AutomorphicForm.borelSubgroup L : Set (GL (Fin 2) L))) :
    b⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b ∈
      normUnipotentSet K L σ hgen ∩ (AutomorphicForm.borelSubgroup L : Set (GL (Fin 2) L)) := by
  obtain ⟨⟨γ, hγ, hclass⟩, hδB⟩ := hδ
  refine ⟨⟨γ, hγ, ?_⟩, ?_⟩
  · have hmk : LT.TwistedNorm.SigmaConjClasses.mk σ δ =
        LT.TwistedNorm.SigmaConjClasses.mk σ (b⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) :=
      LT.TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨b, rfl⟩
    rw [← hmk]
    exact hclass
  · exact (AutomorphicForm.borelSubgroup L).mul_mem ((AutomorphicForm.borelSubgroup L).mul_mem
      ((AutomorphicForm.borelSubgroup L).inv_mem hb) hδB) (generalLinearGroup_map_mem_borel _ hb)

private theorem borel_apply_zero_zero_ne_zero {L : Type} [Field L] {b : GL (Fin 2) L}
    (hb : b ∈ AutomorphicForm.borelSubgroup L) : (b : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
  have h := (AutomorphicForm.borelDiagFst (⟨b, hb⟩ : ↥(AutomorphicForm.borelSubgroup L))).ne_zero
  simpa using h

private theorem borel_apply_one_one_ne_zero {L : Type} [Field L] {b : GL (Fin 2) L}
    (hb : b ∈ AutomorphicForm.borelSubgroup L) : (b : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
  have h := (AutomorphicForm.borelDiagSnd (⟨b, hb⟩ : ↥(AutomorphicForm.borelSubgroup L))).ne_zero
  simpa using h

private theorem mul_apply_diag_of_borel {L : Type} [Field L] {x y : GL (Fin 2) L}
    (hx : (x : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hy : (y : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((x * y : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 =
        (x : Matrix (Fin 2) (Fin 2) L) 0 0 * (y : Matrix (Fin 2) (Fin 2) L) 0 0 ∧
      ((x * y : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 =
        (x : Matrix (Fin 2) (Fin 2) L) 1 1 * (y : Matrix (Fin 2) (Fin 2) L) 1 1 := by
  constructor <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hx, hy]

private theorem inv_apply_diag_of_borel {L : Type} [Field L] {b : GL (Fin 2) L}
    (hb : b ∈ AutomorphicForm.borelSubgroup L) :
    ((b⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = ((b : Matrix (Fin 2) (Fin 2) L) 0 0)⁻¹ ∧
      ((b⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = ((b : Matrix (Fin 2) (Fin 2) L) 1 1)⁻¹ := by
  have hb' : ((b⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 :=
    (AutomorphicForm.borelSubgroup L).inv_mem hb
  have hmul := mul_apply_diag_of_borel (x := b⁻¹) (y := b) hb' hb
  rw [inv_mul_cancel] at hmul
  have h1 : ((1 : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 := by simp
  have h2 : ((1 : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by simp
  rw [h1] at hmul
  rw [h2] at hmul
  exact ⟨eq_inv_of_mul_eq_one_left hmul.1.symm, eq_inv_of_mul_eq_one_left hmul.2.symm⟩

private theorem twistedConj_mem_borelNormOne {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (σ : L ≃ₐ[K] L) {b : GL (Fin 2) L} (hb : b ∈ AutomorphicForm.borelSubgroup L) {δ : GL (Fin 2) L}
    (hδ : δ ∈ borelNormOneSet K L) :
    b⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b ∈ borelNormOneSet K L := by
  obtain ⟨hδ10, hδN⟩ := hδ
  have hδB : δ ∈ AutomorphicForm.borelSubgroup L := hδ10
  have hmem : b⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b ∈ AutomorphicForm.borelSubgroup L :=
    (AutomorphicForm.borelSubgroup L).mul_mem ((AutomorphicForm.borelSubgroup L).mul_mem
      ((AutomorphicForm.borelSubgroup L).inv_mem hb) hδB) (generalLinearGroup_map_mem_borel _ hb)
  refine ⟨hmem, ?_⟩
  have hbinv : ((b⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 :=
    (AutomorphicForm.borelSubgroup L).inv_mem hb
  have hbδ : ((b⁻¹ * δ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 :=
    (AutomorphicForm.borelSubgroup L).mul_mem ((AutomorphicForm.borelSubgroup L).inv_mem hb) hδB
  have hσb : ((Matrix.GeneralLinearGroup.map (σ : L →+* L) b : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 :=
    generalLinearGroup_map_mem_borel _ hb
  obtain ⟨e00, e11⟩ := mul_apply_diag_of_borel hbδ hσb
  obtain ⟨f00, f11⟩ := mul_apply_diag_of_borel hbinv hδ10
  obtain ⟨i00, i11⟩ := inv_apply_diag_of_borel hb
  have hσ00 : ((Matrix.GeneralLinearGroup.map (σ : L →+* L) b : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 =
      σ ((b : Matrix (Fin 2) (Fin 2) L) 0 0) := by
    rw [LT.TwistedNorm.coe_generalLinearGroup_map, Matrix.map_apply]
    rfl
  have hσ11 : ((Matrix.GeneralLinearGroup.map (σ : L →+* L) b : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 =
      σ ((b : Matrix (Fin 2) (Fin 2) L) 1 1) := by
    rw [LT.TwistedNorm.coe_generalLinearGroup_map, Matrix.map_apply]
    rfl
  rw [e00, e11, f00, f11, i00, i11, hσ00, hσ11]
  set a := (b : Matrix (Fin 2) (Fin 2) L) 0 0 with ha_def
  set d := (b : Matrix (Fin 2) (Fin 2) L) 1 1 with hd_def
  set p := (δ : Matrix (Fin 2) (Fin 2) L) 0 0 with hp_def
  set q := (δ : Matrix (Fin 2) (Fin 2) L) 1 1 with hq_def
  have ha : a ≠ 0 := borel_apply_zero_zero_ne_zero hb
  have hd : d ≠ 0 := borel_apply_one_one_ne_zero hb
  have hq : q ≠ 0 := borel_apply_one_one_ne_zero hδB
  have hσa : σ a ≠ 0 := (map_ne_zero σ).mpr ha
  have hσd : σ d ≠ 0 := (map_ne_zero σ).mpr hd
  have hu : a / d ≠ 0 := div_ne_zero ha hd
  have key : a⁻¹ * p * σ a / (d⁻¹ * q * σ d) * (a / d) = p / q * σ (a / d) := by
    rw [map_div₀]
    field_simp
  have hN := congrArg (Algebra.norm K) key
  rw [map_mul, map_mul, Algebra.norm_eq_of_algEquiv, hδN, one_mul] at hN
  have hNu : Algebra.norm K (a / d) ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hu
  exact mul_right_cancel₀ hNu (hN.trans (one_mul _).symm)

private theorem mul_unipotentGL2_mem_borelNormOne {K L : Type} [Field K] [Field L] [Algebra K L] {δ : GL (Fin 2) L}
    (hδ : δ ∈ borelNormOneSet K L) (k : L) : δ * AutomorphicForm.unipotentGL2 k ∈ borelNormOneSet K L := by
  obtain ⟨hδ10, hδN⟩ := hδ
  have h10 : ((δ * AutomorphicForm.unipotentGL2 k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 =
      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 := by
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hδ10]
  have h00 : ((δ * AutomorphicForm.unipotentGL2 k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 =
      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 := by
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((δ * AutomorphicForm.unipotentGL2 k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 =
      (δ : Matrix (Fin 2) (Fin 2) L) 1 1 := by
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hδ10]
  exact ⟨by rw [h10, hδ10], by rw [h00, h11]; exact hδN⟩

private theorem finsum_mem_twistedConj {K L : Type} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (S : Set (GL (Fin 2) L))
    (hS : ∀ b ∈ AutomorphicForm.borelSubgroup L, ∀ δ ∈ S, b⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b ∈ S)
    {b : GL (Fin 2) L} (hb : b ∈ AutomorphicForm.borelSubgroup L) (f : GL (Fin 2) L → ℂ) :
    ∑ᶠ δ ∈ S, f (b⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) = ∑ᶠ δ ∈ S, f δ := by
  refine finsum_mem_eq_of_bijOn (fun δ => b⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ⟨?_, ?_, ?_⟩
    fun δ _ => rfl
  · intro δ hδ
    exact hS b hb δ hδ
  · intro δ₁ _ δ₂ _ h
    simpa using h
  · intro δ' hδ'
    have hbinv : b⁻¹ ∈ AutomorphicForm.borelSubgroup L := (AutomorphicForm.borelSubgroup L).inv_mem hb
    refine ⟨b⁻¹⁻¹ * δ' * Matrix.GeneralLinearGroup.map (σ : L →+* L) b⁻¹, hS b⁻¹ hbinv δ' hδ', ?_⟩
    simp only [inv_inv, map_inv]
    group

private theorem finsum_mem_borelNormOne_mul_unipotentGL2 {K L : Type} [Field K] [Field L] [Algebra K L] (k : L)
    (f : GL (Fin 2) L → ℂ) :
    ∑ᶠ δ ∈ borelNormOneSet K L, f (δ * AutomorphicForm.unipotentGL2 k) = ∑ᶠ δ ∈ borelNormOneSet K L, f δ := by
  refine finsum_mem_eq_of_bijOn (fun δ => δ * AutomorphicForm.unipotentGL2 k) ⟨?_, ?_, ?_⟩ fun δ _ => rfl
  · intro δ hδ
    exact mul_unipotentGL2_mem_borelNormOne hδ k
  · intro δ₁ _ δ₂ _ h
    simpa using h
  · intro δ' hδ'
    refine ⟨δ' * AutomorphicForm.unipotentGL2 (-k), mul_unipotentGL2_mem_borelNormOne hδ' (-k), ?_⟩
    show δ' * AutomorphicForm.unipotentGL2 (-k) * AutomorphicForm.unipotentGL2 k = δ'
    rw [mul_assoc, ← AutomorphicForm.unipotentGL2_add, neg_add_cancel, AutomorphicForm.unipotentGL2_zero, mul_one]

private theorem _root_.AutomorphicForm.TwistedBruhat.centralScalar_mul_comm {L : Type} [Field L] [NumberField L] (z : (AdeleRing (𝓞 L) L)ˣ)
    (h : AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.centralScalar (𝓞 L) L z * h = h * AutomorphicForm.centralScalar (𝓞 L) L z := by
  have hcoe : ((AutomorphicForm.centralScalar (𝓞 L) L z : AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) := rfl
  ext i j
  have hc := (Matrix.scalar_commute (z : AdeleRing (𝓞 L) L) (fun r => Commute.all _ r)
    ((h : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq
  rw [Units.val_mul, Units.val_mul, hcoe, hc]

p2m_export "AutomorphicForm.TwistedBruhat" "centralScalar_mul_comm"
private theorem sigmaAdelicAct_globalPoints_mul {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) L)
    (w : AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.globalPoints (𝓞 L) L γ * w) =
      AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ) *
        AutomorphicForm.sigmaAdelicAct K L D σ w := by
  rw [map_mul]
  congr 1
  exact AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ γ

private theorem globalPoints_unipotentGL2 {L : Type} [Field L] [NumberField L] (k : L) :
    AutomorphicForm.globalPoints (𝓞 L) L (AutomorphicForm.unipotentGL2 k) =
      AutomorphicForm.unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) k) := by
  ext i j
  rw [AutomorphicForm.globalPoints_apply, AutomorphicForm.unipotentGL2_coe, AutomorphicForm.unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem unipotentGL2_mul_globalPoints_of_borel {L : Type} [Field L] [NumberField L] {b : GL (Fin 2) L}
    (hb : b ∈ AutomorphicForm.borelSubgroup L) (t : AdeleRing (𝓞 L) L) :
    AutomorphicForm.unipotentGL2 t * AutomorphicForm.globalPoints (𝓞 L) L b =
      AutomorphicForm.globalPoints (𝓞 L) L b *
        AutomorphicForm.unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L)
          ((b : Matrix (Fin 2) (Fin 2) L) 1 1 / (b : Matrix (Fin 2) (Fin 2) L) 0 0) * t) := by
  have hb10 : (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := hb
  have ha : (b : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := borel_apply_zero_zero_ne_zero hb
  have hmul : (b : Matrix (Fin 2) (Fin 2) L) 0 0 *
      ((b : Matrix (Fin 2) (Fin 2) L) 1 1 / (b : Matrix (Fin 2) (Fin 2) L) 0 0) = (b : Matrix (Fin 2) (Fin 2) L) 1 1 :=
    mul_div_cancel₀ _ ha
  have hα : algebraMap L (AdeleRing (𝓞 L) L) ((b : Matrix (Fin 2) (Fin 2) L) 0 0) *
      algebraMap L (AdeleRing (𝓞 L) L) ((b : Matrix (Fin 2) (Fin 2) L) 1 1 / (b : Matrix (Fin 2) (Fin 2) L) 0 0) =
        algebraMap L (AdeleRing (𝓞 L) L) ((b : Matrix (Fin 2) (Fin 2) L) 1 1) := by
    rw [← map_mul, hmul]
  ext i j
  rw [Units.val_mul, Units.val_mul, AutomorphicForm.unipotentGL2_coe, AutomorphicForm.unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, AutomorphicForm.globalPoints_apply, hb10]
  linear_combination (-t) * hα

private noncomputable def borelSum (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (g : AdelicGL2 (𝓞 L) L)
    (y : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∑ᶠ δ ∈ borelNormOneSet K L,
    φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)

private theorem borelSum_globalPoints_borel_mul {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    {b : GL (Fin 2) L} (hb : b ∈ AutomorphicForm.borelSubgroup L) (g w : AdelicGL2 (𝓞 L) L) :
    borelSum K L D σ φ (AutomorphicForm.globalPoints (𝓞 L) L b * g) (AutomorphicForm.globalPoints (𝓞 L) L b * w) =
      borelSum K L D σ φ g w := by
  unfold borelSum
  rw [show (∑ᶠ δ ∈ borelNormOneSet K L,
        φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ w)) =
      ∑ᶠ δ ∈ borelNormOneSet K L,
        φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L (b⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) *
          AutomorphicForm.sigmaAdelicAct K L D σ w) from
    (finsum_mem_twistedConj σ (borelNormOneSet K L) (fun b hb δ hδ => twistedConj_mem_borelNormOne σ hb hδ) hb _).symm]
  refine finsum_mem_congr rfl fun δ _ => ?_
  rw [sigmaAdelicAct_globalPoints_mul, map_mul, map_mul, map_inv, mul_inv_rev]
  congr 1
  group

private theorem borelSum_globalPoints_unipotent_mul {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (g : AdelicGL2 (𝓞 L) L) (k : L) (w : AdelicGL2 (𝓞 L) L) :
    borelSum K L D σ φ g (AutomorphicForm.globalPoints (𝓞 L) L (AutomorphicForm.unipotentGL2 k) * w) =
      borelSum K L D σ φ g w := by
  unfold borelSum
  rw [show (∑ᶠ δ ∈ borelNormOneSet K L,
        φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ w)) =
      ∑ᶠ δ ∈ borelNormOneSet K L,
        φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L (δ * AutomorphicForm.unipotentGL2 ((σ : L →+* L) k)) *
          AutomorphicForm.sigmaAdelicAct K L D σ w) from
    (finsum_mem_borelNormOne_mul_unipotentGL2 (K := K) ((σ : L →+* L) k) _).symm]
  refine finsum_mem_congr rfl fun δ _ => ?_
  rw [sigmaAdelicAct_globalPoints_mul, generalLinearGroup_map_unipotentGL2, map_mul]
  congr 1
  group

end Invariance

private theorem cuspKernel_globalPoints_mul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (b : GL (Fin 2) L) (hb : b ∈ AutomorphicForm.borelSubgroup L) (g : AdelicGL2 (𝓞 L) L) :
    cuspKernel K L D σ hgen φ z (AutomorphicForm.globalPoints (𝓞 L) L b * g) = cuspKernel K L D σ hgen φ z g := by
  have hcomm : AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.globalPoints (𝓞 L) L b * g) =
      AutomorphicForm.globalPoints (𝓞 L) L b * (AutomorphicForm.centralScalar (𝓞 L) L z * g) := by
    rw [← mul_assoc, centralScalar_mul_comm, mul_assoc]
  unfold cuspKernel
  rw [show (∑ᶠ β ∈ normUnipotentSet K L σ hgen ∩ (AutomorphicForm.borelSubgroup L : Set (GL (Fin 2) L)),
        φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L β *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * g))) =
      ∑ᶠ β ∈ normUnipotentSet K L σ hgen ∩ (AutomorphicForm.borelSubgroup L : Set (GL (Fin 2) L)),
        φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L (b⁻¹ * β * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * g)) from
    (finsum_mem_twistedConj σ _ (fun b hb δ hδ => twistedConj_mem_normUnipotent_inter_borel σ hgen hb hδ) hb _).symm]
  refine finsum_mem_congr rfl fun β _ => ?_
  rw [hcomm, sigmaAdelicAct_globalPoints_mul]
  simp only [map_mul, map_inv, mul_inv_rev]
  congr 1
  group

private theorem cuspTruncation_globalPoints_mul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L) (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) (b : GL (Fin 2) L)
    (hb : b ∈ AutomorphicForm.borelSubgroup L) (g : AdelicGL2 (𝓞 L) L) :
    cuspTruncation K L D σ R φ z (AutomorphicForm.globalPoints (𝓞 L) L b * g) =
      cuspTruncation K L D σ R φ z g := by
  have hb10 : (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := hb
  have hcomm : AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.globalPoints (𝓞 L) L b * g) =
      AutomorphicForm.globalPoints (𝓞 L) L b * (AutomorphicForm.centralScalar (𝓞 L) L z * g) := by
    rw [← mul_assoc, centralScalar_mul_comm, mul_assoc]
  have hheight : NumberField.AdelicHeight.adelicHeight L
        (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.globalPoints (𝓞 L) L b * g)) =
      NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.centralScalar (𝓞 L) L z * g) := by
    rw [hcomm, NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero L b hb10]
  have hmem : AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.globalPoints (𝓞 L) L b * g) ∈
        AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R) ↔
      AutomorphicForm.centralScalar (𝓞 L) L z * g ∈
        AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R) := by
    rw [AutomorphicForm.mem_highSet_iff, AutomorphicForm.mem_highSet_iff, hheight]

  have ha' : (b : Matrix (Fin 2) (Fin 2) L) 1 1 / (b : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 :=
    div_ne_zero (borel_apply_one_one_ne_zero hb) (borel_apply_zero_zero_ne_zero hb)
  set F : AdeleRing (𝓞 L) L → ℂ := fun s =>
    borelSum K L D σ φ g (AutomorphicForm.unipotentGL2 s * (AutomorphicForm.centralScalar (𝓞 L) L z * g)) with hF_def
  have hper : ∀ (k : L) (s : AdeleRing (𝓞 L) L), F (algebraMap L (AdeleRing (𝓞 L) L) k + s) = F s := by
    intro k s
    simp only [hF_def]
    rw [AutomorphicForm.unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, borelSum_globalPoints_unipotent_mul]
  have hpt : ∀ t : AdeleRing (𝓞 L) L,
      borelSum K L D σ φ (AutomorphicForm.globalPoints (𝓞 L) L b * g)
          (AutomorphicForm.unipotentGL2 t *
            (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.globalPoints (𝓞 L) L b * g))) =
        F (algebraMap L (AdeleRing (𝓞 L) L)
          ((b : Matrix (Fin 2) (Fin 2) L) 1 1 / (b : Matrix (Fin 2) (Fin 2) L) 0 0) * t) := by
    intro t
    have harg : AutomorphicForm.unipotentGL2 t *
          (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.globalPoints (𝓞 L) L b * g)) =
        AutomorphicForm.globalPoints (𝓞 L) L b *
          (AutomorphicForm.unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L)
              ((b : Matrix (Fin 2) (Fin 2) L) 1 1 / (b : Matrix (Fin 2) (Fin 2) L) 0 0) * t) *
            (AutomorphicForm.centralScalar (𝓞 L) L z * g)) := by
      rw [hcomm, ← mul_assoc, unipotentGL2_mul_globalPoints_of_borel hb, mul_assoc]
    simp only [hF_def]
    rw [harg, borelSum_globalPoints_borel_mul D σ φ hb]
  have hCT : (@AutomorphicForm.constantTerm _
        (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) _ _
        (@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 L) L)
          (adelicAddHaar (𝓞 L) L) (adelicBox L))
        (fun t => AutomorphicForm.unipotentGL2 t) (borelSum K L D σ φ (AutomorphicForm.globalPoints (𝓞 L) L b * g))
        (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.globalPoints (𝓞 L) L b * g))) =
      @AutomorphicForm.constantTerm _
        (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) _ _
        (@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 L) L)
          (adelicAddHaar (𝓞 L) L) (adelicBox L))
        (fun t => AutomorphicForm.unipotentGL2 t) (borelSum K L D σ φ g)
        (AutomorphicForm.centralScalar (𝓞 L) L z * g) := by
    unfold AutomorphicForm.constantTerm AutomorphicForm.constantTermIntegrand
    simp only [hpt]
    exact NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap L hper _ ha'
  unfold cuspTruncation
  by_cases hhigh : AutomorphicForm.centralScalar (𝓞 L) L z * g ∈
      AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
  · rw [Set.indicator_of_mem (hmem.mpr hhigh), Set.indicator_of_mem hhigh]
    exact hCT
  · rw [Set.indicator_of_notMem (fun h => hhigh (hmem.mp h)), Set.indicator_of_notMem hhigh]

private theorem exists_forall_cuspTruncation_globalPoints_mul_eq_zero (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂) :
    ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R → ∀ x ∈ Φ₀, ∀ γ : GL (Fin 2) L, (γ : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0 →
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ),
        cuspTruncation K L D σ R φ z (AutomorphicForm.globalPoints (𝓞 L) L γ * x) = 0 := by
  obtain ⟨R₁, hR₁⟩ :=
    WindowedSiegel.exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet
      L c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S
  refine ⟨R₁, fun R hR x hx γ hγ φ z => ?_⟩
  unfold cuspTruncation
  apply Set.indicator_of_notMem
  rw [AutomorphicForm.mem_highSet_iff, not_lt, HeightShapeInvariance.adelicHeight_centralScalar_mul]
  have h1 := hR₁ x hx γ hγ
  have h2 := Real.add_one_le_exp R
  linarith

private theorem exists_forall_cuspTruncation_eq_finsum (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L) (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc)
    (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂) :
    ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R → ∀ reps : Set (GL (Fin 2) L), IsCuspTransversal L reps → ∀ x ∈ Φ₀,
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ),
        cuspTruncation K L D σ R φ z x =
          ∑ᶠ ρ ∈ reps, cuspTruncation K L D σ R φ z (AutomorphicForm.globalPoints (𝓞 L) L ρ * x) := by
  obtain ⟨R₁, hR₁⟩ :=
    exists_forall_cuspTruncation_globalPoints_mul_eq_zero K L D σ c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S
  refine ⟨R₁, fun R hR reps hreps x hx φ z => ?_⟩
  obtain ⟨ρ₀, ⟨hρ₀, hρ₀B⟩, huniq⟩ := hreps 1
  have hρ₀B' : ρ₀ ∈ AutomorphicForm.borelSubgroup L := by
    have h := hρ₀B
    rw [one_mul] at h
    simpa using (AutomorphicForm.borelSubgroup L).inv_mem h
  have hsub : reps ∩ Function.support
      (fun ρ : GL (Fin 2) L => cuspTruncation K L D σ R φ z (AutomorphicForm.globalPoints (𝓞 L) L ρ * x)) ⊆
        ↑({ρ₀} : Finset (GL (Fin 2) L)) := by
    rintro ρ ⟨hρ, hne⟩
    rw [Finset.coe_singleton, Set.mem_singleton_iff]
    by_contra hρρ₀
    apply hne
    apply hR₁ R hR x hx ρ _ φ z
    intro h10
    apply hρρ₀
    have hρB : 1 * ρ⁻¹ ∈ AutomorphicForm.borelSubgroup L := by
      rw [one_mul]
      exact (AutomorphicForm.borelSubgroup L).inv_mem h10
    exact huniq ρ ⟨hρ, hρB⟩
  rw [finsum_mem_eq_sum_of_subset _ hsub (by simpa using hρ₀), Finset.sum_singleton,
    cuspTruncation_globalPoints_mul K L D σ R φ z ρ₀ hρ₀B' x]

#print axioms exists_isCuspTransversal
#print axioms exists_forall_cuspTruncation_globalPoints_mul_eq_zero
#print axioms exists_forall_cuspTruncation_eq_finsum

#print axioms cuspKernel_globalPoints_mul
#print axioms cuspTruncation_globalPoints_mul

#print axioms existsUnique_mem_mul_mul_inv_mem_borelSubgroup
#print axioms finsum_normUnipotent_eq_finsum_cuspKernel
#print axioms cuspTruncation_apply

end AutomorphicForm.TwistedBruhat

end TwistedBruhatProofs

section UnfoldingProof

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm P2MW.S_UnipotentTermUnfolding_exists_forall_setIntegral_unipotentTerm_eq_mul_integral_iwasawa.AutomorphicForm"
open scoped ENNReal

noncomputable section

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm P2MW.S_UnipotentTermUnfolding_exists_forall_setIntegral_unipotentTerm_eq_mul_integral_iwasawa.AutomorphicForm Matrix"
open scoped ENNReal NNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

namespace BorelWord

section Generic

variable {L : Type*} [Field L] {A : Type*} [CommRing A]

private theorem coe_scalar (ζ : Aˣ) :
    ((GeneralLinearGroup.scalar (Fin 2) ζ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      Matrix.scalar (Fin 2) (ζ : A) := rfl

private theorem _root_.BorelWord.coe_map (ι : L →+* A) (γ : GL (Fin 2) L) :
    ((GeneralLinearGroup.map ι γ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      (γ : Matrix (Fin 2) (Fin 2) L).map ι := rfl

p2m_export "BorelWord" "coe_map"
private theorem coe_unipotentGL2 (x : A) :
    ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![1, x; 0, 1] := rfl

private theorem coe_diagOne (t : Aˣ) :
    ((diagOne t : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = Matrix.diagonal ![(t : A), 1] := rfl

private theorem map_mul_word (ι : L →+* A) (γ : GL (Fin 2) L)
    (h10 : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) {α β : L}
    (h00 : (γ : Matrix (Fin 2) (Fin 2) L) 0 0 = (γ : Matrix (Fin 2) (Fin 2) L) 1 1 * α)
    (h01 : (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = (γ : Matrix (Fin 2) (Fin 2) L) 1 1 * β)
    (d αU : Lˣ) (hd : (d : L) = (γ : Matrix (Fin 2) (Fin 2) L) 1 1) (hα : (αU : L) = α)
    (x : A) (ζ t : Aˣ) :
    GeneralLinearGroup.map ι γ * (unipotentGL2 x * GeneralLinearGroup.scalar (Fin 2) ζ * diagOne t) =
      unipotentGL2 (ι β + ι α * x) * GeneralLinearGroup.scalar (Fin 2) (Units.map ι.toMonoidHom d * ζ)
        * diagOne (Units.map ι.toMonoidHom αU * t) := by
  refine GeneralLinearGroup.ext fun i j => ?_
  simp only [GeneralLinearGroup.coe_mul, coe_map, coe_scalar, coe_unipotentGL2, coe_diagOne]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.vecMul_diagonal, h10, h00, h01, hd, hα,
      map_mul] <;>
    ring

end Generic

section Adelic

variable (L : Type) [Field L] [NumberField L]

private theorem globalPoints_mul_word (γ : GL (Fin 2) L) (h10 : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) {α β : L}
    (h00 : (γ : Matrix (Fin 2) (Fin 2) L) 0 0 = (γ : Matrix (Fin 2) (Fin 2) L) 1 1 * α)
    (h01 : (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = (γ : Matrix (Fin 2) (Fin 2) L) 1 1 * β)
    (d αU : Lˣ) (hd : (d : L) = (γ : Matrix (Fin 2) (Fin 2) L) 1 1) (hα : (αU : L) = α)
    (x : AdeleRing (𝓞 L) L) (ζ t : (AdeleRing (𝓞 L) L)ˣ) :
    globalPoints (𝓞 L) L γ * (unipotentGL2 x * centralScalar (𝓞 L) L ζ * diagOne t) =
      unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) β + algebraMap L (AdeleRing (𝓞 L) L) α * x) *
        centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom d * ζ) *
        diagOne (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom αU * t) :=
  map_mul_word (algebraMap L (AdeleRing (𝓞 L) L)) γ h10 h00 h01 d αU hd hα x ζ t

end Adelic

section Action

variable (L : Type) [Field L] [NumberField L]

private abbrev Coord : Type :=
  AdeleRing (𝓞 L) L ×
    ((AdeleRing (𝓞 L) L)ˣ × ((AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L)))

variable {L}

private def ent (γ : borelSubgroup L) (i j : Fin 2) : L := ((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j

omit [NumberField L] in
private theorem ent_one_zero (γ : borelSubgroup L) : ent γ 1 0 = 0 := γ.2

omit [NumberField L] in
private theorem ent_one (i j : Fin 2) : ent (1 : borelSubgroup L) i j = (1 : Matrix (Fin 2) (Fin 2) L) i j := rfl

omit [NumberField L] in
private theorem ent_mul_zero_zero (γ γ' : borelSubgroup L) : ent (γ * γ') 0 0 = ent γ 0 0 * ent γ' 0 0 := by
  have h := ent_one_zero γ'
  unfold ent at h ⊢
  simp only [Subgroup.coe_mul, GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h,
    mul_zero, add_zero]

omit [NumberField L] in
private theorem ent_mul_zero_one (γ γ' : borelSubgroup L) :
    ent (γ * γ') 0 1 = ent γ 0 0 * ent γ' 0 1 + ent γ 0 1 * ent γ' 1 1 := by
  unfold ent
  simp only [Subgroup.coe_mul, GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

omit [NumberField L] in
private theorem ent_mul_one_one (γ γ' : borelSubgroup L) : ent (γ * γ') 1 1 = ent γ 1 1 * ent γ' 1 1 := by
  have h := ent_one_zero γ
  unfold ent at h ⊢
  simp only [Subgroup.coe_mul, GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h,
    zero_mul, zero_add]

omit [NumberField L] in
private theorem det_ne_zero (γ : borelSubgroup L) : ent γ 0 0 * ent γ 1 1 ≠ 0 := by
  have h := ent_one_zero γ
  have hdet := (Matrix.isUnits_det_units (γ : GL (Fin 2) L)).ne_zero
  unfold ent at h ⊢
  rwa [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet

omit [NumberField L] in
private theorem ent_zero_zero_ne_zero (γ : borelSubgroup L) : ent γ 0 0 ≠ 0 := left_ne_zero_of_mul (det_ne_zero γ)

omit [NumberField L] in
private theorem ent_one_one_ne_zero (γ : borelSubgroup L) : ent γ 1 1 ≠ 0 := right_ne_zero_of_mul (det_ne_zero γ)

variable (L)

private noncomputable def dChar : borelSubgroup L →* Lˣ where
  toFun γ := Units.mk0 (ent γ 1 1) (ent_one_one_ne_zero γ)
  map_one' := Units.ext (by simp [ent_one])
  map_mul' γ γ' := Units.ext (by simp [ent_mul_one_one])

private noncomputable def aChar : borelSubgroup L →* Lˣ where
  toFun γ := Units.mk0 (ent γ 0 0) (ent_zero_zero_ne_zero γ)
  map_one' := Units.ext (by simp [ent_one])
  map_mul' γ γ' := Units.ext (by simp [ent_mul_zero_zero])

private noncomputable def αChar : borelSubgroup L →* Lˣ := aChar L * (dChar L)⁻¹

variable {L}

omit [NumberField L] in
private theorem coe_dChar (γ : borelSubgroup L) : ((dChar L γ : Lˣ) : L) = ent γ 1 1 := rfl

omit [NumberField L] in
private theorem coe_aChar (γ : borelSubgroup L) : ((aChar L γ : Lˣ) : L) = ent γ 0 0 := rfl

omit [NumberField L] in
private theorem coe_αChar (γ : borelSubgroup L) : ((αChar L γ : Lˣ) : L) = ent γ 0 0 / ent γ 1 1 := by
  simp [αChar, coe_aChar, coe_dChar, div_eq_mul_inv]

private noncomputable def βFun (γ : borelSubgroup L) : L := ent γ 0 1 / ent γ 1 1

omit [NumberField L] in
private theorem βFun_one : βFun (1 : borelSubgroup L) = 0 := by
  simp [βFun, ent_one]

omit [NumberField L] in
private theorem βFun_mul (γ γ' : borelSubgroup L) :
    βFun (γ * γ') = ((αChar L γ : Lˣ) : L) * βFun γ' + βFun γ := by
  rw [βFun, βFun, βFun, coe_αChar, ent_mul_zero_one, ent_mul_one_one]
  field_simp [ent_one_one_ne_zero γ, ent_one_one_ne_zero γ']

omit [NumberField L] in
private theorem ent_zero_zero_eq (γ : borelSubgroup L) : ent γ 0 0 = ent γ 1 1 * ((αChar L γ : Lˣ) : L) := by
  rw [coe_αChar, mul_div_cancel₀ _ (ent_one_one_ne_zero γ)]

omit [NumberField L] in
private theorem ent_zero_one_eq (γ : borelSubgroup L) : ent γ 0 1 = ent γ 1 1 * βFun γ := by
  rw [βFun, mul_div_cancel₀ _ (ent_one_one_ne_zero γ)]

variable (L)

private noncomputable scoped instance : SMul (borelSubgroup L) (Coord L) where
  smul γ p :=
    (algebraMap L (AdeleRing (𝓞 L) L) (βFun γ) +
        algebraMap L (AdeleRing (𝓞 L) L) ((αChar L γ : Lˣ) : L) * p.1,
      Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom (dChar L γ) * p.2.1,
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom (αChar L γ) * p.2.2.1, p.2.2.2))

variable {L}

private theorem _root_.BorelWord.smul_def (γ : borelSubgroup L) (p : Coord L) :
    γ • p =
      (algebraMap L (AdeleRing (𝓞 L) L) (βFun γ) +
          algebraMap L (AdeleRing (𝓞 L) L) ((αChar L γ : Lˣ) : L) * p.1,
        Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom (dChar L γ) * p.2.1,
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom (αChar L γ) * p.2.2.1, p.2.2.2)) := rfl

p2m_export "BorelWord" "smul_def"
variable (L)

private noncomputable scoped instance : MulAction (borelSubgroup L) (Coord L) where
  one_smul p := by
    obtain ⟨x, ζ, t, k⟩ := p
    simp [smul_def, βFun_one]
  mul_smul γ γ' p := by
    obtain ⟨x, ζ, t, k⟩ := p
    simp only [smul_def, βFun_mul, map_mul, map_add, Units.val_mul, mul_assoc, Prod.mk.injEq, and_true]
    ring

variable {L}

private theorem globalPoints_mul_word_eq_word_smul (γ : borelSubgroup L) (p : Coord L) :
    globalPoints (𝓞 L) L (γ : GL (Fin 2) L) *
        (unipotentGL2 p.1 * centralScalar (𝓞 L) L p.2.1 * diagOne p.2.2.1 *
          (p.2.2.2 : AdelicGL2 (𝓞 L) L)) =
      unipotentGL2 (γ • p).1 * centralScalar (𝓞 L) L (γ • p).2.1 * diagOne (γ • p).2.2.1 *
        ((γ • p).2.2.2 : AdelicGL2 (𝓞 L) L) := by
  simp only [smul_def]
  rw [← mul_assoc (globalPoints (𝓞 L) L _)]
  congr 1
  exact globalPoints_mul_word L (γ : GL (Fin 2) L) (ent_one_zero γ) (ent_zero_zero_eq γ)
    (ent_zero_one_eq γ) (dChar L γ) (αChar L γ) (coe_dChar γ) rfl p.1 p.2.1 p.2.2.1

end Action

section Domain

variable (L : Type) [Field L] [NumberField L]

local notation "𝔸" => AdeleRing (𝓞 L) L

private noncomputable abbrev principalUnit : Lˣ →* (𝔸)ˣ := Units.map (algebraMap L 𝔸).toMonoidHom

private abbrev principalRange : Subgroup (𝔸)ˣ := (Units.map (algebraMap L 𝔸 : L →* 𝔸)).range

private noncomputable def modulusDensity (t : (𝔸)ˣ) : ℝ≥0 := Real.toNNReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)

private noncomputable def torusMeasure : Measure (𝔸)ˣ :=
  (NumberField.Idele.idelicHaar L).withDensity fun t => ((modulusDensity L t : ℝ≥0) : ℝ≥0∞)

variable {L} in

private scoped instance [SigmaFinite (NumberField.Idele.idelicHaar L)] : SFinite (torusMeasure L) := by
  unfold torusMeasure; infer_instance

private noncomputable def iwasawaMeasure : Measure (Coord L) :=
  (adelicAddHaar (𝓞 L) L).prod
    ((NumberField.Idele.idelicHaar L).prod ((torusMeasure L).prod (maximalCompactHaar L)))

private noncomputable def mkBorel (a d : Lˣ) (b : L) : borelSubgroup L :=
  ⟨GeneralLinearGroup.mkOfDetNeZero !![(a : L), b; 0, (d : L)]
      (by rw [Matrix.det_fin_two_of]; simp),
    by
      show (!![(a : L), b; 0, (d : L)] : Matrix (Fin 2) (Fin 2) L) 1 0 = 0
      simp⟩

omit [NumberField L] in
private theorem ent_mkBorel_zero_zero (a d : Lˣ) (b : L) : ent (mkBorel L a d b) 0 0 = a := by
  simp [ent, mkBorel, GeneralLinearGroup.mkOfDetNeZero]

omit [NumberField L] in
private theorem ent_mkBorel_zero_one (a d : Lˣ) (b : L) : ent (mkBorel L a d b) 0 1 = b := by
  simp [ent, mkBorel, GeneralLinearGroup.mkOfDetNeZero]

omit [NumberField L] in
private theorem ent_mkBorel_one_one (a d : Lˣ) (b : L) : ent (mkBorel L a d b) 1 1 = d := by
  simp [ent, mkBorel, GeneralLinearGroup.mkOfDetNeZero]

omit [NumberField L] in
private theorem dChar_mkBorel (a d : Lˣ) (b : L) : dChar L (mkBorel L a d b) = d :=
  Units.ext (by rw [coe_dChar, ent_mkBorel_one_one])

omit [NumberField L] in
private theorem αChar_mkBorel (c d : Lˣ) (b : L) : αChar L (mkBorel L (c * d) d b) = c := by
  refine Units.ext ?_
  rw [coe_αChar, ent_mkBorel_zero_zero, ent_mkBorel_one_one, Units.val_mul]
  exact mul_div_cancel_right₀ _ d.ne_zero

omit [NumberField L] in
private theorem βFun_mkBorel (a d : Lˣ) (l : L) : βFun (mkBorel L a d (l * d)) = l := by
  rw [βFun, ent_mkBorel_zero_one, ent_mkBorel_one_one]
  exact mul_div_cancel_right₀ _ d.ne_zero

omit [NumberField L] in

private theorem eq_one_of_chars (γ : borelSubgroup L) (hd : dChar L γ = 1) (hα : αChar L γ = 1) (hβ : βFun γ = 0) :
    γ = 1 := by
  have h11 : ent γ 1 1 = 1 := by rw [← coe_dChar, hd, Units.val_one]
  have h00 : ent γ 0 0 = 1 := by rw [ent_zero_zero_eq, hα, Units.val_one, h11, one_mul]
  have h01 : ent γ 0 1 = 0 := by rw [ent_zero_one_eq, hβ, mul_zero]
  have h10 := ent_one_zero γ
  apply Subtype.ext
  refine GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Measures

variable (hmod : Measurable (modulusDensity L))
  (hn : ∀ c : Lˣ, NumberField.TateGlobal.ideleNorm L (principalUnit L c) = 1)
  (hscale : ∀ c : Lˣ,
    MeasurePreserving (fun x : AdeleRing (𝓞 L) L => algebraMap L (AdeleRing (𝓞 L) L) (c : L) * x)
      (adelicAddHaar (𝓞 L) L) (adelicAddHaar (𝓞 L) L))

include hn in
private theorem modulusDensity_unit_mul (c : Lˣ) (t : (𝔸)ˣ) :
    modulusDensity L (principalUnit L c * t) = modulusDensity L t := by
  rw [modulusDensity, modulusDensity, NumberField.TateGlobal.ideleNorm_mul, hn c, one_mul]

include hmod hn in
private theorem measurePreserving_unit_mul_torusMeasure (c : Lˣ) :
    MeasurePreserving (fun t : (𝔸)ˣ => principalUnit L c * t) (torusMeasure L) (torusMeasure L) := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar L
  have hc : MeasurePreserving (fun t : (𝔸)ˣ => principalUnit L c * t) (NumberField.Idele.idelicHaar L)
      (NumberField.Idele.idelicHaar L) := measurePreserving_mul_left _ _
  refine ⟨hc.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hc.measurable hs, torusMeasure, withDensity_apply _ (hc.measurable hs), withDensity_apply _ hs]
  exact (setLIntegral_congr_fun (hc.measurable hs) fun t _ =>
      congrArg ENNReal.ofNNReal (modulusDensity_unit_mul L hn c t).symm).trans
    (hc.setLIntegral_comp_preimage hs (f := fun t => ((modulusDensity L t : ℝ≥0) : ℝ≥0∞))
      (measurable_coe_nnreal_ennreal.comp hmod))

include hscale in
private theorem measurePreserving_affine (γ : borelSubgroup L) :
    MeasurePreserving
      (fun x : 𝔸 => algebraMap L 𝔸 (βFun γ) + algebraMap L 𝔸 ((αChar L γ : Lˣ) : L) * x)
      (adelicAddHaar (𝓞 L) L) (adelicAddHaar (𝓞 L) L) :=
  (measurePreserving_add_left (adelicAddHaar (𝓞 L) L) (algebraMap L 𝔸 (βFun γ))).comp (hscale (αChar L γ))

include hmod hn hscale in

private theorem measurePreserving_smul [SigmaFinite (NumberField.Idele.idelicHaar L)] (γ : borelSubgroup L) :
    MeasurePreserving (fun p : Coord L => γ • p) (iwasawaMeasure L) (iwasawaMeasure L) := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar L
  haveI : SFinite (torusMeasure L) := by unfold torusMeasure; infer_instance
  have hζ : MeasurePreserving (fun ζ : (𝔸)ˣ => principalUnit L (dChar L γ) * ζ) (NumberField.Idele.idelicHaar L)
      (NumberField.Idele.idelicHaar L) := measurePreserving_mul_left _ _
  have h := (measurePreserving_affine L hscale γ).prod
    (hζ.prod ((measurePreserving_unit_mul_torusMeasure L hmod hn (αChar L γ)).prod
      (MeasurePreserving.id (maximalCompactHaar L))))
  have hfun : (fun p : Coord L => γ • p) =
      Prod.map (fun x : 𝔸 => algebraMap L 𝔸 (βFun γ) + algebraMap L 𝔸 ((αChar L γ : Lˣ) : L) * x)
        (Prod.map (fun ζ : (𝔸)ˣ => principalUnit L (dChar L γ) * ζ)
          (Prod.map (fun t : (𝔸)ˣ => principalUnit L (αChar L γ) * t) id)) :=
    funext fun p => rfl
  rw [hfun, iwasawaMeasure]
  exact h

private theorem iwasawaMeasure_cyl_x_null [SigmaFinite (NumberField.Idele.idelicHaar L)]
    {N : Set 𝔸} (hN : adelicAddHaar (𝓞 L) L N = 0) :
    iwasawaMeasure L (N ×ˢ (Set.univ : Set ((𝔸)ˣ × ((𝔸)ˣ × ↥(adelicMaximalCompact L))))) = 0 := by
  rw [iwasawaMeasure, Measure.prod_prod, hN, zero_mul]

private theorem iwasawaMeasure_cyl_ζ_null [SigmaFinite (NumberField.Idele.idelicHaar L)]
    {N : Set (𝔸)ˣ} (hN : NumberField.Idele.idelicHaar L N = 0) :
    iwasawaMeasure L (Set.univ ×ˢ (N ×ˢ (Set.univ : Set ((𝔸)ˣ × ↥(adelicMaximalCompact L))))) = 0 := by
  rw [iwasawaMeasure, Measure.prod_prod, Measure.prod_prod, hN, zero_mul, mul_zero]

private theorem iwasawaMeasure_cyl_t_null [SigmaFinite (NumberField.Idele.idelicHaar L)]
    {N : Set (𝔸)ˣ} (hN : NumberField.Idele.idelicHaar L N = 0) :
    iwasawaMeasure L (Set.univ ×ˢ (Set.univ ×ˢ (N ×ˢ (Set.univ : Set ↥(adelicMaximalCompact L))))) = 0 := by
  have hN' : torusMeasure L N = 0 := withDensity_absolutelyContinuous _ _ hN
  rw [iwasawaMeasure, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, hN', zero_mul, mul_zero,
    mul_zero]

variable {X : Set (AdeleRing (𝓞 L) L)}
  (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
  {Ω₁ Ω₂ : Set (AdeleRing (𝓞 L) L)ˣ} (hΩ₁ : IsFundamentalDomain (principalRange L) Ω₁ (NumberField.Idele.idelicHaar L))
  (hΩ₂ : IsFundamentalDomain (principalRange L) Ω₂ (NumberField.Idele.idelicHaar L))

private def productDomain : Set (Coord L) := X ×ˢ (Ω₁ ×ˢ (Ω₂ ×ˢ (Set.univ : Set ↥(adelicMaximalCompact L))))

private theorem mem_productDomain {p : Coord L} :
    p ∈ productDomain L (X := X) (Ω₁ := Ω₁) (Ω₂ := Ω₂) ↔ p.1 ∈ X ∧ p.2.1 ∈ Ω₁ ∧ p.2.2.1 ∈ Ω₂ := by
  simp [productDomain]

private theorem exists_eq_principalUnit (g : principalRange L) : ∃ c : Lˣ, principalUnit L c = (g : (𝔸)ˣ) := g.2

private theorem principalUnit_injective : Function.Injective (principalUnit L) :=
  Units.map_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 L) L)

private noncomputable def toRange (c : Lˣ) : principalRange L := ⟨principalUnit L c, c, rfl⟩

private theorem toRange_ne_one {c : Lˣ} (hc : c ≠ 1) : toRange L c ≠ 1 := by
  intro h
  apply hc
  apply principalUnit_injective L
  have := congrArg Subtype.val h
  simpa [toRange] using this

private noncomputable def toPrincipal (l : L) : AdeleRing.principalSubgroup (𝓞 L) L := ⟨algebraMap L 𝔸 l, l, rfl⟩

private theorem toPrincipal_ne_zero {l : L} (hl : l ≠ 0) : toPrincipal L l ≠ 0 := by
  intro h
  apply hl
  have := congrArg Subtype.val h
  have h0 : algebraMap L 𝔸 l = 0 := by simpa [toPrincipal] using this
  exact NumberField.AdeleRing.algebraMap_injective (𝓞 L) L (h0.trans (map_zero (algebraMap L 𝔸)).symm)

include hmod hn hscale hX hΩ₁ hΩ₂ in

private theorem isFundamentalDomain_productDomain [SigmaFinite (NumberField.Idele.idelicHaar L)] :
    IsFundamentalDomain (borelSubgroup L) (productDomain L (X := X) (Ω₁ := Ω₁) (Ω₂ := Ω₂))
      (iwasawaMeasure L) := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar L
  haveI : Countable L := (Module.finBasis ℚ L).equivFun.toEquiv.injective.countable
  haveI : Countable Lˣ := Units.val_injective.countable
  refine IsFundamentalDomain.mk'' ?_ ?_ ?_ fun γ =>
    (measurePreserving_smul L hmod hn hscale γ).quasiMeasurePreserving
  ·
    unfold productDomain iwasawaMeasure
    exact hX.nullMeasurableSet.prod (hΩ₁.nullMeasurableSet.prod
      ((hΩ₂.nullMeasurableSet.mono_ac (withDensity_absolutelyContinuous _ _)).prod
        MeasurableSet.univ.nullMeasurableSet))
  ·
    rw [ae_iff]
    set badX : Set 𝔸 := {y | ¬ ∃ g : AdeleRing.principalSubgroup (𝓞 L) L, g +ᵥ y ∈ X} with hbadX
    have hbadX0 : adelicAddHaar (𝓞 L) L badX = 0 := ae_iff.mp hX.ae_covers
    set bad₃ : Set 𝔸 := ⋃ c : Lˣ, (fun x : 𝔸 => algebraMap L 𝔸 (c : L) * x) ⁻¹' badX with hbad₃
    have hbad₃0 : adelicAddHaar (𝓞 L) L bad₃ = 0 :=
      measure_iUnion_null fun c => by
        rw [(hscale c).measure_preimage (NullMeasurableSet.of_null hbadX0)]
        exact hbadX0
    have h₁ : NumberField.Idele.idelicHaar L {ζ | ¬ ∃ g : principalRange L, g • ζ ∈ Ω₁} = 0 :=
      ae_iff.mp hΩ₁.ae_covers
    have h₂ : NumberField.Idele.idelicHaar L {t | ¬ ∃ g : principalRange L, g • t ∈ Ω₂} = 0 :=
      ae_iff.mp hΩ₂.ae_covers
    refine measure_mono_null ?_ (measure_union_null (measure_union_null
      (iwasawaMeasure_cyl_x_null L hbad₃0) (iwasawaMeasure_cyl_ζ_null L h₁)) (iwasawaMeasure_cyl_t_null L h₂))
    rintro ⟨x, ζ, t, k⟩ hp
    by_contra hnot
    apply hp
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and, not_or,
      Set.mem_setOf_eq, not_not] at hnot
    obtain ⟨⟨hx, g₁, hg₁⟩, g₂, hg₂⟩ := hnot
    obtain ⟨d, hd⟩ := exists_eq_principalUnit L g₁
    obtain ⟨c, hc⟩ := exists_eq_principalUnit L g₂
    have hxc : algebraMap L 𝔸 (c : L) * x ∉ badX := fun h => hx (Set.mem_iUnion.mpr ⟨c, h⟩)
    simp only [hbadX, Set.mem_setOf_eq, not_not] at hxc
    obtain ⟨g₃, hg₃⟩ := hxc
    obtain ⟨l, hl⟩ := g₃.2
    refine ⟨mkBorel L (c * d) d (l * d), ?_⟩
    rw [mem_productDomain, smul_def, βFun_mkBorel, αChar_mkBorel, dChar_mkBorel]
    refine ⟨?_, ?_, ?_⟩
    · have hg₃' : (g₃ : 𝔸) + algebraMap L 𝔸 (c : L) * x ∈ X := hg₃
      rwa [← hl] at hg₃'
    · have hg₁' : (g₁ : (𝔸)ˣ) * ζ ∈ Ω₁ := hg₁
      rwa [← hd] at hg₁'
    · have hg₂' : (g₂ : (𝔸)ˣ) * t ∈ Ω₂ := hg₂
      rwa [← hc] at hg₂'
  ·
    intro γ hγ
    show iwasawaMeasure L (γ • productDomain L (X := X) (Ω₁ := Ω₁) (Ω₂ := Ω₂) ∩
      productDomain L (X := X) (Ω₁ := Ω₁) (Ω₂ := Ω₂)) = 0
    by_cases hd : dChar L γ = 1
    · by_cases hα : αChar L γ = 1
      ·
        have hβ : βFun γ ≠ 0 := fun hβ => hγ (eq_one_of_chars L γ hd hα hβ)
        have hnull : adelicAddHaar (𝓞 L) L ((toPrincipal L (βFun γ) +ᵥ X) ∩ X) = 0 := by
          have h := hX.aedisjoint (toPrincipal_ne_zero L hβ)
          simpa only [Function.onFun, zero_vadd, AEDisjoint] using h
        refine measure_mono_null ?_ (iwasawaMeasure_cyl_x_null L hnull)
        rintro _ ⟨⟨q, hq, rfl⟩, hp⟩
        refine ⟨⟨⟨q.1, ((mem_productDomain L).mp hq).1, ?_⟩, ((mem_productDomain L).mp hp).1⟩, Set.mem_univ _⟩
        show algebraMap L 𝔸 (βFun γ) + q.1 = (γ • q).1
        rw [smul_def, hα, Units.val_one, map_one, one_mul]
      ·
        have hnull : NumberField.Idele.idelicHaar L ((toRange L (αChar L γ) • Ω₂) ∩ Ω₂) = 0 := by
          have h := hΩ₂.aedisjoint (toRange_ne_one L hα)
          simpa only [Function.onFun, one_smul, AEDisjoint] using h
        refine measure_mono_null ?_ (iwasawaMeasure_cyl_t_null L hnull)
        rintro _ ⟨⟨q, hq, rfl⟩, hp⟩
        refine ⟨Set.mem_univ _, Set.mem_univ _,
          ⟨⟨q.2.2.1, ((mem_productDomain L).mp hq).2.2, rfl⟩, ((mem_productDomain L).mp hp).2.2⟩,
          Set.mem_univ _⟩
    ·
      have hnull : NumberField.Idele.idelicHaar L ((toRange L (dChar L γ) • Ω₁) ∩ Ω₁) = 0 := by
        have h := hΩ₁.aedisjoint (toRange_ne_one L hd)
        simpa only [Function.onFun, one_smul, AEDisjoint] using h
      refine measure_mono_null ?_ (iwasawaMeasure_cyl_ζ_null L hnull)
      rintro _ ⟨⟨q, hq, rfl⟩, hp⟩
      exact ⟨Set.mem_univ _,
        ⟨⟨q.2.1, ((mem_productDomain L).mp hq).2.1, rfl⟩, ((mem_productDomain L).mp hp).2.1⟩,
        Set.mem_univ _⟩

end Measures

end Domain

section Unfolding

variable (L : Type) [Field L] [NumberField L]

local notation "𝔸" => AdeleRing (𝓞 L) L

attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

private def coordWord (p : Coord L) : AdelicGL2 (𝓞 L) L :=
  unipotentGL2 p.1 * centralScalar (𝓞 L) L p.2.1 * diagOne p.2.2.1 * (p.2.2.2 : AdelicGL2 (𝓞 L) L)

private theorem coordWord_smul (γ : borelSubgroup L) (p : Coord L) :
    coordWord L (γ • p) = globalPoints (𝓞 L) L (γ : GL (Fin 2) L) * coordWord L p :=
  (globalPoints_mul_word_eq_word_smul γ p).symm

private theorem measurable_modulusDensity : Measurable (modulusDensity L) := by
  show Measurable fun t : (𝔸)ˣ => Real.toNNReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)
  exact (NumberField.TateGlobal.continuous_ideleNorm L).measurable.inv.real_toNNReal

private theorem det_diagOne {A : Type*} [CommRing A] (s : Aˣ) : GeneralLinearGroup.det (diagOne s) = s := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, coe_diagOne, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem ideleNorm_principalUnit (c : Lˣ) :
    NumberField.TateGlobal.ideleNorm L (principalUnit L c) = 1 := by
  have hdet : GeneralLinearGroup.det (globalPoints (𝓞 L) L (diagOne c)) = principalUnit L c := by
    show GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap L 𝔸) (diagOne c)) = principalUnit L c
    rw [Matrix.GeneralLinearGroup.map_det, det_diagOne]
    exact Units.ext rfl
  have h := AutomorphicForm.ideleNorm_det_globalPoints (F := L) (diagOne c)
  rwa [hdet] at h

private theorem measurePreserving_mul_principal (c : Lˣ) :
    MeasurePreserving (fun x : AdeleRing (𝓞 L) L => algebraMap L (AdeleRing (𝓞 L) L) (c : L) * x)
      (adelicAddHaar (𝓞 L) L) (adelicAddHaar (𝓞 L) L) :=
  NumberField.AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar L (c : L) c.ne_zero

private theorem countable_gl : Countable (GL (Fin 2) L) := by
  haveI : Countable L := (Module.finBasis ℚ L).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Units.val_injective.countable

private theorem countable_borelSubgroup : Countable (borelSubgroup L) := by
  haveI := countable_gl L
  infer_instance

private theorem _root_.BorelWord.countable_range : Countable (globalPoints (𝓞 L) L).range := by
  haveI := countable_gl L
  exact (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 L) L)).countable

p2m_export "BorelWord" "countable_range"
private theorem secondCountableTopology_adeleRing : SecondCountableTopology 𝔸 :=
  NumberField.AdeleRing.secondCountableTopology L

private theorem secondCountableTopology_idele : SecondCountableTopology (𝔸)ˣ := by
  haveI := secondCountableTopology_adeleRing L
  haveI : SecondCountableTopology (𝔸)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

private theorem sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar L) := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar L
  haveI := secondCountableTopology_idele L
  infer_instance

private theorem globalPoints_injective : Function.Injective (globalPoints (𝓞 L) L) := by
  intro a b h
  refine Units.ext (Matrix.ext fun i j => NumberField.AdeleRing.algebraMap_injective (𝓞 L) L ?_)
  rw [← globalPoints_apply, ← globalPoints_apply, h]

private theorem continuous_diagOne : Continuous (diagOne : (𝔸)ˣ → AdelicGL2 (𝓞 L) L) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : (𝔸)ˣ => Matrix.diagonal ![(t : 𝔸), 1]
    exact (Units.continuous_val.matrixVecCons continuous_const).matrix_diagonal
  · show Continuous fun t : (𝔸)ˣ => Matrix.diagonal ![((t⁻¹ : (𝔸)ˣ) : 𝔸), 1]
    exact (Units.continuous_coe_inv.matrixVecCons continuous_const).matrix_diagonal

private theorem _root_.BorelWord.continuous_centralScalar :
    Continuous (centralScalar (𝓞 L) L : (𝔸)ˣ → AdelicGL2 (𝓞 L) L) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun u : (𝔸)ˣ => Matrix.diagonal fun _ : Fin 2 => (u : 𝔸)
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  · show Continuous fun u : (𝔸)ˣ => Matrix.diagonal fun _ : Fin 2 => ((u⁻¹ : (𝔸)ˣ) : 𝔸)
    exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal

p2m_export "BorelWord" "continuous_centralScalar"
private theorem continuous_coordWord : Continuous (coordWord L) := by
  show Continuous fun p : Coord L =>
    unipotentGL2 p.1 * centralScalar (𝓞 L) L p.2.1 * diagOne p.2.2.1 * (p.2.2.2 : AdelicGL2 (𝓞 L) L)
  exact ((((AutomorphicForm.continuous_unipotentGL2 (R := 𝔸)).comp continuous_fst).mul
    ((continuous_centralScalar L).comp continuous_snd.fst)).mul
    ((continuous_diagOne L).comp continuous_snd.snd.fst)).mul
    (continuous_subtype_val.comp continuous_snd.snd.snd)

private theorem measurable_coordWord : Measurable (coordWord L) := by
  haveI := secondCountableTopology_adeleRing L
  haveI := secondCountableTopology_idele L
  exact (continuous_coordWord L).measurable

private theorem lintegral_withDensity_modulusDensity (ν : Measure (𝔸)ˣ) (h : (𝔸)ˣ → ℝ≥0∞)
    (hh : Measurable h) :
    ∫⁻ t, h t ∂(ν.withDensity fun t => ((modulusDensity L t : ℝ≥0) : ℝ≥0∞)) =
      ∫⁻ t, h t * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹) ∂ν := by
  have hρ : Measurable fun t : (𝔸)ˣ => ((modulusDensity L t : ℝ≥0) : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp (measurable_modulusDensity L)
  rw [lintegral_withDensity_eq_lintegral_mul ν hρ hh]
  refine lintegral_congr fun t => ?_
  show ((modulusDensity L t : ℝ≥0) : ℝ≥0∞) * h t = h t * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)
  rw [mul_comm]
  rfl

private theorem lintegral_coordWord_eq (μ : Measure 𝔸) (ν₁ ν₂ : Measure (𝔸)ˣ) [SFinite ν₁] [SFinite ν₂]
    (ψ : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ p, ψ (coordWord L p)
        ∂(μ.prod (ν₁.prod ((ν₂.withDensity fun t => ((modulusDensity L t : ℝ≥0) : ℝ≥0∞)).prod
          (maximalCompactHaar L)))) =
      ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
          ψ (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)
        ∂(maximalCompactHaar L) ∂ν₂ ∂ν₁ ∂μ := by
  have hm : Measurable fun p : Coord L => ψ (coordWord L p) := hψ.comp (measurable_coordWord L)
  have h1 : ∀ x : 𝔸, Measurable fun q : (𝔸)ˣ × ((𝔸)ˣ × ↥(adelicMaximalCompact L)) =>
      ψ (coordWord L (x, q)) :=
    fun x => hm.comp measurable_prodMk_left
  have h2 : ∀ (x : 𝔸) (u : (𝔸)ˣ), Measurable fun q : (𝔸)ˣ × ↥(adelicMaximalCompact L) =>
      ψ (coordWord L (x, (u, q))) :=
    fun x u => (h1 x).comp measurable_prodMk_left
  have h3 : ∀ (x : 𝔸) (u t : (𝔸)ˣ), Measurable fun k : ↥(adelicMaximalCompact L) =>
      ψ (coordWord L (x, (u, (t, k)))) :=
    fun x u t => (h2 x u).comp measurable_prodMk_left
  calc ∫⁻ p, ψ (coordWord L p)
        ∂(μ.prod (ν₁.prod ((ν₂.withDensity fun t => ((modulusDensity L t : ℝ≥0) : ℝ≥0∞)).prod
          (maximalCompactHaar L))))
      = ∫⁻ x, ∫⁻ q, ψ (coordWord L (x, q))
          ∂(ν₁.prod ((ν₂.withDensity fun t => ((modulusDensity L t : ℝ≥0) : ℝ≥0∞)).prod
            (maximalCompactHaar L))) ∂μ :=
        lintegral_prod _ hm.aemeasurable
    _ = ∫⁻ x, ∫⁻ u, ∫⁻ q, ψ (coordWord L (x, (u, q)))
          ∂((ν₂.withDensity fun t => ((modulusDensity L t : ℝ≥0) : ℝ≥0∞)).prod (maximalCompactHaar L))
          ∂ν₁ ∂μ :=
        lintegral_congr fun x => lintegral_prod _ (h1 x).aemeasurable
    _ = ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k, ψ (coordWord L (x, (u, (t, k)))) ∂(maximalCompactHaar L)
          ∂(ν₂.withDensity fun t => ((modulusDensity L t : ℝ≥0) : ℝ≥0∞)) ∂ν₁ ∂μ :=
        lintegral_congr fun x => lintegral_congr fun u => lintegral_prod _ (h2 x u).aemeasurable
    _ = _ := by
        refine lintegral_congr fun x => lintegral_congr fun u => ?_
        have hF : Measurable fun t : (𝔸)ˣ =>
            ∫⁻ k, ψ (coordWord L (x, (u, (t, k)))) ∂(maximalCompactHaar L) :=
          (h2 x u).lintegral_prod_right'
        refine (lintegral_withDensity_modulusDensity L ν₂ _ hF).trans (lintegral_congr fun t => ?_)
        exact (lintegral_mul_const _ (h3 x u t)).symm

private theorem lintegral_iwasawaMeasure_eq [SFinite (NumberField.Idele.idelicHaar L)]
    (ψ : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ p, ψ (coordWord L p) ∂(iwasawaMeasure L) =
      ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
          ψ (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) :=
  lintegral_coordWord_eq L _ _ _ ψ hψ

private theorem restrict_iwasawaMeasure_productDomain [SFinite (NumberField.Idele.idelicHaar L)]
    [SFinite (adelicAddHaar (𝓞 L) L)] (X : Set 𝔸) (Ω₁ Ω₂ : Set (𝔸)ˣ) :
    (iwasawaMeasure L).restrict (productDomain L (X := X) (Ω₁ := Ω₁) (Ω₂ := Ω₂)) =
      ((adelicAddHaar (𝓞 L) L).restrict X).prod (((NumberField.Idele.idelicHaar L).restrict Ω₁).prod
        ((((NumberField.Idele.idelicHaar L).restrict Ω₂).withDensity fun t =>
          ((modulusDensity L t : ℝ≥0) : ℝ≥0∞)).prod (maximalCompactHaar L))) := by
  rw [← restrict_withDensity' Ω₂, Measure.restrict_prod_eq_prod_univ (ν := maximalCompactHaar L) Ω₂,
    Measure.prod_restrict, Measure.prod_restrict]
  rfl

private theorem setLIntegral_productDomain_eq [SFinite (NumberField.Idele.idelicHaar L)]
    [SFinite (adelicAddHaar (𝓞 L) L)] (X : Set 𝔸) (Ω₁ Ω₂ : Set (𝔸)ˣ)
    (ψ : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ p in productDomain L (X := X) (Ω₁ := Ω₁) (Ω₂ := Ω₂), ψ (coordWord L p) ∂(iwasawaMeasure L) =
      ∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
          ψ (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) := by
  rw [restrict_iwasawaMeasure_productDomain L X Ω₁ Ω₂]
  exact lintegral_coordWord_eq L _ _ _ ψ hψ

private def cosetCount (Φ : Set (AdelicGL2 (𝓞 L) L)) (reps : Set (GL (Fin 2) L)) (y : AdelicGL2 (𝓞 L) L) :
    ℝ≥0∞ :=
  ∑' ρ : reps, Φ.indicator 1 ((globalPoints (𝓞 L) L (ρ : GL (Fin 2) L))⁻¹ * y)

private def pointCount (Φ : Set (AdelicGL2 (𝓞 L) L)) (y : AdelicGL2 (𝓞 L) L) : ℝ≥0∞ :=
  ∑' γ : GL (Fin 2) L, Φ.indicator 1 (globalPoints (𝓞 L) L γ * y)

private theorem measurable_tsum {ι α : Type*} [Countable ι] [MeasurableSpace α] {f : ι → α → ℝ≥0∞}
    (h : ∀ i, Measurable (f i)) : Measurable fun x => ∑' i, f i x := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact Measurable.iSup fun s => s.measurable_fun_sum fun i _ => h i

private theorem measurable_cosetCount {Φ : Set (AdelicGL2 (𝓞 L) L)} (hΦm : MeasurableSet Φ)
    (reps : Set (GL (Fin 2) L)) : Measurable (cosetCount L Φ reps) := by
  haveI := countable_gl L
  unfold cosetCount
  exact measurable_tsum fun ρ => (measurable_one.indicator hΦm).comp (measurable_const_mul _)

private theorem measurable_pointCount {Φ : Set (AdelicGL2 (𝓞 L) L)} (hΦm : MeasurableSet Φ) :
    Measurable (pointCount L Φ) := by
  haveI := countable_gl L
  unfold pointCount
  exact measurable_tsum fun γ => (measurable_one.indicator hΦm).comp (measurable_const_mul _)

private theorem indicator_translate {G₀ : Type*} [Group G₀] (Φ : Set G₀) (f : G₀ → ℝ≥0∞) (g y : G₀) :
    Φ.indicator (fun z => f (g * z)) (g⁻¹ * y) = Φ.indicator 1 (g⁻¹ * y) * f y := by
  by_cases hy : g⁻¹ * y ∈ Φ
  · simp only [Set.indicator_of_mem hy, Pi.one_apply, one_mul, mul_inv_cancel_left]
  · simp only [Set.indicator_of_notMem hy, zero_mul]

private theorem setLIntegral_tsum_eq_lintegral_cosetCount {Φ : Set (AdelicGL2 (𝓞 L) L)} (hΦm : MeasurableSet Φ)
    (reps : Set (GL (Fin 2) L)) (f : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y in Φ, ∑' ρ : reps, f (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * y) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      ∫⁻ y, cosetCount L Φ reps y * f y ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by
  haveI := countable_gl L
  have hρ : ∀ ρ : reps, Measurable fun y : AdelicGL2 (𝓞 L) L => f (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * y) :=
    fun ρ => hf.comp (measurable_const_mul _)
  have hind : ∀ ρ : reps, Measurable fun y : AdelicGL2 (𝓞 L) L =>
      Φ.indicator 1 ((globalPoints (𝓞 L) L (ρ : GL (Fin 2) L))⁻¹ * y) * f y :=
    fun ρ => ((measurable_one.indicator hΦm).comp (measurable_const_mul _)).mul hf
  calc ∫⁻ y in Φ, ∑' ρ : reps, f (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * y) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
      = ∑' ρ : reps, ∫⁻ y in Φ, f (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * y) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) :=
        lintegral_tsum fun ρ => (hρ ρ).aemeasurable
    _ = ∑' ρ : reps, ∫⁻ y, Φ.indicator 1 ((globalPoints (𝓞 L) L (ρ : GL (Fin 2) L))⁻¹ * y) * f y
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by
        refine tsum_congr fun ρ => ?_
        rw [← lintegral_indicator hΦm,
          ← (measurePreserving_mul_left (adelicGLHaar (Fin 2) (𝓞 L) L)
            (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L))⁻¹).lintegral_comp ((hρ ρ).indicator hΦm)]
        exact lintegral_congr fun y => indicator_translate Φ f _ y
    _ = ∫⁻ y, ∑' ρ : reps, Φ.indicator 1 ((globalPoints (𝓞 L) L (ρ : GL (Fin 2) L))⁻¹ * y) * f y
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L) :=
        (lintegral_tsum fun ρ => (hind ρ).aemeasurable).symm
    _ = ∫⁻ y, cosetCount L Φ reps y * f y ∂(adelicGLHaar (Fin 2) (𝓞 L) L) :=
        lintegral_congr fun y => ENNReal.tsum_mul_right

private def repMul (reps : Set (GL (Fin 2) L)) (p : borelSubgroup L × reps) : GL (Fin 2) L :=
  (p.2 : GL (Fin 2) L)⁻¹ * (p.1 : GL (Fin 2) L)

omit [NumberField L] in

private theorem repMul_bijective {reps : Set (GL (Fin 2) L)}
    (hreps : ∀ g : GL (Fin 2) L, ∃! ρ : GL (Fin 2) L, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup L) :
    Function.Bijective (repMul L reps) := by
  refine ⟨?_, fun γ => ?_⟩
  · rintro ⟨β, ρ⟩ ⟨β', ρ'⟩ h
    change (ρ : GL (Fin 2) L)⁻¹ * (β : GL (Fin 2) L) = (ρ' : GL (Fin 2) L)⁻¹ * (β' : GL (Fin 2) L) at h
    have key : (ρ' : GL (Fin 2) L) * (ρ : GL (Fin 2) L)⁻¹ = (β' : GL (Fin 2) L) * (β : GL (Fin 2) L)⁻¹ := by
      calc (ρ' : GL (Fin 2) L) * (ρ : GL (Fin 2) L)⁻¹
          = (ρ' : GL (Fin 2) L) * ((ρ : GL (Fin 2) L)⁻¹ * (β : GL (Fin 2) L) * (β : GL (Fin 2) L)⁻¹) := by
            rw [mul_inv_cancel_right]
        _ = (β' : GL (Fin 2) L) * (β : GL (Fin 2) L)⁻¹ := by
            rw [h, mul_assoc ((ρ' : GL (Fin 2) L)⁻¹), mul_inv_cancel_left]
    have hB : (ρ' : GL (Fin 2) L) * (ρ : GL (Fin 2) L)⁻¹ ∈ borelSubgroup L := by
      rw [key]
      exact Subgroup.mul_mem _ β'.2 (Subgroup.inv_mem _ β.2)
    obtain ⟨ρ₀, -, huniq⟩ := hreps (ρ' : GL (Fin 2) L)
    have h1 : (ρ : GL (Fin 2) L) = ρ₀ := huniq _ ⟨ρ.2, hB⟩
    have h2 : (ρ' : GL (Fin 2) L) = ρ₀ := huniq _ ⟨ρ'.2, by rw [mul_inv_cancel]; exact Subgroup.one_mem _⟩
    obtain rfl : ρ = ρ' := Subtype.ext (h1.trans h2.symm)
    obtain rfl : β = β' := Subtype.ext (mul_left_cancel h)
    rfl
  · obtain ⟨ρ, ⟨hρ, hB⟩, -⟩ := hreps γ⁻¹
    refine ⟨(⟨ρ * γ, ?_⟩, ⟨ρ, hρ⟩), ?_⟩
    · have h := Subgroup.inv_mem _ hB
      rwa [_root_.mul_inv_rev, inv_inv, inv_inv] at h
    · show ρ⁻¹ * (ρ * γ) = γ
      exact inv_mul_cancel_left ρ γ

omit [NumberField L] in
private theorem tsum_tsum_eq_tsum {reps : Set (GL (Fin 2) L)}
    (hreps : ∀ g : GL (Fin 2) L, ∃! ρ : GL (Fin 2) L, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup L)
    (f : GL (Fin 2) L → ℝ≥0∞) :
    ∑' β : borelSubgroup L, ∑' ρ : reps, f ((ρ : GL (Fin 2) L)⁻¹ * (β : GL (Fin 2) L)) =
      ∑' γ : GL (Fin 2) L, f γ :=
  calc ∑' β : borelSubgroup L, ∑' ρ : reps, f ((ρ : GL (Fin 2) L)⁻¹ * (β : GL (Fin 2) L))
      = ∑' p : borelSubgroup L × reps, f ((p.2 : GL (Fin 2) L)⁻¹ * (p.1 : GL (Fin 2) L)) :=
        (ENNReal.tsum_prod' (f := fun p : borelSubgroup L × reps =>
          f ((p.2 : GL (Fin 2) L)⁻¹ * (p.1 : GL (Fin 2) L)))).symm
    _ = ∑' γ : GL (Fin 2) L, f γ := (Equiv.ofBijective _ (repMul_bijective L hreps)).tsum_eq f

private theorem tsum_cosetCount {reps : Set (GL (Fin 2) L)}
    (hreps : ∀ g : GL (Fin 2) L, ∃! ρ : GL (Fin 2) L, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup L)
    (Φ : Set (AdelicGL2 (𝓞 L) L)) (y : AdelicGL2 (𝓞 L) L) :
    ∑' β : borelSubgroup L, cosetCount L Φ reps (globalPoints (𝓞 L) L (β : GL (Fin 2) L) * y) =
      pointCount L Φ y := by
  unfold cosetCount pointCount
  have h : ∀ (β : borelSubgroup L) (ρ : reps),
      (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L))⁻¹ * (globalPoints (𝓞 L) L (β : GL (Fin 2) L) * y) =
        globalPoints (𝓞 L) L ((ρ : GL (Fin 2) L)⁻¹ * (β : GL (Fin 2) L)) * y := fun β ρ => by
    rw [map_mul, map_inv, mul_assoc]
  simp only [h]
  exact tsum_tsum_eq_tsum L hreps fun γ => Φ.indicator 1 (globalPoints (𝓞 L) L γ * y)

private theorem smulInvariantMeasure_restrict {S₀ : Set (AdelicGL2 (𝓞 L) L)} (hS₀m : MeasurableSet S₀)
    (hS₀ : ∀ (γ : GL (Fin 2) L) (g : AdelicGL2 (𝓞 L) L), globalPoints (𝓞 L) L γ * g ∈ S₀ ↔ g ∈ S₀) :
    SMulInvariantMeasure (globalPoints (𝓞 L) L).range (AdelicGL2 (𝓞 L) L)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀) := by
  refine ⟨fun g s hs => ?_⟩
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp g.2
  have hmp : MeasurePreserving (fun x : AdelicGL2 (𝓞 L) L => (g : AdelicGL2 (𝓞 L) L) * x)
      (adelicGLHaar (Fin 2) (𝓞 L) L) (adelicGLHaar (Fin 2) (𝓞 L) L) :=
    measurePreserving_mul_left _ _
  have hpre : (fun x : AdelicGL2 (𝓞 L) L => (g : AdelicGL2 (𝓞 L) L) * x) ⁻¹' s ∩ S₀ =
      (fun x : AdelicGL2 (𝓞 L) L => (g : AdelicGL2 (𝓞 L) L) * x) ⁻¹' (s ∩ S₀) := by
    ext x
    show (g : AdelicGL2 (𝓞 L) L) * x ∈ s ∧ x ∈ S₀ ↔
      (g : AdelicGL2 (𝓞 L) L) * x ∈ s ∧ (g : AdelicGL2 (𝓞 L) L) * x ∈ S₀
    rw [← hγ, hS₀ γ x]
  show ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀)
      ((fun x : AdelicGL2 (𝓞 L) L => (g : AdelicGL2 (𝓞 L) L) * x) ⁻¹' s) =
    ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀) s
  rw [Measure.restrict_apply (measurable_const_mul (g : AdelicGL2 (𝓞 L) L) hs), Measure.restrict_apply hs, hpre]
  exact hmp.measure_preimage (hs.inter hS₀m).nullMeasurableSet

private theorem ae_pointCount_eq_one {S₀ Φ : Set (AdelicGL2 (𝓞 L) L)} (hS₀m : MeasurableSet S₀)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀)) :
    ∀ᵐ y ∂(adelicGLHaar (Fin 2) (𝓞 L) L), y ∈ S₀ → pointCount L Φ y = 1 := by
  haveI := countable_gl L
  rw [← ae_restrict_iff' hS₀m]
  have hex : ∀ᵐ y ∂((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀),
      ∃ γ : GL (Fin 2) L, globalPoints (𝓞 L) L γ * y ∈ Φ :=
    hΦ.ae_covers.mono fun y ⟨g, hg⟩ => by
      obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp g.2
      exact ⟨γ, by rw [hγ]; exact hg⟩
  have huniq : ∀ᵐ y ∂((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀), ∀ γ γ' : GL (Fin 2) L,
      globalPoints (𝓞 L) L γ * y ∈ Φ → globalPoints (𝓞 L) L γ' * y ∈ Φ → γ = γ' := by
    refine ae_all_iff.2 fun γ => ae_all_iff.2 fun γ' => ?_
    by_cases hne : γ = γ'
    · exact Filter.Eventually.of_forall fun y _ _ => hne
    · have hne' : (⟨globalPoints (𝓞 L) L γ, γ, rfl⟩ : (globalPoints (𝓞 L) L).range)⁻¹ ≠
          (⟨globalPoints (𝓞 L) L γ', γ', rfl⟩ : (globalPoints (𝓞 L) L).range)⁻¹ := fun h =>
        hne (globalPoints_injective L (Subtype.ext_iff.mp (inv_injective h)))
      have h0 : ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀)
          ((⟨globalPoints (𝓞 L) L γ, γ, rfl⟩ : (globalPoints (𝓞 L) L).range)⁻¹ • Φ ∩
            (⟨globalPoints (𝓞 L) L γ', γ', rfl⟩ : (globalPoints (𝓞 L) L).range)⁻¹ • Φ) = 0 :=
        hΦ.aedisjoint hne'
      refine (measure_eq_zero_iff_ae_notMem.1 h0).mono fun y hy h1 h2 => (hy ⟨?_, ?_⟩).elim
      · exact Set.mem_inv_smul_set_iff.mpr h1
      · exact Set.mem_inv_smul_set_iff.mpr h2
  filter_upwards [hex, huniq] with y hy hu
  obtain ⟨γ₀, h₀⟩ := hy
  have hsum : pointCount L Φ y = Φ.indicator 1 (globalPoints (𝓞 L) L γ₀ * y) :=
    tsum_eq_single γ₀ fun γ hγ => Set.indicator_of_notMem (fun h => hγ (hu γ γ₀ h h₀)) _
  rw [hsum, Set.indicator_of_mem h₀, Pi.one_apply]

private theorem exists_measurableSet_fundamentalDomain {S₀ Φ₀ : Set (AdelicGL2 (𝓞 L) L)} (hS₀m : MeasurableSet S₀)
    (hS₀ : ∀ (γ : GL (Fin 2) L) (g : AdelicGL2 (𝓞 L) L), globalPoints (𝓞 L) L γ * g ∈ S₀ ↔ g ∈ S₀)
    (hΦ₀S : Φ₀ ⊆ S₀)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀)) :
    ∃ Φ : Set (AdelicGL2 (𝓞 L) L), Φ ⊆ Φ₀ ∧ MeasurableSet Φ ∧ Φ =ᵐ[adelicGLHaar (Fin 2) (𝓞 L) L] Φ₀ ∧
      IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀) := by
  haveI := countable_range L
  obtain ⟨Φ, hΦsub, hΦm, hΦae⟩ := hΦ₀.nullMeasurableSet.exists_measurable_subset_ae_eq
  refine ⟨Φ, hΦsub, hΦm, ?_, hΦm.nullMeasurableSet, ?_, ?_⟩
  · have h := ae_eq_set.mp hΦae
    rw [Measure.restrict_apply' hS₀m, Measure.restrict_apply' hS₀m,
      Set.inter_eq_self_of_subset_left (Set.diff_subset.trans (hΦsub.trans hΦ₀S)),
      Set.inter_eq_self_of_subset_left (Set.diff_subset.trans hΦ₀S)] at h
    exact ae_eq_set.mpr h
  · obtain ⟨N, hsubN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_eq_set.mp hΦae).2
    have hU : ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀)
        (⋃ g : (globalPoints (𝓞 L) L).range, (fun x : AdelicGL2 (𝓞 L) L => g • x) ⁻¹' N) = 0 :=
      measure_iUnion_null fun g => by
        rw [(smulInvariantMeasure_restrict L hS₀m hS₀).measure_preimage_smul g hNm]
        exact hN0
    refine (hΦ₀.ae_covers.and (measure_eq_zero_iff_ae_notMem.1 hU)).mono fun x hx => ?_
    obtain ⟨⟨g, hg⟩, hxU⟩ := hx
    refine ⟨g, ?_⟩
    by_contra hcon
    exact hxU (Set.mem_iUnion.mpr ⟨g, hsubN ⟨hg, hcon⟩⟩)
  · intro g g' hne
    have hd : AEDisjoint ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀) (g • Φ₀) (g' • Φ₀) := hΦ₀.aedisjoint hne
    exact hd.mono (Set.smul_set_mono hΦsub) (Set.smul_set_mono hΦsub)

private theorem iwasawaMeasure_preimage_null [SFinite (NumberField.Idele.idelicHaar L)] {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : ∀ φ : AdelicGL2 (𝓞 L) L → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
        c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
              φ (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
                ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)
            ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
            ∂(adelicAddHaar (𝓞 L) L))
    {Z : Set (AdelicGL2 (𝓞 L) L)} (hZm : MeasurableSet Z) (hZ : adelicGLHaar (Fin 2) (𝓞 L) L Z = 0) :
    iwasawaMeasure L (coordWord L ⁻¹' Z) = 0 := by
  have h := hc (Z.indicator 1) (measurable_one.indicator hZm)
  rw [lintegral_indicator_one hZm, hZ, ← lintegral_iwasawaMeasure_eq L _ (measurable_one.indicator hZm)] at h
  have h2 : ∫⁻ p, Z.indicator (1 : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (coordWord L p) ∂(iwasawaMeasure L) = 0 :=
    (mul_eq_zero.mp h.symm).resolve_left hc0
  have h3 : (fun p => Z.indicator (1 : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (coordWord L p)) =
      (coordWord L ⁻¹' Z).indicator 1 := by
    funext p
    by_cases hp : coordWord L p ∈ Z
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (Set.mem_preimage.mpr hp)]
      rfl
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem fun h => hp (Set.mem_preimage.mp h)]
  rw [h3, lintegral_indicator_one (hZm.preimage (measurable_coordWord L))] at h2
  exact h2

private theorem lintegral_cosetCount_mul_eq [SigmaFinite (NumberField.Idele.idelicHaar L)]
    {Φ : Set (AdelicGL2 (𝓞 L) L)} (hΦm : MeasurableSet Φ) {reps : Set (GL (Fin 2) L)}
    (hreps : ∀ g : GL (Fin 2) L, ∃! ρ : GL (Fin 2) L, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup L)
    {X : Set 𝔸} (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    {Ω₁ Ω₂ : Set (𝔸)ˣ} (hΩ₁ : IsFundamentalDomain (principalRange L) Ω₁ (NumberField.Idele.idelicHaar L))
    (hΩ₂ : IsFundamentalDomain (principalRange L) Ω₂ (NumberField.Idele.idelicHaar L))
    {G : AdelicGL2 (𝓞 L) L → ℝ≥0∞} (hGm : Measurable G)
    (hGinv : ∀ (β : borelSubgroup L) (g : AdelicGL2 (𝓞 L) L), G (globalPoints (𝓞 L) L (β : GL (Fin 2) L) * g) = G g) :
    ∫⁻ p, cosetCount L Φ reps (coordWord L p) * G (coordWord L p) ∂(iwasawaMeasure L) =
      ∫⁻ p in productDomain L (X := X) (Ω₁ := Ω₁) (Ω₂ := Ω₂), pointCount L Φ (coordWord L p) * G (coordWord L p)
        ∂(iwasawaMeasure L) := by
  haveI := countable_gl L
  haveI := countable_borelSubgroup L
  haveI : MeasurableConstSMul (borelSubgroup L) (Coord L) :=
    ⟨fun γ => (measurePreserving_smul L (measurable_modulusDensity L) (ideleNorm_principalUnit L)
      (measurePreserving_mul_principal L) γ).measurable⟩
  haveI : SMulInvariantMeasure (borelSubgroup L) (Coord L) (iwasawaMeasure L) :=
    ⟨fun γ _s hs => (measurePreserving_smul L (measurable_modulusDensity L) (ideleNorm_principalUnit L)
      (measurePreserving_mul_principal L) γ).measure_preimage hs.nullMeasurableSet⟩
  have hD := isFundamentalDomain_productDomain L (measurable_modulusDensity L) (ideleNorm_principalUnit L)
    (measurePreserving_mul_principal L) hX hΩ₁ hΩ₂
  have hNm := measurable_cosetCount L hΦm reps
  have hmeas : ∀ β : borelSubgroup L, Measurable fun p : Coord L =>
      cosetCount L Φ reps (globalPoints (𝓞 L) L (β : GL (Fin 2) L) * coordWord L p) * G (coordWord L p) :=
    fun β => ((hNm.comp (measurable_const_mul _)).comp (measurable_coordWord L)).mul
      (hGm.comp (measurable_coordWord L))
  rw [hD.lintegral_eq_tsum'' fun p => cosetCount L Φ reps (coordWord L p) * G (coordWord L p)]
  simp only [coordWord_smul, hGinv]
  rw [← lintegral_tsum fun β => (hmeas β).aemeasurable]
  refine lintegral_congr fun p => ?_
  rw [ENNReal.tsum_mul_right, tsum_cosetCount L hreps]

private theorem measure_inter_preimage_pointCount_eq_zero {S₀ Φ : Set (AdelicGL2 (𝓞 L) L)} (hS₀m : MeasurableSet S₀)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀)) :
    adelicGLHaar (Fin 2) (𝓞 L) L (S₀ ∩ pointCount L Φ ⁻¹' ({1} : Set ℝ≥0∞)ᶜ) = 0 := by
  have hae := ae_pointCount_eq_one L hS₀m hΦ
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hae] with y hy hmem
  rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hmem
  exact hmem.2 (hy hmem.1)

private theorem ae_pointCount_mul_indicator_eq_of_null {S₀ Φ : Set (AdelicGL2 (𝓞 L) L)} (F : AdelicGL2 (𝓞 L) L → ℝ≥0∞)
    (hZ : iwasawaMeasure L (coordWord L ⁻¹' (S₀ ∩ pointCount L Φ ⁻¹' ({1} : Set ℝ≥0∞)ᶜ)) = 0) :
    ∀ᵐ p ∂(iwasawaMeasure L),
      pointCount L Φ (coordWord L p) * S₀.indicator F (coordWord L p) = S₀.indicator F (coordWord L p) := by
  rw [measure_eq_zero_iff_ae_notMem] at hZ
  filter_upwards [hZ] with p hp
  rw [Set.mem_preimage, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, not_and,
    not_not] at hp
  by_cases hpS : coordWord L p ∈ S₀
  · rw [hp hpS, one_mul]
  · rw [Set.indicator_of_notMem hpS, mul_zero]

private theorem ae_pointCount_mul_indicator_eq [SigmaFinite (NumberField.Idele.idelicHaar L)] {c : ℝ≥0∞}
    (hc0 : c ≠ 0)
    (hc : ∀ φ : AdelicGL2 (𝓞 L) L → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
        c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
              φ (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
                ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)
            ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
            ∂(adelicAddHaar (𝓞 L) L))
    {S₀ Φ : Set (AdelicGL2 (𝓞 L) L)} (hS₀m : MeasurableSet S₀) (hΦm : MeasurableSet Φ)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀))
    (F : AdelicGL2 (𝓞 L) L → ℝ≥0∞) :
    ∀ᵐ p ∂(iwasawaMeasure L),
      pointCount L Φ (coordWord L p) * S₀.indicator F (coordWord L p) = S₀.indicator F (coordWord L p) :=
  ae_pointCount_mul_indicator_eq_of_null L F
    (iwasawaMeasure_preimage_null L hc0 hc
      (hS₀m.inter (measurable_pointCount L hΦm (measurableSet_singleton (1 : ℝ≥0∞)).compl))
      (measure_inter_preimage_pointCount_eq_zero L hS₀m hΦ))

private theorem indicator_mul_eq {S₀ : Set (AdelicGL2 (𝓞 L) L)}
    (hS₀ : ∀ (γ : GL (Fin 2) L) (g : AdelicGL2 (𝓞 L) L), globalPoints (𝓞 L) L γ * g ∈ S₀ ↔ g ∈ S₀)
    {M : Type*} [Zero M] {F : AdelicGL2 (𝓞 L) L → M}
    (hF : ∀ β ∈ borelSubgroup L, ∀ g : AdelicGL2 (𝓞 L) L, F (globalPoints (𝓞 L) L β * g) = F g)
    (β : borelSubgroup L) (g : AdelicGL2 (𝓞 L) L) :
    S₀.indicator F (globalPoints (𝓞 L) L (β : GL (Fin 2) L) * g) = S₀.indicator F g := by
  by_cases hg : g ∈ S₀
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hS₀ (β : GL (Fin 2) L) g).mpr hg), hF _ β.2]
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem fun h => hg ((hS₀ (β : GL (Fin 2) L) g).mp h)]

private theorem setLIntegral_tsum_eq_of_measurableSet [SigmaFinite (NumberField.Idele.idelicHaar L)]
    [SFinite (adelicAddHaar (𝓞 L) L)] {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : ∀ φ : AdelicGL2 (𝓞 L) L → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
        c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
              φ (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
                ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)
            ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
            ∂(adelicAddHaar (𝓞 L) L))
    {S₀ : Set (AdelicGL2 (𝓞 L) L)} (hS₀m : MeasurableSet S₀)
    (hS₀ : ∀ (γ : GL (Fin 2) L) (g : AdelicGL2 (𝓞 L) L), globalPoints (𝓞 L) L γ * g ∈ S₀ ↔ g ∈ S₀)
    {Φ : Set (AdelicGL2 (𝓞 L) L)} (hΦm : MeasurableSet Φ) (hΦS : Φ ⊆ S₀)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀))
    {reps : Set (GL (Fin 2) L)}
    (hreps : ∀ g : GL (Fin 2) L, ∃! ρ : GL (Fin 2) L, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup L)
    {X : Set 𝔸} (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    {Ω₁ Ω₂ : Set (𝔸)ˣ} (hΩ₁ : IsFundamentalDomain (principalRange L) Ω₁ (NumberField.Idele.idelicHaar L))
    (hΩ₂ : IsFundamentalDomain (principalRange L) Ω₂ (NumberField.Idele.idelicHaar L))
    (F : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (hFm : Measurable F)
    (hF : ∀ β ∈ borelSubgroup L, ∀ g : AdelicGL2 (𝓞 L) L, F (globalPoints (𝓞 L) L β * g) = F g) :
    ∫⁻ x in Φ, ∑' ρ : reps, F (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      c * ∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
            S₀.indicator F (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
          ∂(adelicAddHaar (𝓞 L) L) := by
  have hGm : Measurable (S₀.indicator F) := hFm.indicator hS₀m
  have hNm := measurable_cosetCount L hΦm reps

  have h1 : ∫⁻ x in Φ, ∑' ρ : reps, F (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      ∫⁻ x in Φ, ∑' ρ : reps, S₀.indicator F (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L) :=
    setLIntegral_congr_fun hΦm fun x hx =>
      tsum_congr fun ρ => (Set.indicator_of_mem ((hS₀ (ρ : GL (Fin 2) L) x).mpr (hΦS hx)) F).symm

  have h2 := hc _ (hNm.mul hGm)
  have h3 := lintegral_iwasawaMeasure_eq L _ (hNm.mul hGm)

  have h4 := lintegral_cosetCount_mul_eq L hΦm hreps hX hΩ₁ hΩ₂ hGm (indicator_mul_eq L hS₀ hF)
  have h5 : ∫⁻ p in productDomain L (X := X) (Ω₁ := Ω₁) (Ω₂ := Ω₂),
      pointCount L Φ (coordWord L p) * S₀.indicator F (coordWord L p) ∂(iwasawaMeasure L) =
      ∫⁻ p in productDomain L (X := X) (Ω₁ := Ω₁) (Ω₂ := Ω₂), S₀.indicator F (coordWord L p)
        ∂(iwasawaMeasure L) :=
    lintegral_congr_ae (ae_restrict_of_ae (ae_pointCount_mul_indicator_eq L hc0 hc hS₀m hΦm hΦ F))
  have h6 := setLIntegral_productDomain_eq L X Ω₁ Ω₂ _ hGm
  rw [h1]
  erw [setLIntegral_tsum_eq_lintegral_cosetCount L hΦm reps _ hGm]
  simp only [Pi.mul_apply] at h2 h3
  rw [h2, ← h3, h4, h5, h6]

private theorem setLIntegral_tsum_eq [SigmaFinite (NumberField.Idele.idelicHaar L)] [SFinite (adelicAddHaar (𝓞 L) L)]
    {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : ∀ φ : AdelicGL2 (𝓞 L) L → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
        c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
              φ (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
                ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)
            ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
            ∂(adelicAddHaar (𝓞 L) L))
    {S₀ : Set (AdelicGL2 (𝓞 L) L)} (hS₀m : MeasurableSet S₀)
    (hS₀ : ∀ (γ : GL (Fin 2) L) (g : AdelicGL2 (𝓞 L) L), globalPoints (𝓞 L) L γ * g ∈ S₀ ↔ g ∈ S₀)
    {Φ₀ : Set (AdelicGL2 (𝓞 L) L)} (hΦ₀S : Φ₀ ⊆ S₀)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀))
    {reps : Set (GL (Fin 2) L)}
    (hreps : ∀ g : GL (Fin 2) L, ∃! ρ : GL (Fin 2) L, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup L)
    {X : Set 𝔸} (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    {Ω₁ Ω₂ : Set (𝔸)ˣ} (hΩ₁ : IsFundamentalDomain (principalRange L) Ω₁ (NumberField.Idele.idelicHaar L))
    (hΩ₂ : IsFundamentalDomain (principalRange L) Ω₂ (NumberField.Idele.idelicHaar L))
    (F : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (hFm : Measurable F)
    (hF : ∀ β ∈ borelSubgroup L, ∀ g : AdelicGL2 (𝓞 L) L, F (globalPoints (𝓞 L) L β * g) = F g) :
    ∫⁻ x in Φ₀, ∑' ρ : reps, F (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      c * ∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
            S₀.indicator F (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
          ∂(adelicAddHaar (𝓞 L) L) := by
  obtain ⟨Φ, hΦsub, hΦm, hΦae, hΦ⟩ := exists_measurableSet_fundamentalDomain L hS₀m hS₀ hΦ₀S hΦ₀
  rw [← setLIntegral_congr hΦae]
  exact setLIntegral_tsum_eq_of_measurableSet L hc0 hc hS₀m hS₀ hΦm (hΦsub.trans hΦ₀S) hΦ hreps hX hΩ₁ hΩ₂ F hFm hF

private def repMeasure (Φ : Set (AdelicGL2 (𝓞 L) L)) (reps : Set (GL (Fin 2) L)) : Measure (AdelicGL2 (𝓞 L) L) :=
  Measure.sum fun ρ : reps =>
    ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ).map fun x => globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x

private def wordMeasure (c : ℝ≥0∞) (S₀ : Set (AdelicGL2 (𝓞 L) L)) (X : Set 𝔸) (Ω₁ Ω₂ : Set (𝔸)ˣ) :
    Measure (AdelicGL2 (𝓞 L) L) :=
  c • (((iwasawaMeasure L).restrict (productDomain L (X := X) (Ω₁ := Ω₁) (Ω₂ := Ω₂))).map (coordWord L)).restrict S₀

private theorem lintegral_repMeasure (Φ : Set (AdelicGL2 (𝓞 L) L)) (reps : Set (GL (Fin 2) L))
    (f : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y ∂(repMeasure L Φ reps) =
      ∫⁻ x in Φ, ∑' ρ : reps, f (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by
  haveI := countable_gl L
  have hρ : ∀ ρ : reps, Measurable fun y : AdelicGL2 (𝓞 L) L => f (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * y) :=
    fun ρ => hf.comp (measurable_const_mul _)
  rw [repMeasure, lintegral_sum_measure]
  refine (tsum_congr fun ρ => ?_).trans (lintegral_tsum fun ρ => (hρ ρ).aemeasurable).symm
  exact lintegral_map hf (measurable_const_mul _)

private theorem lintegral_wordMeasure [SigmaFinite (NumberField.Idele.idelicHaar L)] [SFinite (adelicAddHaar (𝓞 L) L)]
    (c : ℝ≥0∞) {S₀ : Set (AdelicGL2 (𝓞 L) L)} (hS₀m : MeasurableSet S₀) (X : Set 𝔸) (Ω₁ Ω₂ : Set (𝔸)ˣ)
    (f : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y ∂(wordMeasure L c S₀ X Ω₁ Ω₂) =
      c * ∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
            S₀.indicator f (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
          ∂(adelicAddHaar (𝓞 L) L) := by
  rw [wordMeasure, lintegral_smul_measure, ← lintegral_indicator hS₀m,
    lintegral_map (hf.indicator hS₀m) (measurable_coordWord L),
    setLIntegral_productDomain_eq L X Ω₁ Ω₂ _ (hf.indicator hS₀m)]
  rfl

private theorem lintegral_repMeasure_eq_lintegral_wordMeasure [SigmaFinite (NumberField.Idele.idelicHaar L)]
    [SFinite (adelicAddHaar (𝓞 L) L)] {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : ∀ φ : AdelicGL2 (𝓞 L) L → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
        c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
              φ (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
                ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)
            ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
            ∂(adelicAddHaar (𝓞 L) L))
    {S₀ : Set (AdelicGL2 (𝓞 L) L)} (hS₀m : MeasurableSet S₀)
    (hS₀ : ∀ (γ : GL (Fin 2) L) (g : AdelicGL2 (𝓞 L) L), globalPoints (𝓞 L) L γ * g ∈ S₀ ↔ g ∈ S₀)
    {Φ₀ : Set (AdelicGL2 (𝓞 L) L)} (hΦ₀S : Φ₀ ⊆ S₀)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀))
    {reps : Set (GL (Fin 2) L)}
    (hreps : ∀ g : GL (Fin 2) L, ∃! ρ : GL (Fin 2) L, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup L)
    {X : Set 𝔸} (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    {Ω₁ Ω₂ : Set (𝔸)ˣ} (hΩ₁ : IsFundamentalDomain (principalRange L) Ω₁ (NumberField.Idele.idelicHaar L))
    (hΩ₂ : IsFundamentalDomain (principalRange L) Ω₂ (NumberField.Idele.idelicHaar L))
    (f : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (hfm : Measurable f)
    (hf : ∀ β ∈ borelSubgroup L, ∀ g : AdelicGL2 (𝓞 L) L, f (globalPoints (𝓞 L) L β * g) = f g) :
    ∫⁻ y, f y ∂(repMeasure L Φ₀ reps) = ∫⁻ y, f y ∂(wordMeasure L c S₀ X Ω₁ Ω₂) := by
  rw [lintegral_repMeasure L Φ₀ reps f hfm, lintegral_wordMeasure L c hS₀m X Ω₁ Ω₂ f hfm]
  exact setLIntegral_tsum_eq L hc0 hc hS₀m hS₀ hΦ₀S hΦ₀ hreps hX hΩ₁ hΩ₂ f hfm hf

@[reducible]
private def invariantSpace : MeasurableSpace (AdelicGL2 (𝓞 L) L) where
  MeasurableSet' s := MeasurableSet s ∧
    ∀ β ∈ borelSubgroup L, (fun g : AdelicGL2 (𝓞 L) L => globalPoints (𝓞 L) L β * g) ⁻¹' s = s
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ => rfl⟩
  measurableSet_compl s hs := ⟨hs.1.compl, fun β hβ => by rw [Set.preimage_compl, hs.2 β hβ]⟩
  measurableSet_iUnion s hs := ⟨MeasurableSet.iUnion fun i => (hs i).1, fun β hβ => by
    rw [Set.preimage_iUnion]
    exact Set.iUnion_congr fun i => (hs i).2 β hβ⟩

private theorem invariantSpace_le : invariantSpace L ≤ NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 L) L :=
  fun _s hs => hs.1

private theorem measurable_invariantSpace {F : AdelicGL2 (𝓞 L) L → ℂ} (hFm : Measurable F)
    (hF : ∀ β ∈ borelSubgroup L, ∀ g : AdelicGL2 (𝓞 L) L, F (globalPoints (𝓞 L) L β * g) = F g) :
    Measurable[invariantSpace L] F :=
  fun t ht => ⟨hFm ht, fun β hβ => Set.ext fun g => by
    show F (globalPoints (𝓞 L) L β * g) ∈ t ↔ F g ∈ t
    rw [hF β hβ g]⟩

private theorem indicator_eq_of_preimage_eq {G₀ : Type*} (φ : G₀ → G₀) {s : Set G₀} (hs : φ ⁻¹' s = s) (g : G₀) :
    s.indicator (1 : G₀ → ℝ≥0∞) (φ g) = s.indicator 1 g := by
  have hmem : φ g ∈ s ↔ g ∈ s := by rw [← Set.mem_preimage, hs]
  by_cases hg : g ∈ s
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hmem.mpr hg)]
    rfl
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem fun h => hg (hmem.mp h)]

private theorem trim_repMeasure_eq_trim_wordMeasure [SigmaFinite (NumberField.Idele.idelicHaar L)]
    [SFinite (adelicAddHaar (𝓞 L) L)] {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : ∀ φ : AdelicGL2 (𝓞 L) L → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
        c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
              φ (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
                ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)
            ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
            ∂(adelicAddHaar (𝓞 L) L))
    {S₀ : Set (AdelicGL2 (𝓞 L) L)} (hS₀m : MeasurableSet S₀)
    (hS₀ : ∀ (γ : GL (Fin 2) L) (g : AdelicGL2 (𝓞 L) L), globalPoints (𝓞 L) L γ * g ∈ S₀ ↔ g ∈ S₀)
    {Φ₀ : Set (AdelicGL2 (𝓞 L) L)} (hΦ₀S : Φ₀ ⊆ S₀)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀))
    {reps : Set (GL (Fin 2) L)}
    (hreps : ∀ g : GL (Fin 2) L, ∃! ρ : GL (Fin 2) L, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup L)
    {X : Set 𝔸} (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    {Ω₁ Ω₂ : Set (𝔸)ˣ} (hΩ₁ : IsFundamentalDomain (principalRange L) Ω₁ (NumberField.Idele.idelicHaar L))
    (hΩ₂ : IsFundamentalDomain (principalRange L) Ω₂ (NumberField.Idele.idelicHaar L)) :
    (repMeasure L Φ₀ reps).trim (invariantSpace_le L) = (wordMeasure L c S₀ X Ω₁ Ω₂).trim (invariantSpace_le L) := by
  refine @Measure.ext _ (invariantSpace L) _ _ fun s hs => ?_
  rw [trim_measurableSet_eq (invariantSpace_le L) hs, trim_measurableSet_eq (invariantSpace_le L) hs,
    ← lintegral_indicator_one hs.1, ← lintegral_indicator_one hs.1]
  exact lintegral_repMeasure_eq_lintegral_wordMeasure L hc0 hc hS₀m hS₀ hΦ₀S hΦ₀ hreps hX hΩ₁ hΩ₂ _
    (measurable_one.indicator hs.1) fun β hβ g => indicator_eq_of_preimage_eq _ (hs.2 β hβ) g

private theorem integral_repMeasure_eq_integral_wordMeasure [SigmaFinite (NumberField.Idele.idelicHaar L)]
    [SFinite (adelicAddHaar (𝓞 L) L)] {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : ∀ φ : AdelicGL2 (𝓞 L) L → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
        c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
              φ (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
                ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)
            ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
            ∂(adelicAddHaar (𝓞 L) L))
    {S₀ : Set (AdelicGL2 (𝓞 L) L)} (hS₀m : MeasurableSet S₀)
    (hS₀ : ∀ (γ : GL (Fin 2) L) (g : AdelicGL2 (𝓞 L) L), globalPoints (𝓞 L) L γ * g ∈ S₀ ↔ g ∈ S₀)
    {Φ₀ : Set (AdelicGL2 (𝓞 L) L)} (hΦ₀S : Φ₀ ⊆ S₀)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀))
    {reps : Set (GL (Fin 2) L)}
    (hreps : ∀ g : GL (Fin 2) L, ∃! ρ : GL (Fin 2) L, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup L)
    {X : Set 𝔸} (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    {Ω₁ Ω₂ : Set (𝔸)ˣ} (hΩ₁ : IsFundamentalDomain (principalRange L) Ω₁ (NumberField.Idele.idelicHaar L))
    (hΩ₂ : IsFundamentalDomain (principalRange L) Ω₂ (NumberField.Idele.idelicHaar L))
    (F : AdelicGL2 (𝓞 L) L → ℂ) (hFm : Measurable F)
    (hF : ∀ β ∈ borelSubgroup L, ∀ g : AdelicGL2 (𝓞 L) L, F (globalPoints (𝓞 L) L β * g) = F g) :
    ∫ y, F y ∂(repMeasure L Φ₀ reps) = ∫ y, F y ∂(wordMeasure L c S₀ X Ω₁ Ω₂) := by
  have hsm : StronglyMeasurable[invariantSpace L] F := (measurable_invariantSpace L hFm hF).stronglyMeasurable
  rw [integral_trim (invariantSpace_le L) hsm, integral_trim (invariantSpace_le L) hsm,
    trim_repMeasure_eq_trim_wordMeasure L hc0 hc hS₀m hS₀ hΦ₀S hΦ₀ hreps hX hΩ₁ hΩ₂]

private theorem integral_repMeasure {Φ : Set (AdelicGL2 (𝓞 L) L)} (reps : Set (GL (Fin 2) L))
    (F : AdelicGL2 (𝓞 L) L → ℂ) (hFm : Measurable F)
    (hfin : ∫⁻ x in Φ, ∑' ρ : reps, ‖F (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x)‖ₑ
      ∂(adelicGLHaar (Fin 2) (𝓞 L) L) ≠ ∞) :
    ∫ y, F y ∂(repMeasure L Φ reps) =
      ∫ x in Φ, ∑' ρ : reps, F (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by
  haveI := countable_gl L
  have hρm : ∀ ρ : reps, Measurable fun x : AdelicGL2 (𝓞 L) L => F (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) :=
    fun ρ => hFm.comp (measurable_const_mul _)
  have hsum : ∑' ρ : reps, ∫⁻ x in Φ, ‖F (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x)‖ₑ
      ∂(adelicGLHaar (Fin 2) (𝓞 L) L) ≠ ∞ := by
    rwa [← lintegral_tsum fun ρ => (hρm ρ).enorm.aemeasurable]
  have hint : Integrable F (repMeasure L Φ reps) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_repMeasure L Φ reps _ hFm.enorm]
    exact lt_top_iff_ne_top.mpr hfin
  rw [integral_tsum (fun ρ => (hρm ρ).aestronglyMeasurable) hsum]
  unfold repMeasure at hint ⊢
  rw [integral_sum_measure hint]
  exact tsum_congr fun ρ => integral_map (measurable_const_mul _).aemeasurable hFm.aestronglyMeasurable

private theorem integral_coordWord_eq (μ : Measure 𝔸) (ν₁ ν₂ : Measure (𝔸)ˣ) [SFinite μ] [SFinite ν₁] [SFinite ν₂]
    (ψ : AdelicGL2 (𝓞 L) L → ℂ)
    (hint : Integrable (fun p : Coord L => ψ (coordWord L p))
      (μ.prod (ν₁.prod ((ν₂.withDensity fun t => ((modulusDensity L t : ℝ≥0) : ℝ≥0∞)).prod
        (maximalCompactHaar L))))) :
    ∫ p, ψ (coordWord L p)
        ∂(μ.prod (ν₁.prod ((ν₂.withDensity fun t => ((modulusDensity L t : ℝ≥0) : ℝ≥0∞)).prod
          (maximalCompactHaar L)))) =
      ∫ x, ∫ u, ∫ t, ∫ k,
          ψ (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
            (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L) ∂ν₂ ∂ν₁ ∂μ := by
  have hρm : Measurable fun t : (𝔸)ˣ => ((modulusDensity L t : ℝ≥0) : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp (measurable_modulusDensity L)
  have hρtop : ∀ᵐ t ∂ν₂, ((modulusDensity L t : ℝ≥0) : ℝ≥0∞) < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.coe_lt_top
  rw [integral_prod _ hint]
  refine integral_congr_ae ?_
  filter_upwards [hint.prod_right_ae] with x hx
  rw [integral_prod _ hx]
  refine integral_congr_ae ?_
  filter_upwards [hx.prod_right_ae] with u hu
  rw [integral_prod _ hu, integral_withDensity_eq_integral_toReal_smul hρm hρtop]
  refine integral_congr_ae ?_
  filter_upwards [] with t
  simp only [coordWord]
  rw [integral_mul_const, ENNReal.coe_toReal, Complex.real_smul, mul_comm]
  congr 1
  show ((Real.toNNReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹) : ℝ) : ℂ) = _
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr (NumberField.TateGlobal.ideleNorm_pos t).le)]

private theorem setIntegral_productDomain_eq [SigmaFinite (NumberField.Idele.idelicHaar L)]
    [SFinite (adelicAddHaar (𝓞 L) L)] (X : Set 𝔸) (Ω₁ Ω₂ : Set (𝔸)ˣ) (ψ : AdelicGL2 (𝓞 L) L → ℂ)
    (hψ : Measurable ψ)
    (hfin : ∫⁻ p in productDomain L (X := X) (Ω₁ := Ω₁) (Ω₂ := Ω₂), ‖ψ (coordWord L p)‖ₑ ∂(iwasawaMeasure L) ≠ ∞) :
    ∫ p in productDomain L (X := X) (Ω₁ := Ω₁) (Ω₂ := Ω₂), ψ (coordWord L p) ∂(iwasawaMeasure L) =
      ∫ x in X, ∫ u in Ω₁, ∫ t in Ω₂, ∫ k,
          ψ (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
            (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) := by
  have hint : Integrable (fun p : Coord L => ψ (coordWord L p))
      ((iwasawaMeasure L).restrict (productDomain L (X := X) (Ω₁ := Ω₁) (Ω₂ := Ω₂))) :=
    ⟨(hψ.comp (measurable_coordWord L)).aestronglyMeasurable,
      hasFiniteIntegral_iff_enorm.mpr (lt_top_iff_ne_top.mpr hfin)⟩
  rw [restrict_iwasawaMeasure_productDomain L X Ω₁ Ω₂] at hint ⊢
  exact integral_coordWord_eq L _ _ _ ψ hint

private theorem integral_wordMeasure [SigmaFinite (NumberField.Idele.idelicHaar L)] [SFinite (adelicAddHaar (𝓞 L) L)]
    (c : ℝ≥0∞) {S₀ : Set (AdelicGL2 (𝓞 L) L)} (hS₀m : MeasurableSet S₀) (X : Set 𝔸) (Ω₁ Ω₂ : Set (𝔸)ˣ)
    (F : AdelicGL2 (𝓞 L) L → ℂ) (hFm : Measurable F)
    (hfin : ∫⁻ p in productDomain L (X := X) (Ω₁ := Ω₁) (Ω₂ := Ω₂), ‖S₀.indicator F (coordWord L p)‖ₑ
      ∂(iwasawaMeasure L) ≠ ∞) :
    ∫ y, F y ∂(wordMeasure L c S₀ X Ω₁ Ω₂) =
      (c.toReal : ℂ) * ∫ x in X, ∫ u in Ω₁, ∫ t in Ω₂, ∫ k,
          S₀.indicator F (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
            (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) := by
  rw [wordMeasure, integral_smul_measure, ← integral_indicator hS₀m,
    integral_map (measurable_coordWord L).aemeasurable (hFm.indicator hS₀m).aestronglyMeasurable,
    setIntegral_productDomain_eq L X Ω₁ Ω₂ (S₀.indicator F) (hFm.indicator hS₀m) hfin, Complex.real_smul]

private theorem setIntegral_tsum_eq [SigmaFinite (NumberField.Idele.idelicHaar L)] [SFinite (adelicAddHaar (𝓞 L) L)]
    {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : ∀ φ : AdelicGL2 (𝓞 L) L → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
        c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
              φ (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
                ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm L t)⁻¹)
            ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
            ∂(adelicAddHaar (𝓞 L) L))
    {S₀ : Set (AdelicGL2 (𝓞 L) L)} (hS₀m : MeasurableSet S₀)
    (hS₀ : ∀ (γ : GL (Fin 2) L) (g : AdelicGL2 (𝓞 L) L), globalPoints (𝓞 L) L γ * g ∈ S₀ ↔ g ∈ S₀)
    {Φ₀ : Set (AdelicGL2 (𝓞 L) L)} (hΦ₀S : Φ₀ ⊆ S₀)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S₀))
    {reps : Set (GL (Fin 2) L)}
    (hreps : ∀ g : GL (Fin 2) L, ∃! ρ : GL (Fin 2) L, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup L)
    {X : Set 𝔸} (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    {Ω₁ Ω₂ : Set (𝔸)ˣ} (hΩ₁ : IsFundamentalDomain (principalRange L) Ω₁ (NumberField.Idele.idelicHaar L))
    (hΩ₂ : IsFundamentalDomain (principalRange L) Ω₂ (NumberField.Idele.idelicHaar L))
    (F : AdelicGL2 (𝓞 L) L → ℂ) (hFm : Measurable F)
    (hF : ∀ β ∈ borelSubgroup L, ∀ g : AdelicGL2 (𝓞 L) L, F (globalPoints (𝓞 L) L β * g) = F g)
    (habs : ∫⁻ x in Φ₀, ∑' ρ : reps, ‖F (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x)‖ₑ
      ∂(adelicGLHaar (Fin 2) (𝓞 L) L) ≠ ∞) :
    ∫ x in Φ₀, ∑' ρ : reps, F (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      (c.toReal : ℂ) * ∫ x in X, ∫ u in Ω₁, ∫ t in Ω₂, ∫ k,
          S₀.indicator F (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
            (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) := by

  have hnm : Measurable fun g => ‖F g‖ₑ := hFm.enorm
  have hninv : ∀ β ∈ borelSubgroup L, ∀ g : AdelicGL2 (𝓞 L) L,
      ‖F (globalPoints (𝓞 L) L β * g)‖ₑ = ‖F g‖ₑ := fun β hβ g => by rw [hF β hβ g]
  have hψm : Measurable fun g => ‖S₀.indicator F g‖ₑ := (hFm.indicator hS₀m).enorm
  have hswap : (fun g => ‖S₀.indicator F g‖ₑ) = S₀.indicator fun g => ‖F g‖ₑ :=
    funext fun g => enorm_indicator_eq_indicator_enorm F g
  have hfin : ∫⁻ p in productDomain L (X := X) (Ω₁ := Ω₁) (Ω₂ := Ω₂),
      ‖S₀.indicator F (coordWord L p)‖ₑ ∂(iwasawaMeasure L) ≠ ∞ := by
    intro htop
    apply habs
    rw [setLIntegral_tsum_eq L hc0 hc hS₀m hS₀ hΦ₀S hΦ₀ hreps hX hΩ₁ hΩ₂ _ hnm hninv, ← hswap,
      ← setLIntegral_productDomain_eq L X Ω₁ Ω₂ _ hψm, htop, ENNReal.mul_top hc0]
  rw [← integral_repMeasure L reps F hFm habs,
    integral_repMeasure_eq_integral_wordMeasure L hc0 hc hS₀m hS₀ hΦ₀S hΦ₀ hreps hX hΩ₁ hΩ₂ F hFm hF,
    integral_wordMeasure L c hS₀m X Ω₁ Ω₂ F hFm hfin]

end Unfolding

end BorelWord
p2m_reactivate "P2MW.S_UnipotentTermUnfolding_exists_forall_setIntegral_unipotentTerm_eq_mul_integral_iwasawa.BorelWord"

end
p2m_reactivate "P2MW.S_UnipotentTermUnfolding_exists_forall_setIntegral_unipotentTerm_eq_mul_integral_iwasawa.BorelWord"

namespace TwistedUnipotentTerm

section IwasawaUnfolding

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

private theorem exists_forall_setLIntegral_tsum_eq_mul_lintegral_iwasawa (K : Type) [Field K] [NumberField K] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
    (∀ (S₀ : Set (AdelicGL2 (𝓞 K) K)), MeasurableSet S₀ →
        (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), globalPoints (𝓞 K) K γ * g ∈ S₀ ↔ g ∈ S₀) →
      ∀ (Φ₀ : Set (AdelicGL2 (𝓞 K) K)), Φ₀ ⊆ S₀ →
        IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict S₀) →
      ∀ (reps : Set (GL (Fin 2) K)),
        (∀ g : GL (Fin 2) K, ∃! ρ : GL (Fin 2) K, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup K) →
      ∀ (X : Set (AdeleRing (𝓞 K) K)) (Ω₁ Ω₂ : Set (AdeleRing (𝓞 K) K)ˣ),
        IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) X (adelicAddHaar (𝓞 K) K) →
        IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω₁
          (NumberField.Idele.idelicHaar K) →
        IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω₂
          (NumberField.Idele.idelicHaar K) →
      ∀ F : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable F →
        (∀ β ∈ borelSubgroup K, ∀ g : AdelicGL2 (𝓞 K) K, F (globalPoints (𝓞 K) K β * g) = F g) →
        ∫⁻ x in Φ₀, ∑' ρ : reps, F (globalPoints (𝓞 K) K (ρ : GL (Fin 2) K) * x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          c * ∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
                S₀.indicator F (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
            ∂(adelicAddHaar (𝓞 K) K)) ∧
    (∀ (S₀ : Set (AdelicGL2 (𝓞 K) K)), MeasurableSet S₀ →
        (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), globalPoints (𝓞 K) K γ * g ∈ S₀ ↔ g ∈ S₀) →
      ∀ (Φ₀ : Set (AdelicGL2 (𝓞 K) K)), Φ₀ ⊆ S₀ →
        IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict S₀) →
      ∀ (reps : Set (GL (Fin 2) K)),
        (∀ g : GL (Fin 2) K, ∃! ρ : GL (Fin 2) K, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup K) →
      ∀ (X : Set (AdeleRing (𝓞 K) K)) (Ω₁ Ω₂ : Set (AdeleRing (𝓞 K) K)ˣ),
        IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) X (adelicAddHaar (𝓞 K) K) →
        IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω₁
          (NumberField.Idele.idelicHaar K) →
        IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω₂
          (NumberField.Idele.idelicHaar K) →
      ∀ F : AdelicGL2 (𝓞 K) K → ℂ, Measurable F →
        (∀ β ∈ borelSubgroup K, ∀ g : AdelicGL2 (𝓞 K) K, F (globalPoints (𝓞 K) K β * g) = F g) →
        (∫⁻ x in Φ₀, ∑' ρ : reps, ‖F (globalPoints (𝓞 K) K (ρ : GL (Fin 2) K) * x)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≠ ∞) →
        ∫ x in Φ₀, ∑' ρ : reps, F (globalPoints (𝓞 K) K (ρ : GL (Fin 2) K) * x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          (c.toReal : ℂ) * ∫ x in X, ∫ u in Ω₁, ∫ t in Ω₂, ∫ k,
                S₀.indicator F (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  (((NumberField.TateGlobal.ideleNorm K t)⁻¹ : ℝ) : ℂ)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
            ∂(adelicAddHaar (𝓞 K) K)) := by
  obtain ⟨c, hc0, hctop, hc⟩ := NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa K
  haveI := BorelWord.sigmaFinite_idelicHaar K
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  exact ⟨c, hc0, hctop, fun S₀ hS₀m hS₀ Φ₀ hΦ₀S hΦ₀ reps hreps X Ω₁ Ω₂ hX hΩ₁ hΩ₂ F hFm hF =>
      BorelWord.setLIntegral_tsum_eq K hc0 hc hS₀m hS₀ hΦ₀S hΦ₀ hreps hX hΩ₁ hΩ₂ F hFm hF,
    fun S₀ hS₀m hS₀ Φ₀ hΦ₀S hΦ₀ reps hreps X Ω₁ Ω₂ hX hΩ₁ hΩ₂ F hFm hF habs =>
      BorelWord.setIntegral_tsum_eq K hc0 hc hS₀m hS₀ hΦ₀S hΦ₀ hreps hX hΩ₁ hΩ₂ F hFm hF habs⟩

end IwasawaUnfolding
p2m_reactivate "P2MW.S_UnipotentTermUnfolding_exists_forall_setIntegral_unipotentTerm_eq_mul_integral_iwasawa.BorelWord"

end TwistedUnipotentTerm
p2m_reactivate "P2MW.S_UnipotentTermUnfolding_exists_forall_setIntegral_unipotentTerm_eq_mul_integral_iwasawa.BorelWord"

#print axioms TwistedUnipotentTerm.exists_forall_setLIntegral_tsum_eq_mul_lintegral_iwasawa

end UnfoldingProof
p2m_reactivate "P2MW.S_UnipotentTermUnfolding_exists_forall_setIntegral_unipotentTerm_eq_mul_integral_iwasawa.BorelWord"

section UnfoldGlue

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_UnipotentTermUnfolding_exists_forall_setIntegral_unipotentTerm_eq_mul_integral_iwasawa.AutomorphicForm"
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace UnfoldGlue

private theorem continuous_comp_pair {X W P : Type} [TopologicalSpace X] [TopologicalSpace W] [TopologicalSpace P]
    (F : X → W → ℂ) (hF : Continuous fun q : X × W => F q.1 q.2) (a : P → X) (ha : Continuous a) (e : P → W)
    (he : Continuous e) : Continuous fun p : P => F (a p) (e p) :=
  hF.comp (ha.prodMk he)

private theorem continuous_swap_pair {X Y W : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W]
    (G : Y → X → W) (hG : Continuous fun q : Y × X => G q.1 q.2) : Continuous fun p : X × Y => G p.2 p.1 :=
  hG.comp (continuous_snd.prodMk continuous_fst)

private theorem continuous_comp_mul_triple {X Y Z W : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace W] [Mul X] [ContinuousMul X] (S : X → W) (hS : Continuous S) (U : Z → X)
    (hU : Continuous U) (C : Y → X) (hC : Continuous C) :
    Continuous fun r : (X × Y) × Z => S (U r.2 * (C r.1.2 * r.1.1)) :=
  hS.comp ((hU.comp continuous_snd).mul ((hC.comp (continuous_snd.comp continuous_fst)).mul
    (continuous_fst.comp continuous_fst)))

private theorem countable_gl (L : Type) [Field L] [NumberField L] : Countable (GL (Fin 2) L) := by
  haveI : Countable L := Function.Injective.countable (Module.finBasis ℚ L).equivFun.injective
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Units.val_injective.countable

private theorem finite_normUnipotent_inter_support (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ) (z : (AdeleRing (𝓞 L) L)ˣ) (x : AdelicGL2 (𝓞 L) L) :
    (TwistedBruhat.normUnipotentSet K L σ hgen ∩ Function.support fun δ : GL (Fin 2) L =>
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))).Finite := by
  obtain ⟨Γ, hΓ, hmem⟩ := KernelFoldBounds.exists_finite_forall_ne_zero_mem L hloc φ hφs
    (isCompact_singleton : IsCompact ({x} : Set (AdelicGL2 (𝓞 L) L)))
    (isCompact_singleton : IsCompact
      ({AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)} :
        Set (AdelicGL2 (𝓞 L) L)))
  exact hΓ.subset fun δ hδ => hmem x (Set.mem_singleton x) _ (Set.mem_singleton _) δ hδ.2

private theorem cuspKernel_globalPoints_mul_eq (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (x : AdelicGL2 (𝓞 L) L) (ρ : GL (Fin 2) L) :
    TwistedBruhat.cuspKernel K L D σ hgen φ z (AutomorphicForm.globalPoints (𝓞 L) L ρ * x) =
      ∑ᶠ β ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∩ (AutomorphicForm.borelSubgroup L : Set (GL (Fin 2) L)),
        φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L (ρ⁻¹ * β * Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ) *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) := by
  have hcomm : AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.globalPoints (𝓞 L) L ρ * x) =
      AutomorphicForm.globalPoints (𝓞 L) L ρ * (AutomorphicForm.centralScalar (𝓞 L) L z * x) := by
    rw [← mul_assoc, TwistedBruhat.centralScalar_mul_comm', mul_assoc]
  unfold TwistedBruhat.cuspKernel
  refine finsum_mem_congr rfl fun β _ => ?_
  rw [hcomm, TwistedBruhat.sigmaAdelicAct_globalPoints_mul']
  simp only [map_mul, map_inv, mul_inv_rev]
  congr 1
  group

private theorem finite_support_cuspKernel (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (reps : Set (GL (Fin 2) L)) (hreps : TwistedBruhat.IsCuspTransversal L reps) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφs : HasCompactSupport φ) (z : (AdeleRing (𝓞 L) L)ˣ) (x : AdelicGL2 (𝓞 L) L) :
    (reps ∩ Function.support fun ρ : GL (Fin 2) L =>
      TwistedBruhat.cuspKernel K L D σ hgen φ z (AutomorphicForm.globalPoints (𝓞 L) L ρ * x)).Finite := by
  have hfin := finite_normUnipotent_inter_support K L hloc D σ hgen φ hφs z x
  refine (hfin.image (TwistedBruhat.cuspRep hgen hreps)).subset ?_
  rintro ρ ⟨hρ, hne⟩
  rw [Function.mem_support, cuspKernel_globalPoints_mul_eq] at hne
  obtain ⟨β, hβ, hβne⟩ := exists_ne_zero_of_finsum_mem_ne_zero hne
  refine ⟨ρ⁻¹ * β * Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ, ⟨?_, hβne⟩, ?_⟩
  · exact TwistedBruhat.twistedConj_mem_normUnipotentSet' σ hgen ρ hβ.1
  · refine TwistedBruhat.cuspRep_eq hgen hreps (TwistedBruhat.twistedConj_mem_normUnipotentSet' σ hgen ρ hβ.1) hρ ?_
    have h : ρ * (ρ⁻¹ * β * Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ) *
        (Matrix.GeneralLinearGroup.map (σ : L →+* L) ρ)⁻¹ = β := by group
    rw [h]
    exact hβ.2

private theorem finite_support_cuspTruncation (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L) (Φ₀ : Set (AdelicGL2 (𝓞 L) L)) (R : ℝ)
    (hvan : ∀ x ∈ Φ₀, ∀ γ : GL (Fin 2) L, (γ : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0 →
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ),
        TwistedBruhat.cuspTruncation K L D σ R φ z (AutomorphicForm.globalPoints (𝓞 L) L γ * x) = 0)
    (reps : Set (GL (Fin 2) L)) (hreps : TwistedBruhat.IsCuspTransversal L reps) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (z : (AdeleRing (𝓞 L) L)ˣ) {x : AdelicGL2 (𝓞 L) L} (hx : x ∈ Φ₀) :
    (reps ∩ Function.support fun ρ : GL (Fin 2) L =>
      TwistedBruhat.cuspTruncation K L D σ R φ z (AutomorphicForm.globalPoints (𝓞 L) L ρ * x)).Finite := by
  obtain ⟨ρ₀, ⟨hρ₀, hρ₀B⟩, huniq⟩ := hreps 1
  refine (Set.finite_singleton ρ₀).subset ?_
  rintro ρ ⟨hρ, hne⟩
  rw [Set.mem_singleton_iff]
  by_contra hρρ₀
  apply hne
  apply hvan x hx ρ _ φ z
  intro h10
  exact hρρ₀ (huniq ρ ⟨hρ, by simpa using (AutomorphicForm.borelSubgroup L).inv_mem (show ρ ∈ _ from h10)⟩)

private theorem finsum_sub_eq_tsum (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (Φ₀ : Set (AdelicGL2 (𝓞 L) L)) (R : ℝ)
    (hvan : ∀ x ∈ Φ₀, ∀ γ : GL (Fin 2) L, (γ : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0 →
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ),
        TwistedBruhat.cuspTruncation K L D σ R φ z (AutomorphicForm.globalPoints (𝓞 L) L γ * x) = 0)
    (hper : ∀ reps : Set (GL (Fin 2) L), TwistedBruhat.IsCuspTransversal L reps → ∀ x ∈ Φ₀,
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ),
        TwistedBruhat.cuspTruncation K L D σ R φ z x =
          ∑ᶠ ρ ∈ reps, TwistedBruhat.cuspTruncation K L D σ R φ z (AutomorphicForm.globalPoints (𝓞 L) L ρ * x))
    (reps : Set (GL (Fin 2) L)) (hreps : TwistedBruhat.IsCuspTransversal L reps) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφs : HasCompactSupport φ) (z : (AdeleRing (𝓞 L) L)ˣ) {x : AdelicGL2 (𝓞 L) L} (hx : x ∈ Φ₀) :
    (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        γ ∈ AutomorphicForm.unipotentCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
        φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
      TwistedBruhat.cuspTruncation K L D σ R φ z x =
    ∑' ρ : reps,
      (TwistedBruhat.cuspKernel K L D σ hgen φ z (AutomorphicForm.globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) -
        TwistedBruhat.cuspTruncation K L D σ R φ z
          (AutomorphicForm.globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x)) := by
  rw [TwistedBruhat.finsum_normUnipotent_eq_finsum_cuspKernel K L D σ hgen reps hreps φ z x
    (finite_normUnipotent_inter_support K L hloc D σ hgen φ hφs z x), hper reps hreps x hx φ z]
  have hK : Function.HasFiniteSupport fun ρ : reps =>
      TwistedBruhat.cuspKernel K L D σ hgen φ z (AutomorphicForm.globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) :=
    ((finite_support_cuspKernel K L hloc D σ hgen reps hreps φ hφs z x).preimage
      Subtype.val_injective.injOn).subset fun ρ hρ => ⟨ρ.2, hρ⟩
  have hT : Function.HasFiniteSupport fun ρ : reps =>
      TwistedBruhat.cuspTruncation K L D σ R φ z (AutomorphicForm.globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) :=
    ((finite_support_cuspTruncation K L D σ Φ₀ R hvan reps hreps φ z hx).preimage
      Subtype.val_injective.injOn).subset fun ρ hρ => ⟨ρ.2, hρ⟩
  have hKT : Function.HasFiniteSupport fun ρ : reps =>
      TwistedBruhat.cuspKernel K L D σ hgen φ z (AutomorphicForm.globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) -
        TwistedBruhat.cuspTruncation K L D σ R φ z (AutomorphicForm.globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) :=
    Set.Finite.subset (Set.Finite.union hK hT) (Function.support_sub _ _)
  refine ((tsum_eq_finsum hKT).trans ((finsum_sub_distrib hK hT).trans ?_)).symm
  exact congrArg₂ (· - ·)
    (finsum_set_coe_eq_finsum_mem (f := fun ρ : GL (Fin 2) L =>
      TwistedBruhat.cuspKernel K L D σ hgen φ z (AutomorphicForm.globalPoints (𝓞 L) L ρ * x)) reps)
    (finsum_set_coe_eq_finsum_mem (f := fun ρ : GL (Fin 2) L =>
      TwistedBruhat.cuspTruncation K L D σ R φ z (AutomorphicForm.globalPoints (𝓞 L) L ρ * x)) reps)

private theorem mul_scalar_mem_cuspIndex (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {δ : GL (Fin 2) L}
    (hδ : δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∩ (AutomorphicForm.borelSubgroup L : Set (GL (Fin 2) L)))
    (a : Lˣ) :
    δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈
      TwistedBruhat.normUnipotentSet K L σ hgen ∩ (AutomorphicForm.borelSubgroup L : Set (GL (Fin 2) L)) :=
  ⟨CellScalarStability.mul_scalar_mem_setOf_unipotent hgen hδ.1 a,
    (by
      have h10 : ((δ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := hδ.2
      have hcoe := CellScalarStability.coe_mul_scalar δ a
      show ((δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0
      rw [hcoe, Matrix.smul_apply, h10, smul_zero])⟩

private theorem integrableOn_cusp (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (R : ℝ) (g : AdelicGL2 (𝓞 L) L) :
    IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (TwistedBruhat.cuspKernel K L D σ hgen φ z g - TwistedBruhat.cuspTruncation K L D σ R φ z g)) ΩL νZL := by
  have h1 : IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      TwistedBruhat.cuspKernel K L D σ hgen φ z g) ΩL νZL :=
    KernelFoldAssembly.integrableOn_mul_finsum_mem_of_stable K L D σ νZL ΩL hΩL ξL hξc hξt hloc φ hφc hφs
      (TwistedBruhat.normUnipotentSet K L σ hgen ∩ (AutomorphicForm.borelSubgroup L : Set (GL (Fin 2) L)))
      (fun δ hδ a => mul_scalar_mem_cuspIndex K L σ hgen hδ a) g
  have h2 : IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      TwistedBruhat.cuspTruncation K L D σ R φ z g) ΩL νZL :=
    TruncationFold.integrableOn_mul_indicator_constantTerm_finsum_borelNormOne K L D σ νZL ΩL hΩL ξL hξc hξt hloc φ
      hφc hφs R g
  have h3 : IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
      ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * TwistedBruhat.cuspKernel K L D σ hgen φ z g -
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * TwistedBruhat.cuspTruncation K L D σ R φ z g) ΩL νZL :=
    h1.sub' h2
  simpa only [mul_sub] using h3

private theorem continuous_fold (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (T' : Set (GL (Fin 2) L)) :
    Continuous fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ∑ᶠ δ ∈ T', φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1)) :=
  continuous_comp_pair
    (fun g w : AdelicGL2 (𝓞 L) L => ∑ᶠ δ ∈ T', φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * w))
    (KernelFoldBounds.continuous_finsum_mem L hloc φ hφc hφs T') Prod.fst continuous_fst
    (fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1))
    (continuous_swap_pair
      (fun (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) =>
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * g))
      (KernelFoldBounds.continuous_sigmaAdelicAct_centralScalar_mul K L D σ))

private theorem continuous_truncationIntegrand (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) :
    Continuous fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
      ∑ᶠ δ ∈ TwistedBruhat.borelNormOneSet K L,
        φ (r.1.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ
          (AutomorphicForm.unipotentGL2 r.2 * (AutomorphicForm.centralScalar (𝓞 L) L r.1.2 * r.1.1))) :=
  continuous_comp_pair
    (fun g w : AdelicGL2 (𝓞 L) L =>
      ∑ᶠ δ ∈ TwistedBruhat.borelNormOneSet K L, φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * w))
    (KernelFoldBounds.continuous_finsum_mem L hloc φ hφc hφs (TwistedBruhat.borelNormOneSet K L))
    (fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L => r.1.1)
    (continuous_fst.comp continuous_fst)
    (fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
      AutomorphicForm.sigmaAdelicAct K L D σ
        (AutomorphicForm.unipotentGL2 r.2 * (AutomorphicForm.centralScalar (𝓞 L) L r.1.2 * r.1.1)))
    (continuous_comp_mul_triple (AutomorphicForm.sigmaAdelicAct K L D σ)
      (KernelFoldBounds.continuous_sigmaAdelicAct'' K L D σ)
      (fun q : AdeleRing (𝓞 L) L => (AutomorphicForm.unipotentGL2 q : AdelicGL2 (𝓞 L) L))
      (TruncationFold.continuous_unipotentGL2 (L := L)) (AutomorphicForm.centralScalar (𝓞 L) L)
      (KernelFoldBounds.continuous_centralScalar L))

open Classical in

private theorem cuspTruncation_eq_ite (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    TwistedBruhat.cuspTruncation K L D σ R φ z g =
      if Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.centralScalar (𝓞 L) L z * g) then
        ∫ q, ∑ᶠ δ ∈ TwistedBruhat.borelNormOneSet K L,
          φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.unipotentGL2 q * (AutomorphicForm.centralScalar (𝓞 L) L z * g)))
          ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
      else 0 := by
  unfold TwistedBruhat.cuspTruncation
  rw [Set.indicator_apply]
  rfl

private theorem measurable_foldIntegrand (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (R : ℝ) (T' : Set (GL (Fin 2) L)) :
    Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ T', φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1))) -
        TwistedBruhat.cuspTruncation K L D σ R φ p.2 p.1) := by
  classical
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := IdeleTopology.secondCountableTopology_units_adeleRing L
  haveI : IsFiniteMeasure
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) := inferInstance
  have hξm : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ((ξL ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) := (hξc.comp continuous_snd).measurable
  have hKm : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ∑ᶠ δ ∈ T', φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1)) :=
    (continuous_fold K L D σ hloc φ hφc hφs T').measurable
  have hhigh : MeasurableSet {p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ |
      Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1)} :=
    ((NumberField.AdelicHeight.continuous_adelicHeight L).comp
      (((KernelFoldBounds.continuous_centralScalar L).comp continuous_snd).mul continuous_fst)).measurable
      measurableSet_Ioi
  have hCT : StronglyMeasurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ∫ q, (fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
        ∑ᶠ δ ∈ TwistedBruhat.borelNormOneSet K L,
          φ (r.1.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.unipotentGL2 r.2 * (AutomorphicForm.centralScalar (𝓞 L) L r.1.2 * r.1.1)))) (p, q)
        ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) :=
    (continuous_truncationIntegrand K L D σ hloc φ hφc hφs).stronglyMeasurable.integral_prod_right'
  have hTm : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      TwistedBruhat.cuspTruncation K L D σ R φ p.2 p.1 := by
    simp_rw [cuspTruncation_eq_ite]
    exact Measurable.ite hhigh hCT.measurable measurable_const
  exact hξm.mul (hKm.sub hTm)

private theorem measurable_foldIntegral (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (R : ℝ) (T' : Set (GL (Fin 2) L)) :
    Measurable fun g : AdelicGL2 (𝓞 L) L => ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ T', φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * g))) -
        TwistedBruhat.cuspTruncation K L D σ R φ z g) ∂νZL := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := IdeleTopology.secondCountableTopology_units_adeleRing L
  haveI : SigmaFinite νZL := inferInstance
  exact ((measurable_foldIntegrand K L D σ ξL hξc hloc φ hφc hφs R T').stronglyMeasurable.integral_prod_right'
    (ν := νZL.restrict ΩL)).measurable

private theorem measurable_tsum_lintegral (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (R : ℝ) (reps : Set (GL (Fin 2) L)) :
    Measurable fun x : AdelicGL2 (𝓞 L) L => ∑' ρ : reps, ∫⁻ z in ΩL,
      ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (TwistedBruhat.cuspKernel K L D σ hgen φ z (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) -
          TwistedBruhat.cuspTruncation K L D σ R φ z (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x))‖ₑ ∂νZL := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := IdeleTopology.secondCountableTopology_units_adeleRing L
  haveI : SigmaFinite νZL := inferInstance
  haveI : Countable (GL (Fin 2) L) := countable_gl L
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  refine Measurable.iSup fun s => Finset.measurable_sum s fun ρ _ => ?_
  have hpair : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * p.1, p.2) :=
    ((continuous_const.mul continuous_fst).prodMk continuous_snd).measurable
  have hG : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ‖((ξL ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) *
        (TwistedBruhat.cuspKernel K L D σ hgen φ p.2 (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * p.1) -
          TwistedBruhat.cuspTruncation K L D σ R φ p.2 (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * p.1))‖ₑ :=
    ((measurable_foldIntegrand K L D σ ξL hξc hloc φ hφc hφs R
      (TwistedBruhat.normUnipotentSet K L σ hgen ∩ (AutomorphicForm.borelSubgroup L : Set (GL (Fin 2) L)))).comp
        hpair).enorm
  exact hG.lintegral_prod_right' (ν := νZL.restrict ΩL)

private theorem integral_eq_tsum_cuspIntegral (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L) (Φ₀ : Set (AdelicGL2 (𝓞 L) L)) (R : ℝ)
    (hvan : ∀ x ∈ Φ₀, ∀ γ : GL (Fin 2) L, (γ : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0 →
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ),
        TwistedBruhat.cuspTruncation K L D σ R φ z (AutomorphicForm.globalPoints (𝓞 L) L γ * x) = 0)
    (hper : ∀ reps : Set (GL (Fin 2) L), TwistedBruhat.IsCuspTransversal L reps → ∀ x ∈ Φ₀,
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ),
        TwistedBruhat.cuspTruncation K L D σ R φ z x =
          ∑ᶠ ρ ∈ reps, TwistedBruhat.cuspTruncation K L D σ R φ z (AutomorphicForm.globalPoints (𝓞 L) L ρ * x))
    (reps : Set (GL (Fin 2) L)) (hreps : TwistedBruhat.IsCuspTransversal L reps) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) {x : AdelicGL2 (𝓞 L) L} (hx : x ∈ Φ₀)
    (hfin : (∑' ρ : reps, ∫⁻ z in ΩL,
      ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (TwistedBruhat.cuspKernel K L D σ hgen φ z (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) -
          TwistedBruhat.cuspTruncation K L D σ R φ z (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x))‖ₑ ∂νZL) < ⊤) :
    (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
          γ ∈ AutomorphicForm.unipotentCell K ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        TwistedBruhat.cuspTruncation K L D σ R φ z x) ∂νZL) =
    ∑' ρ : reps, ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (TwistedBruhat.cuspKernel K L D σ hgen φ z (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) -
        TwistedBruhat.cuspTruncation K L D σ R φ z (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x)) ∂νZL := by
  haveI : Countable (GL (Fin 2) L) := countable_gl L
  have hmeas : ∀ ρ : reps, AEStronglyMeasurable (fun z : (AdeleRing (𝓞 L) L)ˣ =>
      ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (TwistedBruhat.cuspKernel K L D σ hgen φ z (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) -
          TwistedBruhat.cuspTruncation K L D σ R φ z (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x)))
      (νZL.restrict ΩL) := fun ρ =>
    (integrableOn_cusp K L νZL ΩL hΩL D σ hgen ξL hξc hξt hloc φ hφc hφs R
      (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x)).integrable.aestronglyMeasurable
  refine Eq.trans ?_ (integral_tsum hmeas hfin.ne)
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  beta_reduce
  rw [tsum_mul_left]
  congr 1
  exact finsum_sub_eq_tsum K L hloc D σ hgen Φ₀ R hvan hper reps hreps φ hφs z hx

private theorem cuspIntegral_globalPoints_mul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (R : ℝ) (b : GL (Fin 2) L)
    (hb : b ∈ AutomorphicForm.borelSubgroup L) (g : AdelicGL2 (𝓞 L) L) :
    ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (TwistedBruhat.cuspKernel K L D σ hgen φ z (globalPoints (𝓞 L) L b * g) -
          TwistedBruhat.cuspTruncation K L D σ R φ z (globalPoints (𝓞 L) L b * g)) ∂νZL =
      ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (TwistedBruhat.cuspKernel K L D σ hgen φ z g - TwistedBruhat.cuspTruncation K L D σ R φ z g) ∂νZL := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  beta_reduce
  rw [TwistedBruhat.cuspKernel_globalPoints_mul K L D σ hgen φ z b hb g,
    TwistedBruhat.cuspTruncation_globalPoints_mul K L D σ R φ z b hb g]

private theorem measurableSet_detShell (L : Type) [Field L] [NumberField L] (α β : ℝ) :
    MeasurableSet {g : AdelicGL2 (𝓞 L) L |
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  exact ((NumberField.TateGlobal.continuous_ideleNorm L).comp (ShellVolume.continuous_det_gl L)).measurable
    measurableSet_Icc

private theorem globalPoints_mul_mem_detShell_iff (L : Type) [Field L] [NumberField L] (α β : ℝ) (γ : GL (Fin 2) L)
    (g : AdelicGL2 (𝓞 L) L) :
    globalPoints (𝓞 L) L γ * g ∈
        {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ↔
      g ∈ {g : AdelicGL2 (𝓞 L) L |
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} := by
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

end UnfoldGlue
p2m_reactivate "P2MW.S_UnipotentTermUnfolding_exists_forall_setIntegral_unipotentTerm_eq_mul_integral_iwasawa.BorelWord"

end UnfoldGlue
p2m_reactivate "P2MW.S_UnipotentTermUnfolding_exists_forall_setIntegral_unipotentTerm_eq_mul_integral_iwasawa.BorelWord"

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (X : Set (AdeleRing (𝓞 L) L)) (Ω₁ Ω₂ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hX : @IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) _ _ _
      (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (hΩ₁ : @IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₁ (NumberField.Idele.idelicHaar L))
    (hΩ₂ : @IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₂ (NumberField.Idele.idelicHaar L)) :
    ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧
    ∀ φ : AdelicGL2 (𝓞 L) L → ℂ, Continuous φ → HasCompactSupport φ →
    ∀ reps : Set (GL (Fin 2) L), TwistedBruhat.IsCuspTransversal L reps →
      (∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R →
      ∫⁻ x in Φ₀, ∑' ρ : reps, ∫⁻ z in ΩL,
          ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (TwistedBruhat.cuspKernel K L D σ hgen φ z (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x) -
              TwistedBruhat.cuspTruncation K L D σ R φ z (globalPoints (𝓞 L) L (ρ : GL (Fin 2) L) * x))‖ₑ ∂νZL
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L) ≠ ⊤) →
      ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R →
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 L) L)
            (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 L) L)
            (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L))
        = (κ.toReal : ℂ) * ∫ x in X, ∫ u in Ω₁, ∫ t in Ω₂, ∫ k,
            Set.indicator
              ({g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :
                Set (AdelicGL2 (𝓞 L) L))
              (fun g : AdelicGL2 (𝓞 L) L => ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                (TwistedBruhat.cuspKernel K L D σ hgen φ z g - TwistedBruhat.cuspTruncation K L D σ R φ z g) ∂νZL)
              (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) := by
  classical
  obtain ⟨κ, hκ0, hκt, -, hb1⟩ := TwistedUnipotentTerm.exists_forall_setLIntegral_tsum_eq_mul_lintegral_iwasawa L
  refine ⟨κ, hκ0, hκt, ?_⟩
  intro φ hφc hφs reps hreps hI
  have hloc : AutomorphicForm.AdelicKernelLocalFiniteness L := AutomorphicForm.adelicKernelLocalFiniteness L
  obtain ⟨R₁a, hR₁a⟩ :=
    TwistedBruhat.exists_forall_cuspTruncation_globalPoints_mul_eq_zero K L D σ c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S
  obtain ⟨R₁b, hR₁b⟩ := TwistedBruhat.exists_forall_cuspTruncation_eq_finsum K L D σ c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S
  obtain ⟨R₁c, hR₁c⟩ := hI
  refine ⟨max (max R₁a R₁b) R₁c, fun R hR => ?_⟩
  have hRa : R₁a ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRb : R₁b ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hRc : R₁c ≤ R := le_trans (le_max_right _ _) hR
  have hIR := hR₁c R hRc

  have hmem : ∀ᵐ x ∂((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀), x ∈ Φ₀ := by
    rw [← Measure.restrict_restrict_of_subset hΦ₀s]
    exact ae_restrict_mem₀ hΦ₀.nullMeasurableSet
  have hfinae := ae_lt_top'
    (UnfoldGlue.measurable_tsum_lintegral K L νZL ΩL D σ hgen ξL hξc hloc φ hφc hφs R reps).aemeasurable hIR
  have hpoint := fun (x : AdelicGL2 (𝓞 L) L) (hx : x ∈ Φ₀) hfin =>
    UnfoldGlue.integral_eq_tsum_cuspIntegral K L νZL ΩL hΩL D σ hgen ξL hξc hξt hloc Φ₀ R (hR₁a R hRa)
      (hR₁b R hRb) reps hreps φ hφc hφs hx hfin
  refine ⟨?int, ?eq⟩
  case int =>
    refine ⟨(UnfoldGlue.measurable_foldIntegral K L νZL ΩL D σ ξL hξc hloc φ hφc hφs R
      {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        γ ∈ AutomorphicForm.unipotentCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
          ConjClasses.mk γ}).aestronglyMeasurable, ?_⟩
    refine hasFiniteIntegral_iff_enorm.2
      (lt_of_le_of_lt (lintegral_mono_ae ((hmem.and hfinae).mono fun x hx => ?_)) hIR.lt_top)
    refine (congrArg (‖·‖ₑ) (hpoint x hx.1 hx.2)).trans_le ?_
    exact enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun ρ => enorm_integral_le_lintegral_enorm _)
  case eq =>
    refine Eq.trans ?_ (hb1 _ (UnfoldGlue.measurableSet_detShell L α β)
      (UnfoldGlue.globalPoints_mul_mem_detShell_iff L α β) Φ₀ hΦ₀s hΦ₀ reps hreps X Ω₁ Ω₂ hX hΩ₁ hΩ₂
      (fun g : AdelicGL2 (𝓞 L) L => ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (TwistedBruhat.cuspKernel K L D σ hgen φ z g - TwistedBruhat.cuspTruncation K L D σ R φ z g) ∂νZL)
      (UnfoldGlue.measurable_foldIntegral K L νZL ΩL D σ ξL hξc hloc φ hφc hφs R
        (TwistedBruhat.normUnipotentSet K L σ hgen ∩ (AutomorphicForm.borelSubgroup L : Set (GL (Fin 2) L))))
      (fun b hb g => UnfoldGlue.cuspIntegral_globalPoints_mul K L νZL ΩL D σ hgen ξL φ R b hb g)
      (ne_top_of_le_ne_top hIR (lintegral_mono fun x => ENNReal.tsum_le_tsum fun ρ =>
        enorm_integral_le_lintegral_enorm _)))
    exact integral_congr_ae ((hmem.and hfinae).mono fun x hx => hpoint x hx.1 hx.2)

#print axioms solution

end S_UnipotentTermUnfolding_exists_forall_setIntegral_unipotentTerm_eq_mul_integral_iwasawa
end P2MW
export P2MW.S_UnipotentTermUnfolding_exists_forall_setIntegral_unipotentTerm_eq_mul_integral_iwasawa (solution)
