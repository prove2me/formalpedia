-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__fibre_scale_modulus_length_one_5c0162a5b56c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:22.10626+00:00
-- url     : https://prove2.me/submissions/19c78863-ed02-4957-8d70-0da43cf9e1f6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarModularCharacterOfContinuousAction
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RankOneFiberMeasureBlockExtension
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__nnreal_eq_of_smul_haar_89aee63d41dc
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__unitTens_coe_14584c718462
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__rmul_sclMat_7f71fd9da8ab
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__cT_sclMat_mul_206826032fcb
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_exists_continuous_modulus_of_continuous_action
import Theorems.Thm_GlobalTheory_T_coordinate_haar_measure
import Theorems.Thm_GlobalTheory_T_gram_fiber_measures_gl_equivariant
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ) (J₁ : Matrix (Fin N) (Fin N) E), IsHermND σ J₁ → ∀ t : F, t ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₁ : HermR R σ 1 → Measure (Fin 1 → Fin N → R ⊗[F] E), IsGramFib R σ J₁ 1 (coordW R b lam 1 N) (coordHerm R σ b lam 1) m₁ → ∃ κ₁ cm : Rˣ → ℝ≥0, Continuous κ₁ ∧ κ₁ 1 = 1 ∧ (∀ u : Rˣ, m₁ (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) = κ₁ u • (m₁ (hermScal R σ (algebraMap F R t))).map (scl ((u : R) ⊗ₜ[F] (1 : E)))) ∧ Continuous cm ∧ (∀ u : Rˣ, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) = cm u • coordK R b lam) ∧ ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → cm 1 = c := by
  intro F E _ _ _ _ _ σ hCM N J₁ hJ t ht R _ _ _ _ _ hR d b lam hlam m₁ hm₁
  have hR0 := hR
  obtain ⟨i1, i2, i3, i4, -⟩ := hR0
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  obtain ⟨k1, k2, k3, k4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := k1
  haveI := k2
  haveI := k3
  haveI := k4
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  haveI := hK
  obtain ⟨κ, hκc, -, hκ1, hκ⟩ :=
    GlobalTheory.T.gram_fiber_measures_gl_equivariant F E σ hCM N J₁ hJ R hR 1 _ _ m₁ (hW 1 N) (hH 1) hm₁
  have hinc : Continuous (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
    have h : Continuous (fun r : R => r • (1 : R ⊗[F] E)) :=
      Continuous.smul (f := fun r : R => r) (g := fun _ => (1 : R ⊗[F] E)) continuous_id
        continuous_const
    refine h.congr fun r => ?_
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hcs : Continuous (sclMat (F := F) (E := E) R) :=
    continuous_pi fun _ => continuous_pi fun _ => hinc
  have hg : Continuous (Units.map (sclMat (F := F) (E := E) R)) := Continuous.units_map _ hcs
  have hu : Continuous (unitTens (F := F) (E := E) R) := Continuous.units_map _ hinc
  obtain ⟨χ, hχc, hχ⟩ := exists_continuous_modulus_of_continuous_action (R ⊗[F] E) (coordK R b lam)
    (R ⊗[F] E)ˣ
  let tU : (R ⊗[F] E)ˣ :=
    Units.map (inclR R : E →+* R ⊗[F] E).toMonoidHom
      (Units.mk0 (algebraMap F E t) ((map_ne_zero _).2 ht))
  have htU : (tU : R ⊗[F] E) = inclR R (algebraMap F E t) := rfl
  have hq : ∀ u : Rˣ, ((unitTens (F := F) (E := E) R u * tU : (R ⊗[F] E)ˣ) : R ⊗[F] E) =
      (u : R) ⊗ₜ[F] (algebraMap F E t) := by
    intro u
    rw [Units.val_mul, unitTens_coe, htU]
    change (u : R) ⊗ₜ[F] (1 : E) * (1 : R) ⊗ₜ[F] (algebraMap F E t) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  refine ⟨fun u => κ (Units.map (sclMat (F := F) (E := E) R) u),
    fun u => χ (unitTens (F := F) (E := E) R u * tU), hκc.comp hg, by simpa using hκ1, ?_,
    hχc.comp (hu.mul continuous_const), ?_, ?_⟩
  · intro u
    have h := hκ (Units.map (sclMat (F := F) (E := E) R) u) (hermScal R σ (algebraMap F R t))
      (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) (cT_sclMat_mul R σ (u : R) _)
    rw [h]
    congr 2
    funext X
    exact rmul_sclMat R X (u : R)
  · intro u
    have e : (fun y : R ⊗[F] E => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) =
        fun v => (unitTens (F := F) (E := E) R u * tU) • v := by
      funext y
      rw [Units.smul_def, smul_eq_mul, hq]
    rw [e]
    exact hχ _
  · intro c hc
    have e : (fun y : R ⊗[F] E => inclR R (algebraMap F E t) * y) = fun v => tU • v := by
      funext y
      rw [Units.smul_def, smul_eq_mul, htU]
    rw [e, hχ tU] at hc
    have := nnreal_eq_of_smul_haar (coordK R b lam) hc
    simpa using this
end GlobalTheory.CompanionTheory.SW.PiLocalization₂
