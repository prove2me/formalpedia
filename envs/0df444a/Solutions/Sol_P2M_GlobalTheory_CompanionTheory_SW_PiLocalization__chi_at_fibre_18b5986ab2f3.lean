-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__chi_at_fibre_18b5986ab2f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:09:44.584681+00:00
-- url     : https://prove2.me/submissions/e5f5ea11-b11d-41c9-9de1-4721a1a23bab

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductMeasurableStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductFold
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__gramR_scl_tmul_f342e5ccde38
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__corner_half_trace_of_pure_tensor_c407ddf04396
import Theorems.Thm_GlobalTheory_T_adelic_unitary_group_locally_compact
import Theorems.Thm_GlobalTheory_T_block_one_scalar_preserves_nondegenerate
import Theorems.Thm_GlobalTheory_T_gram_block_one_schur_coordinates
import Theorems.Thm_GlobalTheory_T_gram_fiber_measure_locally_finite_measurable_supported
import Theorems.Thm_GlobalTheory_T_hermitian_matrices_locally_compact_borel
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_corner_half_trace_of_pure_tensor_9938135d429c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ x ∈ B₀, ∀ y₀ : Fin 1 → Fin (M + 1) → R ⊗[F] E, gramR R σ (blockOne (algebraMap F E t) J) y₀ = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) = ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S' in Unt σ R n, ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) ∂(m' S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ x hx y₀ hy₀
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id D.hR
  have hJt := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨-, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  obtain ⟨-, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJt R
  obtain ⟨-, -, -, hBH, hliftn⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R n
  obtain ⟨-, -, -, -, hlift⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R (n + 1)
  obtain ⟨hUo, -, hoff, -⟩ := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨g, -, hg⟩ := hlift (M + 1) _ hJt
  have hcoord := (GlobalTheory.T.gram_block_one_schur_coordinates F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D).1 x hx
  have hd : Module.finrank F E = 2 := D.hCM.2.2.1
  set u : R := ((a x : Rˣ) : R) with hu

  have hy00 : gramR R σ (blockOne (algebraMap F E t) J) y₀ 0 0 = algebraMap F R t ⊗ₜ[F] (1 : E) := by
    rw [hy₀]; rfl
  have hG : gramR R σ (blockOne (algebraMap F E t) J) (scl (u ⊗ₜ[F] (1 : E)) y₀) 0 0 =
      x ⊗ₜ[F] (1 : E) := by
    rw [gramR_scl_tmul, hy00, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    have hq : u ^ 2 * algebraMap F R t = x := (D.hsq x hx).symm
    rw [mul_one, mul_one, ← pow_two, hq]
  have hs0 : s0 R (gramR R σ (blockOne (algebraMap F E t) J) (scl (u ⊗ₜ[F] (1 : E)) y₀)) = x :=
    corner_half_trace_of_pure_tensor R b hd x _ hG
  have hsT : sTil σ J t s a (scl (u ⊗ₜ[F] (1 : E)) y₀) = s y₀ := by
    unfold sTil
    rw [hs0]
    congr 1
    funext i j
    simp only [scl, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [hu, Units.mul_inv]
    exact mul_one _
  have hsec := congrFun (D.hsec y₀ hy₀) 0
  have hcons : ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E),
      (Fin.cons (scl (u ⊗ₜ[F] (1 : E)) y₀ 0)
        (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (fun j => Fin.cons (c j) (X j))) :
          Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =
      actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) := by
    intro c X
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have e : (Fin.cons (u ⊗ₜ[F] (1 : E)) (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) =
          (u ⊗ₜ[F] (1 : E)) • (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) := by
        funext k
        refine Fin.cases ?_ (fun l => ?_) k <;> simp
      simp only [Fin.cons_zero, vec, actW, actTup]
      rw [e, Matrix.mulVec_smul]
      simp only [actW, actTup] at hsec
      rw [hsec]
      funext k
      simp [scl, mul_comm]
    · simp [vec, actW, actTup]
  have hmem : ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E),
      actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) ∈
        (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) ↔
      X ∈ {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
    intro c X
    have hinv := (hact (n + 1)).2.2.2 (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X)
    simp only [Uset, Set.mem_preimage, hinv, Set.mem_setOf_eq]
    constructor
    · rintro ⟨S, ⟨-, hSu⟩, hS⟩
      have := (hcoord c X S hS).2.2
      rwa [this] at hSu
    · intro hX
      have h3 := hcoord c X (g (vec (u ⊗ₜ[F] (1 : E)) c X)) (hg _).symm
      refine ⟨g (vec (u ⊗ₜ[F] (1 : E)) c X), ⟨?_, ?_⟩, (hg _).symm⟩
      · rw [h3.1]; exact hx
      · rw [h3.2.2]; exact hX
  haveI := hBor n M
  haveI := hBor (n + 1) (M + 1)
  have hUt : MeasurableSet (Unt σ R n) := hUo.measurableSet
  have hUd : MeasurableSet {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
    obtain ⟨g', hg'c, hg'⟩ := hliftn M J D.hJ
    have e : {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} = g' ⁻¹' Unt σ R n := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Unt, hg' X]
    rw [e]
    exact (hUo.preimage hg'c).measurableSet
  have hψ : ∀ c : Fin n → R ⊗[F] E, Measurable fun X : Fin n → Fin M → R ⊗[F] E =>
      φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X)) := by
    intro c
    have hv : Continuous fun X : Fin n → Fin M → R ⊗[F] E => vec (u ⊗ₜ[F] (1 : E)) c X := by
      refine continuous_pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · exact continuous_const
      · refine continuous_pi fun k => ?_
        refine Fin.cases ?_ (fun l => ?_) k
        · exact continuous_const
        · exact (continuous_apply l).comp (continuous_apply j)
    have hc : Continuous fun X : Fin n → Fin M → R ⊗[F] E =>
        actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) :=
      (hact (n + 1)).1.comp (continuous_const.prodMk hv)
    exact hφ.comp hc.measurable
  unfold chi
  rw [hsT]
  refine lintegral_congr fun c => ?_
  calc _ = ∫⁻ X : Fin n → Fin M → R ⊗[F] E,
        {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det}.indicator (fun X =>
          φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X))) X
        ∂(coordW R b lam n M) := by
        refine lintegral_congr fun X => ?_
        rw [hcons c X]
        by_cases h : X ∈ {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det}
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem c X).2 h)]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hmem c X).1 h'))]
    _ = ∫⁻ X in {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det},
          φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X))
        ∂(coordW R b lam n M) := lintegral_indicator hUd _
    _ = ∫⁻ S', ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀)
            (vec (u ⊗ₜ[F] (1 : E)) c X)) ∂(m' S') ∂(coordHerm R σ b lam n) :=
        D.hm'.2.1 _ (hψ c)
    _ = _ := by
        rw [← lintegral_indicator hUt]
        refine lintegral_congr fun S' => ?_
        by_cases h : S' ∈ Unt σ R n
        · rw [Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h, hoff S' h, lintegral_zero_measure]
end GlobalTheory.CompanionTheory.SW.PiLocalization₂
