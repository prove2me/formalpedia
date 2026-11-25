-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__integrable_fibS_and_integral_94f51a3d34ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:41:47.559495+00:00
-- url     : https://prove2.me/submissions/c86c9892-cd98-4bdc-b71c-d47846e05761

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductScaling
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__integrable_map_prod_of_compact_4f664ae6111b
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__vec_zero_2aa2babec28f
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__continuous_vec_8c5d52ef9dc7
import Theorems.Thm_GlobalTheory_T_adelic_unitary_group_locally_compact
import Theorems.Thm_GlobalTheory_T_block_one_scalar_preserves_nondegenerate
import Theorems.Thm_GlobalTheory_T_gram_fiber_measure_locally_finite_measurable_supported
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), Integrable φ (fibS σ J t m₁ m' s B₀ a κ₁ cm S) ∧ ∫ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) = ((κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) * cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n : ℝ≥0) : ℝ) * Preal σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm hD φ hφ hcs S hS
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := hD.hR
  have := hTR
  have := hLC
  have := hSC
  have := hT2
  obtain ⟨hKr, hKlc, hKsc, hKt2, -, -, -, hBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hD.hCM R
  have := hKr
  have := hKlc
  have := hKsc
  have := hKt2
  have hB1 : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := hBor 1 (M + 1)
  have hB2 : BorelSpace (Fin n → Fin M → R ⊗[F] E) := hBor n M
  have hB3 : BorelSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := hBor (n + 1) (M + 1)
  have hJ₁ := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J hD.hJ t hD.ht
  obtain ⟨hTG, -, hHsc, hHt2, hHB, hact⟩ :=
    GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hD.hCM (M + 1) (blockOne (algebraMap F E t) J) hJ₁ R
  have := hTG
  have := hHsc
  have := hHt2
  have := hHB
  obtain ⟨hcont, hone, hmul, -⟩ := hact (n + 1)
  have k1 := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ hD.hCM (M + 1) 1 (blockOne (algebraMap F E t) J) hJ₁ R hD.hR d b lam
    hD.hlam m₁ hD.hm₁
  have k2 := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ hD.hCM M n J hD.hJ R hD.hR d b lam hD.hlam m' hD.hm'
  obtain ⟨-, hlf₁, -, -, -, hgram⟩ := k1
  obtain ⟨-, hlf₂, -, -, -, -⟩ := k2
  set α : Rˣ := a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) with hα
  set c := cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) with hc
  set S' := schur R σ t a S with hS'
  set μ₁ := m₁ (hermScal R σ (algebraMap F R t)) with hμ₁
  set u : R ⊗[F] E := (α : R) ⊗ₜ[F] (1 : E) with hu
  set u' : R ⊗[F] E := ((α⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E) with hu'
  have huu : u * u' = 1 := by
    simp [hu, hu', Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def]
  have := hlf₁ (hermScal R σ (algebraMap F R t))
  have := hlf₂ S'
  let f : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) →
      Fin (n + 1) → Fin (M + 1) → R ⊗[F] E :=
    fun p => actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec u c p.2)
  have hfm : Measurable f :=
    hcont.measurable.comp ((hD.hs.comp measurable_fst).prodMk
      ((continuous_vec u c).measurable.comp measurable_snd))
  have hfib : fibS σ J t m₁ m' s B₀ a κ₁ cm S = (κ₁ α * cm α ^ n) • (μ₁.prod (m' S')).map f := by
    unfold fibS
    rw [Set.indicator_of_mem hS]
  set C := tsupport φ with hC
  have hCc : IsCompact C := hcs
  let e₁ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → Fin 1 → Fin (M + 1) → R ⊗[F] E :=
    fun Z _ i => Z 0 i * u'
  have he₁ : Continuous e₁ := by
    refine continuous_pi fun _ => continuous_pi fun i => ?_
    exact (continuous_apply_apply (0 : Fin (n + 1)) i).mul continuous_const
  have hC₁ : IsCompact (e₁ '' C) := hCc.image he₁
  obtain ⟨C', hC'c, hC'⟩ := hD.hcpt (e₁ '' C) hC₁
  let e₂ : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) →
      Fin (n + 1) → Fin (M + 1) → R ⊗[F] E :=
    fun q => actW R σ (blockOne (algebraMap F E t) J) q.1⁻¹ q.2
  have he₂ : Continuous e₂ := hcont.comp ((continuous_fst.inv).prodMk continuous_snd)
  let e₃ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → Fin n → Fin M → R ⊗[F] E :=
    fun Z j i => Z j.succ i.succ
  have he₃ : Continuous e₃ := by
    refine continuous_pi fun j => continuous_pi fun i => ?_
    exact continuous_apply_apply j.succ i.succ
  have hC₂ : IsCompact (e₃ '' (e₂ '' (C' ×ˢ C))) := ((hC'c.prod hCc).image he₂).image he₃
  have hsupp : ∀ᵐ y ∂μ₁, ∀ X, φ (f (y, X)) ≠ 0 → y ∈ e₁ '' C ∧ X ∈ e₃ '' (e₂ '' (C' ×ˢ C)) := by
    filter_upwards [hgram (hermScal R σ (algebraMap F R t))] with y hy X hne
    have hZ : f (y, X) ∈ C := subset_tsupport _ hne
    have hy0 : e₁ (f (y, X)) = y := by
      have h1 := hD.hsec y hy
      funext i j
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      have h2 : (f (y, X)) 0 = u • y 0 := by
        conv_rhs => rw [← h1]
        simp only [f, actW, actTup, vec_zero, Matrix.mulVec_smul]
      simp only [e₁, h2, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm u, mul_assoc, huu, mul_one]
    have hy1 : y ∈ e₁ '' C := ⟨_, hZ, hy0⟩
    have hsy : s y ∈ C' := hC' y hy1 hy
    have hv : e₂ (s y, f (y, X)) = vec u c X := by
      simp only [e₂, f]
      rw [← hmul, inv_mul_cancel, hone]
    refine ⟨hy1, vec u c X, ⟨(s y, f (y, X)), ⟨hsy, hZ⟩, hv⟩, ?_⟩
    funext j i
    simp [e₃, vec]
  rw [hfib]
  exact integrable_map_prod_of_compact μ₁ (m' S') f hfm φ hφ hcs _ _ hC₁ hC₂ hsupp _
end GlobalTheory.CompanionTheory.SW.PiLocalization₂
