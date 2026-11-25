-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_isUnit_gram_2d7d21b9dd7f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:19:49.909257+00:00
-- url     : https://prove2.me/submissions/b0bb0157-211f-47a3-b577-41daeb77f61b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureOrthogonalExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousHermScal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductIntegralStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductUnfold
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_isUnit_tmul_one_4ffcade0a0df
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_hermScal_main
import Theorems.Thm_GlobalTheory_T_block_one_scalar_preserves_nondegenerate
import Theorems.Thm_GlobalTheory_T_hermitian_matrices_locally_compact_borel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {t : F} {n : ℕ}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
  {d : ℕ} {b : Module.Basis (Fin d) F E} {lam : Measure R}
  {m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)}
  {m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)}
  {s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)}
  {B₀ : Set R} {a : R → Rˣ} {κ₁ cm : Rˣ → ℝ≥0}
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1
theorem _root_.solution (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    {y : Fin 1 → Fin (M + 1) → R ⊗[F] E}
    (hy : s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) ∈ B₀) :
    IsUnit (gramR R σ (blockOne (algebraMap F E t) J) y).det := by
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨-, -, -, -, hg⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R 1
  obtain ⟨g, -, hg⟩ := hg (M + 1) _ hJ'
  obtain ⟨-, hh, -⟩ := hermScal_main F E σ D.hCM R d b
  have hS := hh (g y)
  rw [← hg y] at hS
  have hx : IsUnit (s0 R (gramR R σ (blockOne (algebraMap F E t) J) y)) := by
    rw [D.hsq _ hy]
    exact ((Units.isUnit _).pow 2).mul ((IsUnit.mk0 t D.ht).map (algebraMap F R))
  have h00 : gramR R σ (blockOne (algebraMap F E t) J) y 0 0 =
      s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) ⊗ₜ[F] (1 : E) := by
    have := congrArg (fun S : HermR R σ 1 => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) hS
    simp only [← hg y] at this
    simpa [hermScal, s0] using this.symm
  rw [Matrix.det_fin_one, h00]
  exact isUnit_tmul_one R hx
end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1
