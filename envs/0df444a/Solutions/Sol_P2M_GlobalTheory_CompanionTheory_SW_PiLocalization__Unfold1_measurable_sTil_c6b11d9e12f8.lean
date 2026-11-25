-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_sTil_c6b11d9e12f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:38:29.34341+00:00
-- url     : https://prove2.me/submissions/a5ca3f06-8205-48b7-82c4-2df59a12d870

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
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_scl_107a1b1645de
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_continuous_tmul_one_a3804b5de181
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_inv_a_8fb4fff192ca
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
theorem _root_.solution (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm) :
    Measurable (sTil σ J t s a) := by
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  obtain ⟨k1, k2, k3, k4, hsigc, htrc, -, hbw, -, hgramc⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hq : Continuous fun y : Fin 1 → Fin (M + 1) → R ⊗[F] E =>
      s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) := by
    unfold s0
    exact continuous_const.mul (htrc.comp ((hgramc 1 (M + 1) _).matrix_elem 0 0))
  have hw : Measurable fun y : Fin 1 → Fin (M + 1) → R ⊗[F] E =>
      (((a (s0 R (gramR R σ (blockOne (algebraMap F E t) J) y)))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E) :=
    (continuous_tmul_one R (F := F) (E := E)).measurable.comp ((measurable_inv_a D).comp hq.measurable)
  exact D.hs.comp (measurable_scl.comp (hw.prodMk measurable_id))
end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1
