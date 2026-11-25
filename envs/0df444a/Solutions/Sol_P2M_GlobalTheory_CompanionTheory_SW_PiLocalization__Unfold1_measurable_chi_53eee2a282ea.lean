-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_chi_53eee2a282ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:15:34.332466+00:00
-- url     : https://prove2.me/submissions/327f1648-1cec-4cd0-914c-72d934f5784e

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
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_fin_cons_fc68d0337b48
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_sTil_c6b11d9e12f8
import Theorems.Thm_GlobalTheory_T_adelic_unitary_group_locally_compact
import Theorems.Thm_GlobalTheory_T_block_one_scalar_preserves_nondegenerate
import Theorems.Thm_GlobalTheory_T_coordinate_haar_measure
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
theorem _root_.solution (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    {φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable (chi σ J t s a b lam φ) := by
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  obtain ⟨k1, k2, k3, k4, -, -, -, hbw, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨h1, h2, h3, h4, h5, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  have hact' := (hact n).1.measurable
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ D.hCM R d b lam D.hlam
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  haveI : SigmaFinite (coordW R b lam n M) := by unfold coordW; infer_instance
  have hG : Measurable fun q : ((Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → R ⊗[F] E)) ×
      (Fin n → Fin M → R ⊗[F] E) =>
      φ (Fin.cons (q.1.1 0) (actW R σ (blockOne (algebraMap F E t) J) (sTil σ J t s a q.1.1)
        (fun j => Fin.cons (q.1.2 j) (q.2 j)))) := by
    refine hφ.comp (measurable_fin_cons ?_ ?_)
    · exact measurable_pi_iff.1 (measurable_fst.comp measurable_fst) 0
    · refine hact'.comp (((measurable_sTil D).comp (measurable_fst.comp measurable_fst)).prodMk ?_)
      refine measurable_pi_iff.2 fun j => measurable_fin_cons ?_ ?_
      · exact measurable_pi_iff.1 (measurable_snd.comp measurable_fst) j
      · exact measurable_pi_iff.1 measurable_snd j
  exact (hG.lintegral_prod_right' (ν := coordW R b lam n M)).lintegral_prod_right'
    (ν := Measure.pi fun _ : Fin n => coordK R b lam)
end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1
