-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Coord_coords_7539cd3187dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:29:57.401735+00:00
-- url     : https://prove2.me/submissions/a9887732-9da5-4e92-9646-7a91f7f9192a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductIntegral
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Coord_schurM_mem_0a609de872e7
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_KAlg_algebra_tensor_invol
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring
import Theorems.Thm_GlobalTheory_T_units_open_embedding_local_tensor
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__schur_coe_f974b9be1078


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → Continuous (fun S : HermR R σ (n + 1) => s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) ∧ ContinuousOn (fun S : HermR R σ (n + 1) => (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ ContinuousOn (fun S : HermR R σ (n + 1) => cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ ContinuousOn (fun S : HermR R σ (n + 1) => schur R σ t a S) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ IsOpen (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨hTR, hLC, hSC, hT2, hAr, hRed, hUR, -⟩ := D.hR
  have hK := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  obtain ⟨hKR, -, -, -, hsig, htr, -⟩ := hK
  have hinv := (GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol F E σ D.hCM R).2.2.2.1
  have hopenU := GlobalTheory.T.units_open_embedding_local_tensor F E σ D.hCM R D.hR

  have hs0 : Continuous (fun S : HermR R σ (n + 1) =>
      s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) := by
    unfold s0
    have h1 : Continuous (fun S : HermR R σ (n + 1) =>
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0) :=
      (continuous_apply_apply 0 0).comp continuous_subtype_val
    exact continuous_const.mul (htr.comp h1)
  have hA : IsOpen {S : HermR R σ (n + 1) |
      s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := D.hB₀.preimage hs0
  have ha : ContinuousOn (fun S : HermR R σ (n + 1) =>
      a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
    D.hac.comp hs0.continuousOn (fun S hS => hS)

  have hleft : Continuous (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    have : (fun r : R => r ⊗ₜ[F] (1 : E)) = fun r : R => r • (1 : R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    rw [this]
    exact (continuous_id (X := R)).smul (continuous_const (y := (1 : R ⊗[F] E)))
  have hc : ContinuousOn (fun S : HermR R σ (n + 1) =>
      cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := by
    refine continuousOn_pi.2 fun j => ?_
    have hent : Continuous (fun S : HermR R σ (n + 1) =>
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ) :=
      (continuous_apply_apply 0 j.succ).comp continuous_subtype_val
    have hu : ContinuousOn (fun S : HermR R σ (n + 1) =>
        ((((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))⁻¹ : Rˣ) : R)))
        {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
      (Units.continuous_val (M := R)).comp_continuousOn ha.inv
    have hfac : (fun S : HermR R σ (n + 1) =>
        cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) j) =
        fun S : HermR R σ (n + 1) =>
        (((((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E)) *
          ((1 : R) ⊗ₜ[F] (algebraMap F E t⁻¹))) *
          (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ := by
      funext S
      simp [cvec, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hfac]
    exact ((hleft.comp_continuousOn hu).mul continuousOn_const).mul hent.continuousOn

  have hM : ContinuousOn (fun S : HermR R σ (n + 1) =>
      schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    have hent : Continuous (fun S : HermR R σ (n + 1) =>
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ) :=
      (continuous_apply_apply i.succ j.succ).comp continuous_subtype_val
    have hci := (continuous_apply i).comp_continuousOn hc
    have hcj := (continuous_apply j).comp_continuousOn hc
    exact hent.continuousOn.sub (((hsig.comp_continuousOn hci).mul continuousOn_const).mul hcj)
  have hsc : ∀ S : HermR R σ (n + 1),
      (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
        schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) :=
    fun S => schur_coe R σ t a S (schurM_mem R σ hinv t a S)
  have hcoe : ContinuousOn (fun S : HermR R σ (n + 1) =>
      (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := by
    simpa only [hsc] using hM
  have hschur : ContinuousOn (fun S : HermR R σ (n + 1) => schur R σ t a S)
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
    (Topology.IsInducing.subtypeVal.continuousOn_iff).2 hcoe
  refine ⟨hs0, ha, hc, hschur, ?_⟩

  have hdet : ContinuousOn (fun S : HermR R σ (n + 1) =>
      (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det)
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
    (continuous_id.matrix_det).comp_continuousOn hcoe
  have hU : IsOpen {y : R ⊗[F] E | IsUnit y} := by
    have : {y : R ⊗[F] E | IsUnit y} = Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext y; simp [IsUnit]
    rw [this]
    exact hopenU.isOpen_range
  have := hdet.isOpen_inter_preimage hA hU
  exact this
end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord
