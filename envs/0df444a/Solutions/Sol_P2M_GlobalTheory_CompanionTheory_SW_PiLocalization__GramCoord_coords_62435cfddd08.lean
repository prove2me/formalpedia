-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_coords_62435cfddd08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:42:40.994647+00:00
-- url     : https://prove2.me/submissions/9bbe7457-fcd8-4701-9a6a-b5a2507ecca5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramBlockOneFirstVectorFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductMeasurable
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_corner_half_trace_of_pure_tensor_9938135d429c
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_gram_symm_862d9e99a9ef
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_schurM_mem_f18186865e22
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_unit_tmul_7668c6c4ee16
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_KAlg_algebra_tensor_invol
import Theorems.Thm_GlobalTheory_T_block_one_scalar_preserves_nondegenerate
import Theorems.Thm_GlobalTheory_T_gram_block_one_first_vector_formula
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__schur_coe_f974b9be1078


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → (∀ x ∈ B₀, ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) (S : HermR R σ (n + 1)), (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = gramR R σ (blockOne (algebraMap F E t) J) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X) → s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = x ∧ cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = c ∧ (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = gramR R σ J X) ∧ (∀ (S : HermR R σ (n + 1)) (X : Fin n → Fin M → R ⊗[F] E), s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀ → gramR R σ J X = (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) → gramR R σ (blockOne (algebraMap F E t) J) (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) ⊗ₜ[F] (1 : E)) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X) = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨-, -, -, -, hart, hred, -⟩ := D.hR
  haveI := hart
  haveI := hred
  obtain ⟨-, -, -, hinv, -, hfix, -⟩ := GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol F E σ D.hCM R
  have hfr : Module.finrank F E = 2 := D.hCM.2.2.1
  have ht : t ≠ 0 := D.ht
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t ht
  refine ⟨?_, ?_⟩
  · intro x hx c X S hS
    obtain ⟨h00, h0j, hij⟩ := GlobalTheory.T.gram_block_one_first_vector_formula F E σ M J t n R ((a x : Rˣ) : R) c X
    rw [← hS] at h00 h0j hij
    have hx0 : (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0 = x ⊗ₜ[F] (1 : E) := by
      rw [h00, ← D.hsq x hx]
    have hs0 := corner_half_trace_of_pure_tensor R hfr _ x hx0
    have hc : cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = c := by
      funext j
      simp only [cvec]
      rw [hs0, h0j j, ← mul_assoc, unit_tmul ht, one_mul]
    refine ⟨hs0, hc, ?_⟩
    rw [schur_coe R σ t a S (schurM_mem R σ hinv t a S)]
    ext i j
    simp only [schurM]
    rw [hc, hij i j, add_sub_cancel_left]
  · intro S X hB hX
    obtain ⟨h00, h0j, hij⟩ := GlobalTheory.T.gram_block_one_first_vector_formula F E σ M J t n R
      ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R)
      (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X
    have hH := gram_symm R σ hinv hJ'.1 (vec
      (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
      (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X)
    obtain ⟨r, hr⟩ := hfix ((S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0) (S.2 0 0)
    have hsr := corner_half_trace_of_pure_tensor R hfr _ r hr
    have hrow : ∀ j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec
        (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
        (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X) 0 j.succ =
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ := by
      intro j
      rw [h0j j]
      simp only [cvec]
      rw [← mul_assoc, mul_comm (_ ⊗ₜ[F] (algebraMap F E t)), unit_tmul ht, one_mul]
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [h00, hr, ← D.hsq _ hB, hsr]
      · exact hrow j
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [← hH i.succ 0, hrow i]
        exact S.2 i.succ 0
      · rw [hij i j, congrFun (congrFun hX i) j, schur_coe R σ t a S (schurM_mem R σ hinv t a S)]
        simp only [schurM]
        rw [add_sub_cancel]
end GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord
