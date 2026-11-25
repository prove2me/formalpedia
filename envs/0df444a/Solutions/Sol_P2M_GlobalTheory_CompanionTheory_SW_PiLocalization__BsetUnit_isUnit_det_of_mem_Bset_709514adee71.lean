-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_isUnit_det_of_mem_Bset_709514adee71
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:29:55.477739+00:00
-- url     : https://prove2.me/submissions/21e115d1-1060-4978-8c36-33b9d5348e98

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductInvariance
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_det_eq_corner_mul_012aaa08b2f5
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_half_trace_tmul_6dbb14eaff81
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_corner_mul_inv_40be7c0e982e
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_KAlg_algebra_tensor_invol
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D S hS
  obtain ⟨-, -, -, -, hArt, hRed, -, -⟩ := D.hR
  obtain ⟨-, -, -, -, -, hfix, -⟩ := KAlg.algebra_tensor_invol F E σ D.hCM R
  have hfr : Module.finrank F E = 2 := D.hCM.2.2.1
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b₂ : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hfr
  have hsig : ∀ (p : R) (e : E), sigR R σ (p ⊗ₜ[F] e) = p ⊗ₜ[F] σ e := fun _ _ => rfl
  set T : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E) := S.1 with hT
  have hH : ∀ i j, sigR R σ (T j i) = T i j := S.2
  obtain ⟨x, hx⟩ := hfix (T 0 0) (hH 0 0)
  have hs0 : s0 R T = x := by
    rw [s0, hx]; exact half_trace_tmul two_ne_zero b₂ x
  have hxB : x ∈ B₀ := by
    have h : s0 R T ∈ B₀ := hS.1
    rwa [hs0] at h
  set u : Rˣ := a x with hu
  set p : R ⊗[F] E := ((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹) with hp
  set τ : R ⊗[F] E := inclR R (algebraMap F E t) with hτ
  have hsp : sigR R σ p = p := by rw [hp, hsig, AlgHom.commutes]
  have hsτ : sigR R σ τ = τ := by
    show sigR R σ ((1 : R) ⊗ₜ[F] (algebraMap F E t)) = (1 : R) ⊗ₜ[F] (algebraMap F E t)
    rw [hsig, AlgHom.commutes]
  have hw : T 0 0 * (p * τ * p) = 1 := by
    rw [hx]
    have := corner_mul_inv (E := E) (R := R) D.ht u
    have hq : x = (u : R) ^ 2 * algebraMap F R t := D.hsq x hxB
    rwa [← hq] at this
  have hschur : ∀ i j, schurM R σ t a T i j = T i.succ j.succ - T i.succ 0 * (p * τ * p) * T 0 j.succ := by
    intro i j
    have hc : ∀ k, cvec R t a T k = p * T 0 k.succ := by
      intro k; rw [cvec, hs0]
    simp only [schurM]
    rw [hc, hc, map_mul, hsp, hH]
    ring
  have hmem : schurM R σ t a T ∈ HermR R σ n := by
    intro i j
    rw [hschur, hschur, map_sub, map_mul, map_mul, map_mul, map_mul, hsp, hsτ, hH, hH, hH]
    ring
  have hdet := det_eq_corner_mul T _ hw
  have hU : IsUnit (T 0 0) := IsUnit.of_mul_eq_one _ hw
  have hsch : (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      Matrix.of fun i j : Fin n => T i.succ j.succ - T i.succ 0 * (p * τ * p) * T 0 j.succ := by
    rw [schur_coe R σ t a S hmem]
    ext i j
    exact hschur i j
  have h2 := hS.2
  rw [hsch] at h2
  rw [hdet]
  exact hU.mul h2
end GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit
