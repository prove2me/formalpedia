-- Prove2me | solution 1 for WHAdditivity.Renyi.single_channel_value
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:22:13.331916+00:00
-- url     : https://prove2.me/submissions/08a33220-dfad-4d24-abf9-688030585856

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

open WHAdditivity.Renyi Matrix
open scoped ComplexOrder

lemma trace_cfc_herm {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp [Function.comp_def]

lemma traceRpow_eq {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (p : ℝ) :
    traceRpow p A = ∑ i, hA.eigenvalues i ^ p := by
  unfold traceRpow; rw [trace_cfc_herm hA]
  rw [Complex.re_sum]; simp

lemma vN_eq {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) :
    vonNeumannEntropy A = ∑ i, Real.negMulLog (hA.eigenvalues i) := by
  unfold vonNeumannEntropy; rw [trace_cfc_herm hA]
  rw [Complex.re_sum]; simp

/-- Real-analytic core: probability vector λ. -/

lemma trace_cfc_of_idem {ι : Type} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (c : ℝ) (hc : c ≠ 0) (hBB : B * B = (c : ℂ) • B) (f : ℝ → ℝ)
    (hf : f 0 = 0) :
    (cfc f B).trace = ((f c / c : ℝ) : ℂ) * B.trace := by
  rw [trace_cfc_herm hB, hB.trace_eq_sum_eigenvalues, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  set l := hB.eigenvalues i
  have hv : (⇑(hB.eigenvectorBasis i) : ι → ℂ) ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 <| hB.eigenvectorBasis.orthonormal.ne_zero i
  have hev := hB.mulVec_eigenvectorBasis i
  have h2 : B *ᵥ (B *ᵥ ⇑(hB.eigenvectorBasis i)) = (c : ℂ) • (B *ᵥ ⇑(hB.eigenvectorBasis i)) := by
    rw [Matrix.mulVec_mulVec, hBB, Matrix.smul_mulVec]
  rw [hev, Matrix.mulVec_smul, hev, smul_smul] at h2
  have h3 : (l * l) • (⇑(hB.eigenvectorBasis i) : ι → ℂ) = (c * l) • ⇑(hB.eigenvectorBasis i) := by
    rw [h2, ← smul_smul]; rw [Complex.coe_smul]
  have h4 : l * l = c * l := smul_left_injective ℝ hv h3
  have : l = 0 ∨ l = c := by
    rcases mul_eq_mul_right_iff.mp h4 with h | h
    · right; exact h
    · left; exact h
  rcases this with h | h
  · rw [h, hf]; simp
  · rw [h]
    have : ((f c / c : ℝ) : ℂ) * (c:ℂ) = f c := by rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hc]
    exact this.symm

lemma pureState_trace {ι : Type} [Fintype ι] (φ : ι → ℂ) (hφ : IsUnitVector φ) :
    (pureState φ).trace = 1 := by
  unfold pureState IsUnitVector at *
  simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.star_apply]
  have : ∀ i, φ i * star (φ i) = ((Complex.normSq (φ i) : ℝ) : ℂ) := fun i => Complex.mul_conj _
  simp_rw [this]; rw [← Complex.ofReal_sum, hφ]; simp

lemma pureState_herm {ι : Type} [Fintype ι] (φ : ι → ℂ) : (pureState φ).IsHermitian := by
  unfold pureState; ext i j
  simp [Matrix.vecMulVec_apply, mul_comm]

lemma pureState_idem {ι : Type} [Fintype ι] (φ : ι → ℂ) (hφ : IsUnitVector φ) :
    pureState φ * pureState φ = pureState φ := by
  have ht := pureState_trace φ hφ
  unfold pureState at *
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
  simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply] at ht
  calc ∑ k, φ i * star φ k * (φ k * star φ j) = φ i * star φ j * ∑ k, φ k * star φ k := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    _ = _ := by rw [ht, mul_one]

lemma unit_star {ι : Type} [Fintype ι] (φ : ι → ℂ) (hφ : IsUnitVector φ) :
    IsUnitVector (star φ) := by
  unfold IsUnitVector at *; simpa using hφ

lemma wh_pure (d : ℕ) (φ : Fin d → ℂ) (hφ : IsUnitVector φ) :
    wernerHolevo d (pureState φ) = ((d : ℂ) - 1)⁻¹ • (1 - pureState (star φ)) := by
  unfold wernerHolevo
  rw [pureState_trace φ hφ, one_smul]
  congr 2
  ext i j; simp [pureState, Matrix.vecMulVec_apply, mul_comm]

lemma renyi_scaled_proj (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 1 ≤ p) (ψ : Fin d → ℂ)
    (hψ : IsUnitVector ψ) :
    renyiEntropy p (((d : ℂ) - 1)⁻¹ • (1 - pureState ψ)) = Real.log ((d : ℝ) - 1) := by
  set c : ℝ := ((d : ℝ) - 1)⁻¹ with hc
  have hd1 : (1:ℝ) ≤ (d:ℝ) - 1 := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcpos : 0 < c := by rw [hc]; apply inv_pos.mpr; linarith
  have hcC : ((d : ℂ) - 1)⁻¹ = (c : ℂ) := by rw [hc]; push_cast; rfl
  rw [hcC]
  set B := (c : ℂ) • (1 - pureState ψ) with hB
  have hP := pureState_idem ψ hψ
  have hBH : B.IsHermitian := by
    have h1 := (Matrix.isHermitian_one (n := Fin d) (α := ℂ)).sub (pureState_herm ψ)
    rw [hB, Matrix.IsHermitian, Matrix.conjTranspose_smul, h1.eq]; simp
  have hBB : B * B = (c : ℂ) • B := by
    rw [hB, smul_mul_smul_comm, sub_mul, mul_sub, mul_sub, hP, smul_smul]; simp
  have htr : B.trace = 1 := by
    rw [hB, Matrix.trace_smul, Matrix.trace_sub, pureState_trace ψ hψ, Matrix.trace_one]
    simp only [Fintype.card_fin, smul_eq_mul]
    rw [hc]; push_cast
    have : (d:ℂ) - 1 ≠ 0 := by
      have : ((d:ℝ) - 1 : ℝ) ≠ 0 := by linarith
      exact_mod_cast this
    field_simp
  have hlogc : Real.log c = -Real.log ((d:ℝ) - 1) := by rw [hc, Real.log_inv]
  unfold renyiEntropy
  split_ifs with h1
  · unfold vonNeumannEntropy
    rw [trace_cfc_of_idem hBH c hcpos.ne' hBB _ (Real.negMulLog_zero), htr, mul_one]
    simp only [Complex.ofReal_re]
    rw [Real.negMulLog, hlogc]; field_simp
  · unfold traceRpow
    rw [trace_cfc_of_idem hBH c hcpos.ne' hBB (fun x => x ^ p) (Real.zero_rpow (by intro h; apply h1; linarith)), htr, mul_one]
    simp only [Complex.ofReal_re]
    have : c ^ p / c = c ^ (p - 1) := by
      rw [Real.rpow_sub hcpos, Real.rpow_one]
    rw [this, Real.log_rpow hcpos, hlogc]
    have : (1 - p) ≠ 0 := by intro h; apply h1; linarith
    field_simp; ring

lemma outputEntropies_wh (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 1 ≤ p) :
    outputEntropies p (wernerHolevo d) = {Real.log ((d : ℝ) - 1)} := by
  ext s
  simp only [outputEntropies, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    rw [wh_pure d φ hφ]; exact renyi_scaled_proj d hd p hp _ (unit_star φ hφ)
  · rintro rfl
    have h0 : 0 < d := by omega
    refine ⟨Pi.single ⟨0, h0⟩ 1, ?_, ?_⟩
    · unfold IsUnitVector
      rw [Finset.sum_eq_single ⟨0, h0⟩]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
    · have hu : IsUnitVector (Pi.single (⟨0, h0⟩ : Fin d) (1:ℂ)) := by
        unfold IsUnitVector
        rw [Finset.sum_eq_single ⟨0, h0⟩]
        · simp
        · intro b _ hb; simp [Pi.single_apply, hb]
        · simp
      rw [wh_pure d _ hu]; exact (renyi_scaled_proj d hd p hp _ (unit_star _ hu)).symm

theorem solution (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 1 ≤ p) :
    (∀ φ : Fin d → ℂ, IsUnitVector φ →
      wernerHolevo d (pureState φ) = ((d : ℂ) - 1)⁻¹ • (1 - pureState (star φ))) ∧
    (∀ φ : Fin d → ℂ, IsUnitVector φ →
      renyiEntropy p (wernerHolevo d (pureState φ)) = Real.log ((d : ℝ) - 1)) ∧
    BddBelow (outputEntropies p (wernerHolevo d)) ∧
    minOutputEntropy p (wernerHolevo d) = Real.log ((d : ℝ) - 1) := by
  refine ⟨fun φ hφ => wh_pure d φ hφ, fun φ hφ => ?_, ?_, ?_⟩
  · rw [wh_pure d φ hφ]; exact renyi_scaled_proj d hd p hp _ (unit_star φ hφ)
  · rw [outputEntropies_wh d hd p hp]; exact bddBelow_singleton
  · unfold minOutputEntropy; rw [outputEntropies_wh d hd p hp, csInf_singleton]
