-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.pure_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T14:00:40.562729+00:00
-- url     : https://prove2.me/submissions/bd140964-42ac-40d9-8a26-7a042f036f49

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

open Matrix

theorem x8_complete [Nonempty A] (T : UnitaryBasis A K) (i j l m : A) :
    ∑ k, T.matrix k i j * star (T.matrix k l m) =
      if (i, j) = (l, m) then (Fintype.card A : ℂ) else 0 := by
  have hcard : Fintype.card K = Fintype.card (A × A) := by
    rw [T.cardinality, Fintype.card_prod, sq]
  let e : K ≃ A × A := Fintype.equivOfCardEq hcard
  obtain ⟨W, hW⟩ : ∃ W : Matrix (A × A) (A × A) ℂ, ∀ p q, W p q = T.matrix (e.symm q) p.1 p.2 :=
    ⟨Matrix.of fun p q => T.matrix (e.symm q) p.1 p.2, fun _ _ => rfl⟩
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hWW : Wᴴ * W = (Fintype.card A : ℂ) • 1 := by
    ext q q'
    have := T.orthogonal (e.symm q) (e.symm q')
    simp only [trace, diag, mul_apply, conjTranspose_apply] at this
    rw [mul_apply, Matrix.smul_apply, one_apply]
    simp only [conjTranspose_apply, hW, Fintype.sum_prod_type]
    rw [Finset.sum_comm] at this
    rw [this]
    by_cases h : q = q' <;> simp [h, e.symm.injective.eq_iff]
  have h1 : ((Fintype.card A : ℂ)⁻¹ • Wᴴ) * W = 1 := by
    rw [smul_mul_assoc, hWW, smul_smul, inv_mul_cancel₀ hd, one_smul]
  have h2 := mul_eq_one_comm.1 h1
  rw [mul_smul_comm] at h2
  have h3 : W * Wᴴ = (Fintype.card A : ℂ) • 1 := by
    have := congrArg (fun M => (Fintype.card A : ℂ) • M) h2
    simp only [smul_smul, mul_inv_cancel₀ hd, one_smul] at this
    exact this
  have := congrFun (congrFun h3 (i, j)) (l, m)
  rw [mul_apply, Matrix.smul_apply, one_apply] at this
  simp only [conjTranspose_apply, hW] at this
  rw [← e.symm.sum_comp (fun k => T.matrix k i j * star (T.matrix k l m))]
  rw [this]
  split_ifs <;> simp


theorem x8_coef_le {U rho : Matrix A A ℂ} (hU : Uᴴ * U = 1) (hrho : IsDensityMatrix rho) :
    ‖(Uᴴ * rho).trace‖ ≤ 1 := by
  set c := (Uᴴ * rho).trace with hc
  by_cases h0 : c = 0
  · rw [h0, norm_zero]; exact zero_le_one
  have hn : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
  have hcc : c * star c = (‖c‖ : ℂ) * ‖c‖ := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hsn : star (‖c‖ : ℂ) = ‖c‖ := Complex.conj_ofReal _
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = c / ‖c‖ := ⟨_, rfl⟩
  have hzz : star z * z = 1 := by
    rw [hz, star_div₀, hsn, div_mul_div_comm, mul_comm (star c), hcc, div_self (mul_ne_zero hn hn)]
  have hzz2 : z * star z = 1 := by rw [mul_comm]; exact hzz
  obtain ⟨B, hB⟩ : ∃ B : Matrix A A ℂ, B = 1 - z • U := ⟨_, rfl⟩
  have hpsd := hrho.1.conjTranspose_mul_mul_same Bᴴ
  rw [conjTranspose_conjTranspose] at hpsd
  have htr := hpsd.trace_nonneg
  have hcU : (U * rho).trace = star c := by
    rw [hc, ← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, hrho.1.1.eq,
      trace_mul_comm]
  have hBB : Bᴴ * B = (2 : ℂ) • (1 : Matrix A A ℂ) - star z • Uᴴ - z • U := by
    rw [hB, conjTranspose_sub, conjTranspose_one, conjTranspose_smul]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hU]
    linear_combination (norm := module) hzz2 • (1 : Matrix A A ℂ)
  have e : (B * rho * Bᴴ).trace = 2 - 2 * (‖c‖ : ℂ) := by
    rw [trace_mul_cycle, hBB]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, trace_sub, trace_smul, smul_eq_mul]
    rw [← hc, hcU, hrho.2, hz, star_div₀, hsn, div_mul_eq_mul_div, div_mul_eq_mul_div,
      mul_comm (star c), hcc]
    field_simp
    ring
  rw [e] at htr
  have := (Complex.nonneg_iff.1 htr).1
  simp at this
  linarith

theorem x8_coef_eq (T : K → Matrix A A ℂ) (rho : Matrix A A ℂ) (k : K) :
    basisCoefficient T rho k = ∑ l, ∑ m, star (T k m l) * rho m l := by
  simp [basisCoefficient, trace, mul_apply, conjTranspose_apply]

theorem x8_expand [Nonempty A] (T : UnitaryBasis A K) (rho : Matrix A A ℂ) :
    rho = (Fintype.card A : ℂ)⁻¹ • (∑ k, basisCoefficient T.matrix rho k • T.matrix k) := by
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext i j
  rw [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp only [Matrix.smul_apply, smul_eq_mul, x8_coef_eq, Finset.sum_mul]
  have : ∀ l m, ∑ k, star (T.matrix k m l) * rho m l * T.matrix k i j =
      rho m l * (if (i, j) = (m, l) then (Fintype.card A : ℂ) else 0) := by
    intro l m
    rw [← x8_complete T i j m l, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_; ring
  rw [Finset.sum_comm]
  simp only [Finset.sum_comm (γ := K)]
  conv_rhs => arg 2; arg 2; ext l; arg 2; ext m; rw [this l m]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp only [if_true]; field_simp
    · intro m _ hm; simp [Ne.symm hm]
    · simp
  · intro l _ hl; refine Finset.sum_eq_zero fun m _ => ?_; simp [Ne.symm hl]
  · simp

theorem x8_parseval [Nonempty A] (T : UnitaryBasis A K) (rho : Matrix A A ℂ) :
    ∑ k, basisCoefficient T.matrix rho k * star (basisCoefficient T.matrix rho k) =
      (Fintype.card A : ℂ) * ∑ l, ∑ m, rho m l * star (rho m l) := by
  simp only [x8_coef_eq, star_sum, star_mul', star_star, Finset.sum_mul, Finset.mul_sum]
  have step : ∀ l m l', ∑ k, ∑ i, star (T.matrix k i l') * rho i l' *
      (T.matrix k m l * star (rho m l)) =
      ∑ i, rho i l' * star (rho m l) * (if (m, l) = (i, l') then (Fintype.card A : ℂ) else 0) := by
    intro l m l'
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← x8_complete T m l i l', Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_; ring
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro m _
  rw [Finset.sum_comm]
  have h2 : ∑ l', ∑ k, ∑ i, star (T.matrix k i l') * rho i l' * (T.matrix k m l * star (rho m l)) =
      ∑ l', ∑ i, rho i l' * star (rho m l) *
        (if (m, l) = (i, l') then (Fintype.card A : ℂ) else 0) :=
    Finset.sum_congr rfl fun l' _ => step l m l'
  rw [h2]
  rw [Finset.sum_eq_single l]
  · rw [Finset.sum_eq_single m]
    · simp; ring
    · intro i _ hi; simp [Ne.symm hi]
    · simp
  · intro l' _ hl; refine Finset.sum_eq_zero fun i _ => ?_; simp [Ne.symm hl]
  · simp

theorem x8_nsq (c : ℂ) : c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem x8_main [Nonempty A] [Nonempty K]
    (T : UnitaryBasis A K) (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho) :
    rho = (Fintype.card A : ℂ)⁻¹ • (∑ k, basisCoefficient T.matrix rho k • T.matrix k) ∧
    basisCoefficient T.matrix rho T.identityLabel = 1 ∧
    (∀ k, ‖basisCoefficient T.matrix rho k‖ ≤ 1) ∧
    (∀ psi : EuclideanSpace ℂ A, IsState psi → rho = pureDensity psi →
      (∑ k ∈ Finset.univ.erase T.identityLabel, ‖basisCoefficient T.matrix rho k‖^2) =
        (Fintype.card A : ℝ) - 1 ∧
      Fintype.card A ≤ (Finset.univ.filter (fun k => basisCoefficient T.matrix rho k ≠ 0)).card ∧
      (∀ S : Finset K, (∀ k, basisCoefficient T.matrix rho k ≠ 0 → k ∈ S) → Fintype.card A ≤ S.card) ∧
      (∀ groupStructure : AddGroup K,
        letI : AddGroup K := groupStructure
        Fintype.card A ≤ Nat.card
          (AddSubgroup.closure {k | basisCoefficient T.matrix rho k ≠ 0}))) := by
  have hid : basisCoefficient T.matrix rho T.identityLabel = 1 := by
    simp [basisCoefficient, T.identity, hrho.2]
  have hle : ∀ k, ‖basisCoefficient T.matrix rho k‖ ≤ 1 := fun k => x8_coef_le (T.unitary k) hrho
  refine ⟨x8_expand T rho, hid, hle, ?_⟩
  intro psi hpsi hpure
  have hn : ∑ i, ‖psi i‖ ^ 2 = 1 := by
    have := EuclideanSpace.norm_eq psi
    rw [hpsi] at this
    have h2 := congrArg (· ^ 2) this
    simp only [one_pow] at h2
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h2
    exact h2.symm
  have hρ : ∑ l, ∑ m, rho m l * star (rho m l) = 1 := by
    rw [hpure]
    simp only [pureDensity, of_apply, x8_nsq, norm_mul, Complex.norm_conj, mul_pow]
    rw [← Complex.ofReal_one, ← hn, ← one_mul (∑ i, ‖psi i‖ ^ 2), ← hn]
    push_cast
    rw [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
  have hsum : ∑ k, ‖basisCoefficient T.matrix rho k‖ ^ 2 = (Fintype.card A : ℝ) := by
    have h := x8_parseval T rho
    rw [hρ, mul_one] at h
    simp only [x8_nsq] at h
    exact_mod_cast h
  have hsupp : ∀ S : Finset K, (∀ k, basisCoefficient T.matrix rho k ≠ 0 → k ∈ S) →
      Fintype.card A ≤ S.card := by
    intro S hS
    have : (Fintype.card A : ℝ) ≤ S.card := by
      rw [← hsum]
      calc ∑ k, ‖basisCoefficient T.matrix rho k‖ ^ 2
          = ∑ k ∈ S, ‖basisCoefficient T.matrix rho k‖ ^ 2 := by
            refine (Finset.sum_subset (Finset.subset_univ S) fun k _ hk => ?_).symm
            have : basisCoefficient T.matrix rho k = 0 := by
              by_contra h; exact hk (hS k h)
            simp [this]
        _ ≤ ∑ k ∈ S, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
            have := hle k; have := norm_nonneg (basisCoefficient T.matrix rho k); nlinarith
        _ = S.card := by simp
    exact_mod_cast this
  refine ⟨?_, hsupp _ (fun k hk => by simp [hk]), hsupp, ?_⟩
  · rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), hsum, hid]; simp
  · intro G
    let _ := G
    refine (hsupp (Finset.univ.filter (fun k => basisCoefficient T.matrix rho k ≠ 0))
      (fun k hk => by simp [hk])).trans ?_
    calc (Finset.univ.filter (fun k => basisCoefficient T.matrix rho k ≠ 0)).card
        = Nat.card (↑(Finset.univ.filter (fun k => basisCoefficient T.matrix rho k ≠ 0)) : Set K) := by
          rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
      _ ≤ Nat.card ((AddSubgroup.closure {k | basisCoefficient T.matrix rho k ≠ 0} : AddSubgroup K) :
          Set K) := Nat.card_mono (Set.toFinite _) fun k hk =>
            AddSubgroup.subset_closure (by simpa using hk)
      _ = _ := rfl

end QAlgorithms.Papers.Independent.Gap48.P36

open scoped Matrix in
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P36 in
theorem solution {A K : Type*} [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]
    [Nonempty A] [Nonempty K]
    (T : UnitaryBasis A K) (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho) :
    rho = (Fintype.card A : ℂ)⁻¹ • (∑ k, basisCoefficient T.matrix rho k • T.matrix k) ∧
    basisCoefficient T.matrix rho T.identityLabel = 1 ∧
    (∀ k, ‖basisCoefficient T.matrix rho k‖ ≤ 1) ∧
    (∀ psi : EuclideanSpace ℂ A, IsState psi → rho = pureDensity psi →
      (∑ k ∈ Finset.univ.erase T.identityLabel, ‖basisCoefficient T.matrix rho k‖^2) =
        (Fintype.card A : ℝ) - 1 ∧
      Fintype.card A ≤ (Finset.univ.filter (fun k => basisCoefficient T.matrix rho k ≠ 0)).card ∧
      (∀ S : Finset K, (∀ k, basisCoefficient T.matrix rho k ≠ 0 → k ∈ S) → Fintype.card A ≤ S.card) ∧
      (∀ groupStructure : AddGroup K,
        letI : AddGroup K := groupStructure
        Fintype.card A ≤ Nat.card
          (AddSubgroup.closure {k | basisCoefficient T.matrix rho k ≠ 0}))) :=
  x8_main T rho hrho
