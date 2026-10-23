-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P07.protectedWeight_noInflow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:56:13.279546+00:00
-- url     : https://prove2.me/submissions/7daf087f-6fe4-441b-89c2-8e46cbbbbd94

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7NoInflow

open Matrix

abbrev J := Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ

lemma psd_eq_mul_conj {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) : ∃ V : Matrix n n ℂ, A = V * Vᴴ := by
  have hs := hA.1.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at hs
  set U : Matrix n n ℂ := (hA.1.eigenvectorUnitary : Matrix n n ℂ) with hU
  refine ⟨U * diagonal (fun i => ((Real.sqrt (hA.1.eigenvalues i) : ℝ) : ℂ)), ?_⟩
  rw [conjTranspose_mul, diagonal_conjTranspose, mul_assoc, ← mul_assoc (diagonal _),
    diagonal_mul_diagonal, ← star_eq_conjTranspose, ← mul_assoc]
  conv_lhs => rw [hs]
  congr 2
  congr 1
  funext i
  simp only [Function.comp, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hA.eigenvalues_nonneg i)]
  rfl

/-- If `K ρ Kᴴ = 0` with `ρ ≥ 0` then `K ρ = 0`. -/
lemma mul_psd_eq_zero {K ρ : J} (hρ : ρ.PosSemidef) (h : K * ρ * Kᴴ = 0) : K * ρ = 0 := by
  obtain ⟨V, rfl⟩ := psd_eq_mul_conj hρ
  have : (K * V) * (K * V)ᴴ = 0 := by
    rw [conjTranspose_mul]; simpa [mul_assoc] using h
  have h2 := self_mul_conjTranspose_eq_zero.1 this
  rw [← mul_assoc, h2, zero_mul]

lemma protect_block {m : ℕ} {K : Fin m → J} {P : J} {p : Fin m → ℝ}
    (h : QAlgorithms.Papers.Independent.Information100.P07.Protects K
      (QAlgorithms.Papers.Independent.Information100.P07.operatorRange P) p)
    (hPP : P * P = P) (i : Fin m) : (1 - P) * K i * P = 0 := by
  obtain ⟨W, hW, hx⟩ := h.2 i
  rw [Matrix.ext_iff_mulVec]
  intro v
  have hmem : Matrix.toEuclideanLin P (WithLp.toLp 2 v) ∈
      QAlgorithms.Papers.Independent.Information100.P07.operatorRange P := ⟨_, rfl⟩
  have h2 : act (K i) (Matrix.toEuclideanLin P (WithLp.toLp 2 v)) ∈
      QAlgorithms.Papers.Independent.Information100.P07.operatorRange P := by
    rw [hx _ hmem]
    exact Submodule.smul_mem _ _ (hW _ hmem)
  obtain ⟨y, hy⟩ := h2
  have hy' : P *ᵥ WithLp.ofLp y = K i *ᵥ (P *ᵥ v) := congrArg WithLp.ofLp hy
  rw [zero_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← hy', mulVec_mulVec, sub_mul, one_mul,
    hPP, sub_self, zero_mulVec]

lemma prod_protect {m : ℕ} {K : Fin m → J} {U V : Matrix (Fin 3) (Fin 3) ℂ} {p : Fin m → ℝ}
    (h : QAlgorithms.Papers.Independent.Information100.P07.ProductProtects K U V p)
    (i : Fin m) : ∃ U' V' : Matrix.unitaryGroup (Fin 3) ℂ,
      K i * Matrix.kronecker U V =
        (Real.sqrt (p i) : ℂ) •
          (Matrix.kronecker (U' : Matrix (Fin 3) (Fin 3) ℂ) (V' : Matrix (Fin 3) (Fin 3) ℂ) *
            Matrix.kronecker U V) := by
  obtain ⟨U', V', -, -, hx⟩ := h.2 i
  refine ⟨U', V', ?_⟩
  rw [Matrix.ext_iff_mulVec]
  intro v
  have hmem : Matrix.toEuclideanLin (Matrix.kronecker U V) (WithLp.toLp 2 v) ∈
      QAlgorithms.Papers.Independent.Information100.P07.operatorRange
        (Matrix.kronecker U V) := ⟨_, rfl⟩
  have := congrArg WithLp.ofLp (hx _ hmem)
  rw [← mulVec_mulVec, smul_mulVec, ← mulVec_mulVec]
  exact this

lemma side {m : ℕ} (A : Fin m → J) (hA : ∑ i, (A i)ᴴ * A i = 1) (P : J) (hPh : Pᴴ = P)
    (hPP : P * P = P) (hAP : ∀ i, (1 - P) * A i * P = 0) :
    (∑ i, (A i)ᴴ * P * A i) - P = ∑ i, (1 - P) * (A i)ᴴ * P * A i * (1 - P) := by
  have hAP' : ∀ i, P * A i * P = A i * P := by
    intro i; have := hAP i; rw [sub_mul, sub_mul, one_mul] at this
    exact (sub_eq_zero.1 this).symm
  set X := ∑ i, (A i)ᴴ * P * A i with hX
  have hXP : X * P = P := by
    rw [hX, Finset.sum_mul]
    calc ∑ i, (A i)ᴴ * P * A i * P = ∑ i, (A i)ᴴ * A i * P := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [mul_assoc (A i)ᴴ P (A i), mul_assoc (A i)ᴴ (P * A i) P, hAP', ← mul_assoc]
      _ = P := by rw [← Finset.sum_mul, hA, one_mul]
  have hXh : Xᴴ = X := by
    rw [hX, conjTranspose_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hPh, mul_assoc]
  have hPX : P * X = P := by
    have := congrArg conjTranspose hXP; rwa [conjTranspose_mul, hXh, hPh] at this
  have e : (1 - P) * X * (1 - P) = X - P * X - X * P + P * X * P := by
    simp only [sub_mul, mul_sub, one_mul, mul_one]; abel
  calc X - P = (1 - P) * X * (1 - P) := by rw [e, hPX, hXP, hPP]; abel
    _ = _ := by simp only [hX, Finset.mul_sum, Finset.sum_mul, mul_assoc]

lemma trace_side {m : ℕ} (A : Fin m → J) (hA : ∑ i, (A i)ᴴ * A i = 1) (P : J) (hPh : Pᴴ = P)
    (hPP : P * P = P) (hAP : ∀ i, (1 - P) * A i * P = 0) (ρ : J) :
    (P * krausApply A ρ).trace =
      (P * ρ).trace + ∑ i, (P * A i * (1 - P) * ρ * (P * A i * (1 - P))ᴴ).trace := by
  have hs := side A hA P hPh hPP hAP
  have h1 : (P * krausApply A ρ).trace = ((∑ i, (A i)ᴴ * P * A i) * ρ).trace := by
    simp only [krausApply, Finset.mul_sum, Finset.sum_mul, trace_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show P * (A i * ρ * (A i)ᴴ) = (P * (A i * ρ)) * (A i)ᴴ by simp only [mul_assoc],
      trace_mul_comm]
    simp only [mul_assoc]
  have h2 : (∑ i, (A i)ᴴ * P * A i) = P + ∑ i, (1 - P) * (A i)ᴴ * P * A i * (1 - P) := by
    rw [← hs]; abel
  rw [h1, h2, add_mul, trace_add, Finset.sum_mul, trace_sum]
  refine congrArg ((P * ρ).trace + ·) (Finset.sum_congr rfl (fun i _ => ?_))
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hPh]
  rw [trace_mul_comm (P * A i * (1 - P) * ρ)]
  refine congrArg Matrix.trace ?_
  calc (1 - P) * (A i)ᴴ * P * A i * (1 - P) * ρ
      = (1 - P) * (A i)ᴴ * (P * P) * A i * (1 - P) * ρ := by rw [hPP]
    _ = _ := by simp only [mul_assoc]

lemma blocks {m : ℕ} (A : Fin m → J) (P ρ : J) (hPh : Pᴴ = P) (hρh : ρᴴ = ρ)
    (hAP : ∀ i, (1 - P) * A i * P = 0) (hK : ∀ i, P * A i * (1 - P) * ρ = 0) :
    krausApply A (P * ρ * P) = P * krausApply A ρ * P ∧
    krausApply A ((1 - P) * ρ * (1 - P)) = (1 - P) * krausApply A ρ * (1 - P) ∧
    krausApply A (P * ρ * (1 - P)) = P * krausApply A ρ * (1 - P) := by
  have hAP' : ∀ i, P * A i * P = A i * P := by
    intro i; have := hAP i; rw [sub_mul, sub_mul, one_mul] at this
    exact (sub_eq_zero.1 this).symm
  have hL : ∀ i, P * A i * ρ = A i * P * ρ := by
    intro i
    have := hK i
    rw [mul_sub, mul_one, sub_mul, hAP'] at this
    exact (sub_eq_zero.1 this)
  have hL2 : ∀ i, (1 - P) * A i * ρ = A i * (1 - P) * ρ := by
    intro i
    rw [sub_mul, sub_mul, one_mul, hL, mul_sub, mul_one, sub_mul]
  have hR : ∀ i, ρ * ((A i)ᴴ * P) = ρ * (P * (A i)ᴴ) := by
    intro i
    have := congrArg conjTranspose (hL i)
    simpa only [conjTranspose_mul, hPh, hρh, mul_assoc] using this
  have hR2 : ∀ i, ρ * ((A i)ᴴ * (1 - P)) = ρ * ((1 - P) * (A i)ᴴ) := by
    intro i
    have := congrArg conjTranspose (hL2 i)
    simpa only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hPh, hρh,
      mul_assoc] using this
  have hLr : ∀ i Y, P * (A i * (ρ * Y)) = A i * (P * (ρ * Y)) := by
    intro i Y
    have := congrArg (· * Y) (hL i)
    simpa only [mul_assoc] using this
  have hLr2 : ∀ i Y, (1 - P) * (A i * (ρ * Y)) = A i * ((1 - P) * (ρ * Y)) := by
    intro i Y
    have := congrArg (· * Y) (hL2 i)
    simpa only [mul_assoc] using this
  refine ⟨?_, ?_, ?_⟩
  · simp only [krausApply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [mul_assoc]
    rw [hR, hLr]
  · simp only [krausApply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [mul_assoc]
    rw [hR2, hLr2]
  · simp only [krausApply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [mul_assoc]
    rw [hR2, hLr]

lemma term_psd {m : ℕ} (A : Fin m → J) (P : J) (hPh : Pᴴ = P) (hPP : P * P = P) :
    (∑ i, (1 - P) * (A i)ᴴ * P * A i * (1 - P)).PosSemidef := by
  apply posSemidef_sum
  intro i _
  have : (1 - P) * (A i)ᴴ * P * A i * (1 - P) = (P * A i * (1 - P))ᴴ * (P * A i * (1 - P)) := by
    simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hPh, mul_assoc]
    rw [← mul_assoc P P, hPP]
  rw [this]
  exact posSemidef_conjTranspose_mul_self _

lemma fix_comm {ι : Type*} [Fintype ι] (K : ι → J) (h1 : ∑ k, (K k)ᴴ * K k = 1)
    (h2 : ∑ k, K k * (K k)ᴴ = 1) (X : J) (hX : Xᴴ = X)
    (hfix : ∑ k, K k * X * (K k)ᴴ = X) : ∀ k, K k * X = X * K k := by
  have hterm : ∀ k, ((K k * X - X * K k)ᴴ * (K k * X - X * K k)).trace =
      ((K k)ᴴ * K k * (X * X)).trace - (K k * X * (K k)ᴴ * X).trace -
        (X * (K k * X * (K k)ᴴ)).trace + (K k * (K k)ᴴ * (X * X)).trace := by
    intro k
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hX]
    simp only [sub_mul, mul_sub, trace_sub]
    have e1 : (X * (K k)ᴴ * (K k * X)).trace = ((K k)ᴴ * K k * (X * X)).trace := by
      rw [show X * (K k)ᴴ * (K k * X) = X * ((K k)ᴴ * K k * X) by simp only [mul_assoc],
        trace_mul_comm]; simp only [mul_assoc]
    have e2 : (X * (K k)ᴴ * (X * K k)).trace = (K k * X * (K k)ᴴ * X).trace := by
      rw [show X * (K k)ᴴ * (X * K k) = (X * (K k)ᴴ * X) * K k by simp only [mul_assoc],
        trace_mul_comm]; simp only [mul_assoc]
    have e3 : ((K k)ᴴ * X * (K k * X)).trace = (X * (K k * X * (K k)ᴴ)).trace := by
      rw [show (K k)ᴴ * X * (K k * X) = (K k)ᴴ * (X * K k * X) by simp only [mul_assoc],
        trace_mul_comm]; simp only [mul_assoc]
    have e4 : ((K k)ᴴ * X * (X * K k)).trace = (K k * (K k)ᴴ * (X * X)).trace := by
      rw [show (K k)ᴴ * X * (X * K k) = ((K k)ᴴ * X * X) * K k by simp only [mul_assoc],
        trace_mul_comm]; simp only [mul_assoc]
    rw [e1, e2, e3, e4]; ring
  have hsum : ∑ k, ((K k * X - X * K k)ᴴ * (K k * X - X * K k)).trace = 0 := by
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← trace_sum,
      ← Finset.sum_mul, ← Finset.mul_sum]
    rw [h1, h2, hfix]; simp
  have hnn : ∀ k ∈ Finset.univ,
      (0 : ℂ) ≤ ((K k * X - X * K k)ᴴ * (K k * X - X * K k)).trace :=
    fun k _ => (posSemidef_conjTranspose_mul_self _).trace_nonneg
  intro k
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum k (Finset.mem_univ _)
  have := ((posSemidef_conjTranspose_mul_self _).trace_eq_zero_iff).1 h0
  exact sub_eq_zero.1 (conjTranspose_mul_self_eq_zero.1 this)

lemma conj_scale (A W P R : J) (c : ℝ) (hc : 0 ≤ c) (hPh : Pᴴ = P) (hRP : P * R * P = R)
    (hAW : A * P = (Real.sqrt c : ℂ) • (W * P)) :
    A * R * Aᴴ = (c : ℂ) • (W * R * Wᴴ) := by
  have e1 : A * R * Aᴴ = (A * P) * R * (A * P)ᴴ := by
    rw [conjTranspose_mul, hPh]; conv_lhs => rw [← hRP]
    simp only [mul_assoc]
  have e2 : W * R * Wᴴ = (W * P) * R * (W * P)ᴴ := by
    rw [conjTranspose_mul, hPh]; conv_lhs => rw [← hRP]
    simp only [mul_assoc]
  rw [e1, e2, hAW, conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
    smul_smul]
  congr 1
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hc]

lemma lu_part {m n : ℕ} (A : Fin m → J) (B : Fin n → J) (p : Fin m → ℝ) (q : Fin n → ℝ)
    (hp : QAlgorithms.Papers.Independent.Information100.P07.Weights p)
    (hq : QAlgorithms.Papers.Independent.Information100.P07.Weights q) (P R S : J)
    (hPh : Pᴴ = P) (WA : Fin m → J) (WB : Fin n → J)
    (hWA : ∀ i, (WA i)ᴴ * WA i = 1 ∧ WA i * (WA i)ᴴ = 1)
    (hWB : ∀ j, (WB j)ᴴ * WB j = 1 ∧ WB j * (WB j)ᴴ = 1)
    (hAW : ∀ i, A i * P = (Real.sqrt (p i) : ℂ) • (WA i * P))
    (hBW : ∀ j, B j * P = (Real.sqrt (q j) : ℂ) • (WB j * P))
    (hRP : P * R * P = R) (hSP : P * S * P = S)
    (hAR : krausApply A R = S) (hBS : krausApply B S = R) (hRh : Rᴴ = R) :
    ∃ j0, S = (WB j0)ᴴ * R * WB j0 := by
  have hS : S = ∑ i, (p i : ℂ) • (WA i * R * (WA i)ᴴ) := by
    rw [← hAR]; exact Finset.sum_congr rfl (fun i _ => conj_scale _ _ _ _ _ (hp.1 i) hPh hRP (hAW i))
  have hR : R = ∑ j, (q j : ℂ) • (WB j * S * (WB j)ᴴ) := by
    rw [← hBS]; exact Finset.sum_congr rfl (fun j _ => conj_scale _ _ _ _ _ (hq.1 j) hPh hSP (hBW j))
  set K : Fin m × Fin n → J := fun ij =>
    (Real.sqrt (p ij.1 * q ij.2) : ℂ) • (WB ij.2 * WA ij.1) with hKdef
  have hpq : ∀ ij : Fin m × Fin n, 0 ≤ p ij.1 * q ij.2 := fun ij => mul_nonneg (hp.1 _) (hq.1 _)
  have hss : ∀ ij : Fin m × Fin n, (star (Real.sqrt (p ij.1 * q ij.2) : ℂ)) *
      (Real.sqrt (p ij.1 * q ij.2) : ℂ) = ((p ij.1 * q ij.2 : ℝ) : ℂ) := by
    intro ij
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hpq ij)]
  have htot : ∑ ij : Fin m × Fin n, ((p ij.1 * q ij.2 : ℝ) : ℂ) = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [Complex.ofReal_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, hp.2, hq.2]; simp
  have h1 : ∑ ij, (K ij)ᴴ * K ij = 1 := by
    have : ∀ ij, (K ij)ᴴ * K ij = ((p ij.1 * q ij.2 : ℝ) : ℂ) • (1 : J) := by
      intro ij
      simp only [hKdef, conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
        conjTranspose_mul]
      rw [mul_comm, ← hss ij]
      congr 1
      rw [mul_assoc, ← mul_assoc (WB ij.2)ᴴ, (hWB _).1, one_mul, (hWA _).1]
    simp only [this, ← Finset.sum_smul, htot, one_smul]
  have h2 : ∑ ij, K ij * (K ij)ᴴ = 1 := by
    have : ∀ ij, K ij * (K ij)ᴴ = ((p ij.1 * q ij.2 : ℝ) : ℂ) • (1 : J) := by
      intro ij
      simp only [hKdef, conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
        conjTranspose_mul]
      rw [← hss ij]
      congr 1
      rw [mul_assoc, ← mul_assoc (WA ij.1), (hWA _).2, one_mul, (hWB _).2]
    simp only [this, ← Finset.sum_smul, htot, one_smul]
  have hfix : ∑ ij, K ij * R * (K ij)ᴴ = R := by
    have : ∀ ij, K ij * R * (K ij)ᴴ = (q ij.2 : ℂ) • (WB ij.2 *
        ((p ij.1 : ℂ) • (WA ij.1 * R * (WA ij.1)ᴴ)) * (WB ij.2)ᴴ) := by
      intro ij
      simp only [hKdef, conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
        conjTranspose_mul]
      have e' : star (Real.sqrt (p ij.1 * q ij.2) : ℂ) * (Real.sqrt (p ij.1 * q ij.2) : ℂ) =
          (q ij.2 : ℂ) * (p ij.1 : ℂ) := by rw [hss ij, Complex.ofReal_mul, mul_comm]
      have e : (Real.sqrt (p ij.1 * q ij.2) : ℂ) * star (Real.sqrt (p ij.1 * q ij.2) : ℂ) =
          (q ij.2 : ℂ) * (p ij.1 : ℂ) := by rw [mul_comm, e']
      simp only [e, e', mul_assoc]
    simp only [this]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    conv_rhs => rw [hR, hS]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  have hcomm := fix_comm K h1 h2 R hRh hfix
  have hqs : ∑ j, q j ≠ 0 := by rw [hq.2]; norm_num
  obtain ⟨j0, -, hj0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hqs
  refine ⟨j0, ?_⟩
  have key : ∀ i, (p i : ℂ) • (WA i * R * (WA i)ᴴ) = (p i : ℂ) • ((WB j0)ᴴ * R * WB j0) := by
    intro i
    by_cases hpi : p i = 0
    · simp [hpi]
    congr 1
    have hc := hcomm (i, j0)
    simp only [hKdef, smul_mul_assoc, mul_smul_comm] at hc
    have hne : (Real.sqrt (p i * q j0) : ℂ) ≠ 0 := by
      have : 0 < p i * q j0 := mul_pos (lt_of_le_of_ne (hp.1 i) (Ne.symm hpi))
        (lt_of_le_of_ne (hq.1 j0) (Ne.symm hj0))
      exact_mod_cast (Real.sqrt_pos.2 this).ne'
    have hc' := smul_right_injective J hne hc
    calc WA i * R * (WA i)ᴴ = (WB j0)ᴴ * (WB j0 * WA i * R) * (WA i)ᴴ := by
          rw [← mul_assoc, ← mul_assoc, (hWB j0).1, one_mul]
      _ = (WB j0)ᴴ * (R * (WB j0 * WA i)) * (WA i)ᴴ := by rw [hc']
      _ = (WB j0)ᴴ * R * WB j0 * (WA i * (WA i)ᴴ) := by simp only [mul_assoc]
      _ = _ := by rw [(hWA i).2, mul_one]
  rw [hS, Finset.sum_congr rfl (fun i _ => key i), ← Finset.sum_smul, ← Complex.ofReal_sum,
    hp.2, Complex.ofReal_one, one_smul]

lemma comm_iff (X P : J) (hX : Xᴴ = X) (hPh : Pᴴ = P) (hPP : P * P = P) :
    X * P = P * X ↔ P * X * (1 - P) = 0 := by
  constructor
  · intro h
    rw [← h, mul_assoc, mul_sub, mul_one, hPP, sub_self, mul_zero]
  · intro h
    have h1 : P * X = P * X * P := by
      rw [mul_sub, mul_one, sub_eq_zero] at h; exact h
    have h2 : X * P = P * X * P := by
      have := congrArg conjTranspose h1
      simpa only [conjTranspose_mul, hX, hPh, mul_assoc] using this
    rw [h1, h2]

lemma unit_kron (U V : Matrix.unitaryGroup (Fin 3) ℂ) :
    (Matrix.kronecker (U : Matrix (Fin 3) (Fin 3) ℂ) (V : Matrix (Fin 3) (Fin 3) ℂ))ᴴ *
        Matrix.kronecker (U : Matrix (Fin 3) (Fin 3) ℂ) (V : Matrix (Fin 3) (Fin 3) ℂ) = 1 ∧
      Matrix.kronecker (U : Matrix (Fin 3) (Fin 3) ℂ) (V : Matrix (Fin 3) (Fin 3) ℂ) *
        (Matrix.kronecker (U : Matrix (Fin 3) (Fin 3) ℂ) (V : Matrix (Fin 3) (Fin 3) ℂ))ᴴ = 1 := by
  have hk : ∀ A B : Matrix (Fin 3) (Fin 3) ℂ, Matrix.kronecker A B = A ⊗ₖ B := fun _ _ => rfl
  have u1 : (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem U.2
  have u2 : (U : Matrix (Fin 3) (Fin 3) ℂ) * (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem U.2
  have v1 : (V : Matrix (Fin 3) (Fin 3) ℂ)ᴴ * V = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem V.2
  have v2 : (V : Matrix (Fin 3) (Fin 3) ℂ) * (V : Matrix (Fin 3) (Fin 3) ℂ)ᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem V.2
  simp only [hk]
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, u1, u2, v1, v2,
    one_kronecker_one]
  exact ⟨rfl, rfl⟩

open QAlgorithms.Papers.Independent.Information100.P07 in
theorem main {m n : ℕ} (A : Fin m → Joint) (B : Fin n → Joint)
    (p : Fin m → ℝ) (q : Fin n → ℝ) (rho sigma P : Joint)
    (hA : IsKrausFamily A) (hB : IsKrausFamily B)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) (hP : IsProjection P)
    (hforward : krausApply A rho = sigma) (hreverse : krausApply B sigma = rho)
    (hprotectA : Protects A (operatorRange P) p) (hprotectB : Protects B (operatorRange P) q) :
    (P * rho).trace = (P * sigma).trace ∧
    ((∑ i, (A i)ᴴ * P * A i) - P).PosSemidef ∧ ((∑ i, (B i)ᴴ * P * B i) - P).PosSemidef ∧
    (∑ i, (A i)ᴴ * P * A i) - P = ∑ i, (1-P) * (A i)ᴴ * P * A i * (1-P) ∧
    (∑ i, (B i)ᴴ * P * B i) - P = ∑ i, (1-P) * (B i)ᴴ * P * B i * (1-P) ∧
    (∀ i, P * A i * (1-P) * rho * (1-P) * (A i)ᴴ * P = 0 ∧ P * A i * (1-P) * rho * P = 0) ∧
    (∀ i, P * B i * (1-P) * sigma * (1-P) * (B i)ᴴ * P = 0 ∧ P * B i * (1-P) * sigma * P = 0) ∧
    krausApply A (P*rho*P) = P*sigma*P ∧ krausApply B (P*sigma*P) = P*rho*P ∧
    krausApply A ((1-P)*rho*(1-P)) = (1-P)*sigma*(1-P) ∧
    krausApply B ((1-P)*sigma*(1-P)) = (1-P)*rho*(1-P) ∧
    krausApply A (P*rho*(1-P)) = P*sigma*(1-P) ∧ krausApply B (P*sigma*(1-P)) = P*rho*(1-P) ∧
    (rho*P = P*rho ↔ sigma*P = P*sigma) ∧
    (∀ U V : Local, IsProjection U → IsProjection V → P = Matrix.kronecker U V →
      ProductProtects A U V p → ProductProtects B U V q → LU (P*rho*P) (P*sigma*P)) := by
  have hPh : Pᴴ = P := hP.1
  have hPP : P * P = P := hP.2
  have hAP := protect_block hprotectA hPP
  have hBP := protect_block hprotectB hPP
  have hρh : rhoᴴ = rho := hrho.1.1
  have hσh : sigmaᴴ = sigma := hsigma.1.1
  have tA := trace_side A hA P hPh hPP hAP rho
  rw [hforward] at tA
  have tB := trace_side B hB P hPh hPP hBP sigma
  rw [hreverse] at tB
  have nA : ∀ i ∈ Finset.univ,
      (0 : ℂ) ≤ (P * A i * (1 - P) * rho * (P * A i * (1 - P))ᴴ).trace :=
    fun i _ => (hrho.1.mul_mul_conjTranspose_same _).trace_nonneg
  have nB : ∀ i ∈ Finset.univ,
      (0 : ℂ) ≤ (P * B i * (1 - P) * sigma * (P * B i * (1 - P))ᴴ).trace :=
    fun i _ => (hsigma.1.mul_mul_conjTranspose_same _).trace_nonneg
  set SA := ∑ i, (P * A i * (1 - P) * rho * (P * A i * (1 - P))ᴴ).trace with hSAdef
  set SB := ∑ i, (P * B i * (1 - P) * sigma * (P * B i * (1 - P))ᴴ).trace with hSBdef
  have hSA : 0 ≤ SA := Finset.sum_nonneg nA
  have hSB : 0 ≤ SB := Finset.sum_nonneg nB
  have hsum : SA + SB = 0 := by linear_combination -tA - tB
  have hSA0 : SA = 0 := by
    refine le_antisymm ?_ hSA
    have := le_add_of_nonneg_right (a := SA) hSB
    rwa [hsum] at this
  have hSB0 : SB = 0 := by
    refine le_antisymm ?_ hSB
    have := le_add_of_nonneg_left (a := SB) hSA
    rwa [hsum] at this
  have hKA : ∀ i, P * A i * (1 - P) * rho = 0 := by
    intro i
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg nA).1 hSA0 i (Finset.mem_univ _)
    exact mul_psd_eq_zero hrho.1 (((hrho.1.mul_mul_conjTranspose_same _).trace_eq_zero_iff).1 h0)
  have hKB : ∀ i, P * B i * (1 - P) * sigma = 0 := by
    intro i
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg nB).1 hSB0 i (Finset.mem_univ _)
    exact mul_psd_eq_zero hsigma.1
      (((hsigma.1.mul_mul_conjTranspose_same _).trace_eq_zero_iff).1 h0)
  have bA := blocks A P rho hPh hρh hAP hKA
  have bB := blocks B P sigma hPh hσh hBP hKB
  rw [hforward] at bA
  rw [hreverse] at bB
  have k0 : ∀ {k : ℕ} (K : Fin k → Joint), krausApply K 0 = 0 := by
    intro k K; simp [krausApply]
  refine ⟨by rw [tB, hSB0, add_zero], by rw [side A hA P hPh hPP hAP]; exact term_psd A P hPh hPP,
    by rw [side B hB P hPh hPP hBP]; exact term_psd B P hPh hPP,
    side A hA P hPh hPP hAP, side B hB P hPh hPP hBP,
    fun i => ⟨by rw [hKA i]; simp, by rw [hKA i]; simp⟩,
    fun i => ⟨by rw [hKB i]; simp, by rw [hKB i]; simp⟩,
    bA.1, bB.1, bA.2.1, bB.2.1, bA.2.2, bB.2.2, ?_, ?_⟩
  · rw [comm_iff rho P hρh hPh hPP, comm_iff sigma P hσh hPh hPP]
    constructor
    · intro h; rw [← bA.2.2, h, k0]
    · intro h; rw [← bB.2.2, h, k0]
  · intro U V _ _ hPUV hpA hpB
    choose UA VA hUA using prod_protect hpA
    choose UB VB hUB using prod_protect hpB
    rw [← hPUV] at hUA hUB
    have hPXP : ∀ X : Joint, P * (P * X * P) * P = P * X * P := by
      intro X; simp only [← mul_assoc, hPP]; simp only [mul_assoc, hPP]
    obtain ⟨j0, hj0⟩ := lu_part A B p q hprotectA.1 hprotectB.1 P (P * rho * P) (P * sigma * P)
      hPh (fun i => Matrix.kronecker (UA i : Local) (VA i : Local))
      (fun j => Matrix.kronecker (UB j : Local) (VB j : Local))
      (fun i => unit_kron _ _) (fun j => unit_kron _ _) hUA hUB (hPXP _) (hPXP _) bA.1 bB.1
      (by simp only [conjTranspose_mul, hPh, hρh, mul_assoc])
    refine ⟨star (UB j0), star (VB j0), ?_⟩
    rw [hj0]
    have hk : ∀ A B : Local, Matrix.kronecker A B = A ⊗ₖ B := fun _ _ => rfl
    simp only [hk, Unitary.coe_star, star_eq_conjTranspose, ← conjTranspose_kronecker,
      conjTranspose_conjTranspose]

end X7NoInflow

open QAlgorithms.Papers.Independent.Information100.P07 in
/-- arXiv:2610.05234v1, PDF p.16, Eq.(S32): weight and input-specific no inflow in both directions. -/
theorem solution {m n : ℕ} (A : Fin m → Joint) (B : Fin n → Joint)
    (p : Fin m → ℝ) (q : Fin n → ℝ) (rho sigma P : Joint)
    (hA : IsKrausFamily A) (hB : IsKrausFamily B)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) (hP : IsProjection P)
    (hforward : krausApply A rho = sigma) (hreverse : krausApply B sigma = rho)
    (hprotectA : Protects A (operatorRange P) p) (hprotectB : Protects B (operatorRange P) q) :
    (P * rho).trace = (P * sigma).trace ∧
    ((∑ i, (A i)ᴴ * P * A i) - P).PosSemidef ∧ ((∑ i, (B i)ᴴ * P * B i) - P).PosSemidef ∧
    (∑ i, (A i)ᴴ * P * A i) - P = ∑ i, (1-P) * (A i)ᴴ * P * A i * (1-P) ∧
    (∑ i, (B i)ᴴ * P * B i) - P = ∑ i, (1-P) * (B i)ᴴ * P * B i * (1-P) ∧
    (∀ i, P * A i * (1-P) * rho * (1-P) * (A i)ᴴ * P = 0 ∧ P * A i * (1-P) * rho * P = 0) ∧
    (∀ i, P * B i * (1-P) * sigma * (1-P) * (B i)ᴴ * P = 0 ∧ P * B i * (1-P) * sigma * P = 0) ∧
    krausApply A (P*rho*P) = P*sigma*P ∧ krausApply B (P*sigma*P) = P*rho*P ∧
    krausApply A ((1-P)*rho*(1-P)) = (1-P)*sigma*(1-P) ∧
    krausApply B ((1-P)*sigma*(1-P)) = (1-P)*rho*(1-P) ∧
    krausApply A (P*rho*(1-P)) = P*sigma*(1-P) ∧ krausApply B (P*sigma*(1-P)) = P*rho*(1-P) ∧
    (rho*P = P*rho ↔ sigma*P = P*sigma) ∧
    (∀ U V : Local, IsProjection U → IsProjection V → P = Matrix.kronecker U V →
      ProductProtects A U V p → ProductProtects B U V q → LU (P*rho*P) (P*sigma*P)) :=
  X7NoInflow.main A B p q rho sigma P hA hB hrho hsigma hP hforward hreverse hprotectA hprotectB
