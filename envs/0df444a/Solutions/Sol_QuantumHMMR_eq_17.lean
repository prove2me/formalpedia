-- Prove2me | solution 1 for QuantumHMMR.eq_17
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T20:44:54.451801+00:00
-- url     : https://prove2.me/submissions/d3d879fd-30d3-42ee-aaf2-3226d29236f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.Multiset.Filter
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Theorems.Thm_QuantumHMMR_eq_16
import Theorems.Thm_QuantumHMMR_eigenvalue_count
import Theorems.Thm_QuantumHMMR_lemma_4_2


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

namespace PRUSpectralGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def normSq (v : ι → ℂ) : ℝ := (star v ⬝ᵥ v).re

lemma normSq_nonneg (v : ι → ℂ) : 0 ≤ normSq v :=
  (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg v)).1

lemma normSq_eq_zero (v : ι → ℂ) : normSq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply dotProduct_star_self_eq_zero.mp
    apply Complex.ext h
    exact (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg v)).2.symm
  · rintro rfl; simp [normSq]

lemma ker_orthogonal (P : Matrix ι ι ℂ) (hP : P.IsHermitian)
    (v : ι → ℂ) (hv : P *ᵥ v = 0) (w : ι → ℂ) : star v ⬝ᵥ (P *ᵥ w) = 0 := by
  rw [Matrix.dotProduct_mulVec, ← hP, Matrix.vecMul_conjTranspose, star_star, hv]
  simp

lemma projection_eigenvector (M P : Matrix ι ι ℂ) (hM : M.IsHermitian)
    (hP : P.IsHermitian) (hMP : M * P = P) (hPM : P * M = P) (hPP : P * P = P)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ v : ι → ℂ, P *ᵥ v = 0 →
      c * normSq v ≤ (star v ⬝ᵥ ((1 - M) *ᵥ v)).re)
    (i : ι) :
    P *ᵥ ⇑(hM.eigenvectorBasis i) =
      if hM.eigenvalues i = 1 then ⇑(hM.eigenvectorBasis i) else 0 := by
  classical
  let v : ι → ℂ := ⇑(hM.eigenvectorBasis i)
  have hev : M *ᵥ v = (hM.eigenvalues i : ℂ) • v := by
    simpa only [v, RCLike.real_smul_eq_coe_smul (K := ℂ)] using! hM.mulVec_eigenvectorBasis i
  by_cases hi : hM.eigenvalues i = 1
  · rw [if_pos hi]
    have hMv : M *ᵥ v = v := by simpa [hi] using hev
    let u := v - P *ᵥ v
    have hPu : P *ᵥ u = 0 := by
      simp only [u, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hPP, sub_self]
    have hMu : M *ᵥ u = u := by
      simp only [u, Matrix.mulVec_sub, hMv, Matrix.mulVec_mulVec, hMP]
    have hz : normSq u = 0 := by
      have h := hgap u hPu
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, hMu, sub_self, dotProduct_zero,
        Complex.zero_re] at h
      nlinarith [normSq_nonneg u]
    have hu : u = 0 := (normSq_eq_zero u).mp hz
    exact (sub_eq_zero.mp hu).symm
  · rw [if_neg hi]
    have heq : (hM.eigenvalues i : ℂ) • (P *ᵥ v) = P *ᵥ v := by
      rw [← Matrix.mulVec_smul, ← hev, Matrix.mulVec_mulVec, hPM]
    have hn : (hM.eigenvalues i : ℂ) ≠ 1 := by exact_mod_cast hi
    have hz : ((hM.eigenvalues i : ℂ) - 1) • (P *ᵥ v) = 0 := by
      rw [sub_smul, one_smul, heq, sub_self]
    exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hn)

lemma eigenvalue_upper (M P : Matrix ι ι ℂ) (hM : M.IsHermitian)
    (c : ℝ) (hgap : ∀ v : ι → ℂ, P *ᵥ v = 0 →
      c * normSq v ≤ (star v ⬝ᵥ ((1 - M) *ᵥ v)).re)
    (i : ι) (hi : P *ᵥ ⇑(hM.eigenvectorBasis i) = 0) : hM.eigenvalues i ≤ 1 - c := by
  have hn : normSq ⇑(hM.eigenvectorBasis i) = 1 := by
    unfold normSq
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K]
    simp [hM.eigenvectorBasis.orthonormal.norm_eq_one]
  have h := hgap _ hi
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re] at h
  change c * normSq ⇑(hM.eigenvectorBasis i) ≤ normSq ⇑(hM.eigenvectorBasis i) -
    (star ⇑(hM.eigenvectorBasis i) ⬝ᵥ (M *ᵥ ⇑(hM.eigenvectorBasis i))).re at h
  have hev : hM.eigenvalues i = (star ⇑(hM.eigenvectorBasis i) ⬝ᵥ (M *ᵥ ⇑(hM.eigenvectorBasis i))).re := by
    simpa! using hM.eigenvalues_eq i
  rw [hn, ← hev] at h
  linarith

lemma projection_diagonalization (M P : Matrix ι ι ℂ) (hM : M.IsHermitian)
    (hPv : ∀ i, P *ᵥ ⇑(hM.eigenvectorBasis i) =
      if hM.eigenvalues i = 1 then ⇑(hM.eigenvectorBasis i) else 0) :
    P = Unitary.conjStarAlgAut ℂ _ hM.eigenvectorUnitary
      (Matrix.diagonal (fun i => if hM.eigenvalues i = 1 then (1 : ℂ) else 0)) := by
  classical
  have hPV : P * (hM.eigenvectorUnitary : Matrix ι ι ℂ) =
      (hM.eigenvectorUnitary : Matrix ι ι ℂ) *
        Matrix.diagonal (fun i => if hM.eigenvalues i = 1 then (1 : ℂ) else 0) := by
    ext a i
    rw [Matrix.mul_diagonal]
    change (P *ᵥ ⇑(hM.eigenvectorBasis i)) a = _
    rw [hPv]
    split_ifs <;> simp [Matrix.IsHermitian.eigenvectorUnitary_apply]
  rw [Unitary.conjStarAlgAut_apply, ← hPV, Matrix.mul_assoc]
  simp

lemma segment_diagonalization (M P : Matrix ι ι ℂ) (hM : M.IsHermitian)
    (hPv : ∀ i, P *ᵥ ⇑(hM.eigenvectorBasis i) =
      if hM.eigenvalues i = 1 then ⇑(hM.eigenvectorBasis i) else 0) (m : ℕ) :
    M ^ m - P = Unitary.conjStarAlgAut ℂ _ hM.eigenvectorUnitary
      (Matrix.diagonal (fun i => if hM.eigenvalues i = 1 then (0 : ℂ)
        else (hM.eigenvalues i : ℂ) ^ m)) := by
  classical
  rw [projection_diagonalization M P hM hPv]
  conv_lhs => lhs; rw [hM.spectral_theorem, ← map_pow]
  rw [← map_sub]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_pow, Matrix.sub_apply, Matrix.diagonal_apply_eq,
      Pi.pow_apply, Function.comp_def]
    split_ifs with hi
    · simp [hi]
    · simp
  · simp [Matrix.diagonal_pow, Matrix.diagonal_apply_ne _ hij, hij]

/-- Spectral multiplicities can be read from any unitary diagonalization. -/
lemma eigenvalue_multiset_of_diagonalization (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℝ)
    (hd : B = Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i => (d i : ℂ)))) :
    (Finset.univ.val.map hB.eigenvalues) = Finset.univ.val.map d := by
  have hchar : B.charpoly = ∏ i, (Polynomial.X - Polynomial.C (d i : ℂ)) := by
    rw [hd, Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.charpoly_diagonal]
  have hroots := hB.roots_charpoly_eq_eigenvalues
  rw [hchar, Polynomial.roots_prod] at hroots
  · have heq : (Finset.univ.val.map (fun i => (d i : ℂ))) =
        Finset.univ.val.map (fun i => (hB.eigenvalues i : ℂ)) := by
      simpa only [Polynomial.roots_X_sub_C, Finset.sum_singleton, Multiset.bind_singleton,
        Function.comp_def] using! hroots
    have hreal := congrArg (Multiset.map Complex.re) heq
    simpa only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] using hreal.symm
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _

lemma eigenvalue_bound_of_multiset (a d : ι → ℝ)
    (heq : Finset.univ.val.map a = Finset.univ.val.map d)
    (r : ℝ) (hd : ∀ i, |d i| ≤ r) : ∀ i, |a i| ≤ r := by
  intro i
  have hi : a i ∈ Finset.univ.val.map a := Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  rw [heq] at hi
  obtain ⟨j,hj,hij⟩ := Multiset.mem_map.mp hi
  rw [← hij]
  exact hd j

lemma eigenvalue_count_of_multiset (a d : ι → ℝ)
    (heq : Finset.univ.val.map a = Finset.univ.val.map d) (r : ℝ) :
    (Finset.univ.filter fun i => r < |a i|).card =
      (Finset.univ.filter fun i => r < |d i|).card := by
  classical
  have h := congrArg (fun s : Multiset ℝ => (s.filter fun x => r < |x|).card) heq
  simpa only [Multiset.filter_map, Multiset.card_map, Function.comp_def,
    ← Finset.filter_val, Finset.card_def] using h

/-- A gap away from a fixed projection persists under taking a whole walk segment.
The count concerns eigenvalues with multiplicity, including negative eigenvalues. -/
theorem segment_spectrum (M P : Matrix ι ι ℂ) (hM : M.IsHermitian)
    (hP : P.IsHermitian) (hMP : M * P = P) (hPM : P * M = P) (hPP : P * P = P)
    (c θ : ℝ) (hc : 0 < c) (hθ0 : 0 ≤ θ) (hθc : θ ≤ 1 - c)
    (hgap : ∀ v : ι → ℂ, P *ᵥ v = 0 →
      c * normSq v ≤ (star v ⬝ᵥ ((1 - M) *ᵥ v)).re)
    (hnegative : ∀ i, hM.eigenvalues i < 0 → |hM.eigenvalues i| ≤ θ)
    (D m : ℕ) (hcount : (Finset.univ.filter fun i => θ < hM.eigenvalues i).card ≤ D) :
    (M ^ m - P) * P = 0 ∧ (M ^ m - P).IsHermitian ∧
      ∀ hB : (M ^ m - P).IsHermitian,
        (∀ i, |hB.eigenvalues i| ≤ (1 - c) ^ m) ∧
        (Finset.univ.filter fun i => θ ^ m < |hB.eigenvalues i|).card ≤ D := by
  classical
  have hpow : ∀ r : ℕ, M ^ r * P = P := by
    intro r
    induction r with
    | zero => simp
    | succ r ih => rw [pow_succ, mul_assoc, hMP, ih]
  refine ⟨by rw [sub_mul, hpow, hPP, sub_self], (hM.pow m).sub hP, ?_⟩
  intro hB
  have hPv := projection_eigenvector M P hM hP hMP hPM hPP c hc hgap
  let d : ι → ℝ := fun i => if hM.eigenvalues i = 1 then 0 else hM.eigenvalues i ^ m
  have hdiag : M ^ m - P = Unitary.conjStarAlgAut ℂ _ hM.eigenvectorUnitary
      (Matrix.diagonal (fun i => (d i : ℂ))) := by
    rw [segment_diagonalization M P hM hPv m]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, d]
      split_ifs <;> simp
    · simp [hij]
  have heq := eigenvalue_multiset_of_diagonalization _ hB hM.eigenvectorUnitary d hdiag
  have hc1 : 0 ≤ 1 - c := hθ0.trans hθc
  constructor
  · apply eigenvalue_bound_of_multiset _ d heq
    intro i
    by_cases hi : hM.eigenvalues i = 1
    · simp only [d, if_pos hi, abs_zero]
      positivity
    · have hPi : P *ᵥ ⇑(hM.eigenvectorBasis i) = 0 := by simpa only [if_neg hi] using hPv i
      have hu := eigenvalue_upper M P hM c hgap i hPi
      have habs : |hM.eigenvalues i| ≤ 1 - c := by
        by_cases hneg : hM.eigenvalues i < 0
        · exact (hnegative i hneg).trans hθc
        · rw [abs_of_nonneg (le_of_not_gt hneg)]
          exact hu
      simp only [d, if_neg hi, abs_pow]
      gcongr
  · rw [eigenvalue_count_of_multiset _ d heq]
    apply le_trans (Finset.card_le_card _) hcount
    intro i hi
    have hgt := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hnot
    have hle : hM.eigenvalues i ≤ θ := le_of_not_gt hnot
    have hsmall : |d i| ≤ θ ^ m := by
      by_cases hione : hM.eigenvalues i = 1
      · simp only [d, if_pos hione, abs_zero]
        positivity
      · have habs : |hM.eigenvalues i| ≤ θ := by
          by_cases hneg : hM.eigenvalues i < 0
          · exact hnegative i hneg
          · rwa [abs_of_nonneg (le_of_not_gt hneg)]
        simp only [d, if_neg hione, abs_pow]
        gcongr
    exact (not_lt_of_ge hsmall) hgt

end PRUSpectralGap



set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PRUSegmentParameters

lemma power_le_exp (x : ℝ) (hx : 0 ≤ 1 - x) (m : ℕ) :
    (1 - x) ^ m ≤ Real.exp (-x * m) := by
  have h : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  calc
    _ ≤ Real.exp (-x) ^ m := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem eventual_parameters (γ a : ℝ) (hγ : 0 < γ) (ha : 0 < a)
    (A : ℕ) (hA : 1 ≤ A) :
    ∃ N : ℕ, ∀ n ≥ N,
      let m := A * n ^ 2
      let c := a / (2 * (m : ℝ))
      let θ := 1 - (1 - (m : ℝ)⁻¹) * γ / n
      1 ≤ m ∧ 0 < c ∧ 0 ≤ θ ∧ θ ≤ 1 - c ∧
        (1 - c) ^ m ≤ Real.exp (-(a / 2)) ∧
        θ ^ m ≤ Real.exp (-(γ * m / (2 * n))) := by
  refine ⟨max 2 (max ⌈γ⌉₊ ⌈a / γ⌉₊), ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hγn : γ ≤ (n : ℝ) := (Nat.le_ceil γ).trans (by exact_mod_cast (show ⌈γ⌉₊ ≤ n by omega))
  have han : a / γ ≤ (n : ℝ) := (Nat.le_ceil (a / γ)).trans
    (by exact_mod_cast (show ⌈a / γ⌉₊ ≤ n by omega))
  have han' : a ≤ (n : ℝ) * γ := (div_le_iff₀ hγ).mp han
  let m := A * n ^ 2
  have hmnat : n ^ 2 ≤ m := by dsimp [m]; nlinarith
  have hm4 : 4 ≤ m := by nlinarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmR4 : (4 : ℝ) ≤ m := by exact_mod_cast hm4
  have hmRn : (n : ℝ) ^ 2 ≤ m := by exact_mod_cast hmnat
  have hnp : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hp0 : (0 : ℝ) ≤ (m : ℝ)⁻¹ := by positivity
  have hpHalf : (m : ℝ)⁻¹ ≤ 1 / 2 := by
    have h : (2 : ℝ) ≤ m := by linarith
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h
  have hθ0 : 0 ≤ 1 - (1 - (m : ℝ)⁻¹) * γ / n := by
    have hdiv : γ / (n : ℝ) ≤ 1 := (div_le_one hnR).mpr hγn
    rw [mul_div_assoc]
    nlinarith [mul_nonneg hp0 (div_nonneg hγ.le hnR.le)]
  have hθc : 1 - (1 - (m : ℝ)⁻¹) * γ / n ≤ 1 - a / (2 * m) := by
    apply (mul_le_mul_iff_right₀ (show 0 < 2 * (m : ℝ) * n by positivity)).mp
    field_simp
    nlinarith [mul_nonneg hγ.le (show 0 ≤ (n : ℝ) ^ 2 / 2 - 1 by nlinarith)]
  have hc0 : 0 < a / (2 * (m : ℝ)) := by positivity
  have hc1 : 0 ≤ 1 - a / (2 * (m : ℝ)) := hθ0.trans hθc
  refine ⟨by omega, hc0, hθ0, hθc, ?_, ?_⟩
  · have h := power_le_exp (a / (2 * m)) hc1 m
    convert h using 1
    congr 1
    field_simp
  · have h := power_le_exp ((1 - (m : ℝ)⁻¹) * γ / n) hθ0 m
    apply h.trans
    apply Real.exp_le_exp.mpr
    change -((1 - (m : ℝ)⁻¹) * γ / n) * (m : ℝ) ≤ -(γ * m / (2 * n))
    have hq : 0 ≤ γ / (n : ℝ) := by positivity
    have hhh : (1 / 2) * (γ / (n : ℝ)) ≤ (1 - (m : ℝ)⁻¹) * (γ / n) := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hhh hmR.le
    calc
      _ = -(((1 - (m : ℝ)⁻¹) * (γ / n)) * m) := by ring
      _ ≤ -((1 / 2) * (γ / (n : ℝ)) * m) := neg_le_neg hh
      _ = _ := by field_simp



/-- Choose an integer segment constant that absorbs the dimension factor. -/
theorem choose_segment_constant (γ : ℝ) (hγ : 0 < γ) (t : ℕ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∃ N : ℕ, ∀ n ≥ N,
      ((2 : ℝ) ^ n) ^ (2 * t) *
        (1 - (1 - ((A * n ^ 2 : ℕ) : ℝ)⁻¹) * γ / n) ^ (A * n ^ 2)
        ≤ Real.exp (-(n : ℝ)) := by
  let K : ℝ := 2 * (2 * (t : ℝ) * Real.log 2 + 1) / γ
  let A : ℕ := max 1 ⌈K⌉₊
  have hA : 1 ≤ A := le_max_left _ _
  have hKA : K ≤ (A : ℝ) := (Nat.le_ceil K).trans (by exact_mod_cast le_max_right 1 ⌈K⌉₊)
  have hAg : 2 * (2 * (t : ℝ) * Real.log 2 + 1) ≤ (A : ℝ) * γ :=
    (div_le_iff₀ hγ).mp hKA
  obtain ⟨N,hN⟩ := eventual_parameters γ 1 hγ (by norm_num) A hA
  refine ⟨A,hA,max N 1,?_⟩
  intro n hn
  have hnN : N ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htail := (hN n hnN).2.2.2.2.2
  have hW : ((2 : ℝ) ^ n) ^ (2 * t) = Real.exp (2 * (t : ℝ) * n * Real.log 2) := by
    conv_lhs => rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ((2 : ℝ) ^ n) ^ (2 * t) * Real.exp (-(γ * (A * n ^ 2 : ℕ) / (2 * n))) := by
      gcongr
    _ = Real.exp (2 * (t : ℝ) * n * Real.log 2 - γ * (A * n ^ 2 : ℕ) / (2 * n)) := by
      rw [hW, ← Real.exp_add]
      congr 1
    _ ≤ Real.exp (-(n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have heq : γ * ((A * n ^ 2 : ℕ) : ℝ) / (2 * n) = γ * A * n / 2 := by
        push_cast
        field_simp
      rw [heq]
      have h := mul_le_mul_of_nonneg_right hAg hnR.le
      nlinarith

end PRUSegmentParameters



set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
open QAlgorithms QuantumHMMR QAlgorithms.Papers.Independent.Extend50.P45
open scoped Matrix ComplexConjugate BigOperators

theorem solution [∀ n, Fintype (Clifford.ProjectiveGroup n)]
    (G : Finset (Clifford.ProjectiveGroup 2)) (hG : IsCliffordGenSet G)
    (t : ℕ) (ht : 4 ≤ t) (γ a : ℝ) (hga : IsGapPair G t γ a) :
    (∀ A : ℕ, 1 ≤ A → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let m := A * n ^ 2
      let p : ℝ := (m : ℝ)⁻¹
      let M := balancedUnitaryMoment (stepLaw G n m) t
      let MH := balancedUnitaryMoment (haarLaw n) t
      let B := M ^ m - MH
      let η : ℝ := (1 - (1 - p) * γ / n) ^ m
      B * MH = 0 ∧ B.IsHermitian ∧
      (∀ hB : B.IsHermitian,
        (∀ i, |hB.eigenvalues i| ≤ Real.exp (-(a / 2))) ∧
        (Finset.univ.filter fun i => η < |hB.eigenvalues i|).card ≤ Dt t) ∧
      η ≤ Real.exp (-(γ * m / (2 * n)))) ∧
    Real.exp (-(a / 2)) < 1 ∧
    ∃ A : ℕ, 1 ≤ A ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ((2 : ℝ) ^ n) ^ (2 * t) * (1 - (1 - ((A * n ^ 2 : ℕ) : ℝ)⁻¹) * γ / n) ^ (A * n ^ 2)
        ≤ Real.exp (-(n : ℝ)) := by
  classical

  have hγ : 0 < γ := hga.1
  have ha : 0 < a := hga.2.1
  refine ⟨?_, Real.exp_lt_one_iff.mpr (by linarith), PRUSegmentParameters.choose_segment_constant γ hγ t⟩
  intro A hA
  obtain ⟨n16,h16⟩ := QuantumHMMR.eq_16 G hG t ht γ a hga A hA
  obtain ⟨nE,hE⟩ := QuantumHMMR.eigenvalue_count G hG t ht γ a hga A hA
  obtain ⟨nP,hparam⟩ := PRUSegmentParameters.eventual_parameters γ a hγ ha A hA
  refine ⟨max n16 (max nE nP), ?_⟩
  intro n hn
  have hn16 : n16 ≤ n := by omega
  have hnE : nE ≤ n := by omega
  have hnP : nP ≤ n := by omega
  let m := A * n ^ 2
  let M := balancedUnitaryMoment (stepLaw G n m) t
  let P := balancedUnitaryMoment (haarLaw n) t
  let c := a / (2 * (m : ℝ))
  let θ := 1 - (1 - (m : ℝ)⁻¹) * γ / n
  obtain ⟨hm,hc,hθ,hθc,hpow,hfast⟩ := hparam n hnP
  obtain ⟨_,_,hM,heigs,_⟩ := hE n hnE
  change M.IsHermitian at hM
  obtain ⟨hcount,hnegative⟩ := heigs hM
  obtain ⟨_,_,_,hP,hPP,_⟩ := (QuantumHMMR.lemma_4_2 G hG).1 t ht n
  change P.IsHermitian at hP
  change P * P = P at hPP
  obtain ⟨hMP,hPM,_,_,hquadratic⟩ := h16 n hn16
  change M * P = P at hMP
  change P * M = P at hPM
  have hgap (v) (hv : P *ᵥ v = 0) :
      c * PRUSpectralGap.normSq v ≤ (star v ⬝ᵥ ((1 - M) *ᵥ v)).re := by
    have h := hquadratic v (PRUSpectralGap.ker_orthogonal P hP v hv)
    have hh := h.2.2.2.trans h.2.2.1
    change (a * (m : ℝ)⁻¹ / 2) * PRUSpectralGap.normSq v ≤ _ at hh
    convert hh using 1 <;> dsimp [c] <;> ring
  have hs := PRUSpectralGap.segment_spectrum M P hM hP hMP hPM hPP c θ hc hθ hθc hgap
    hnegative (Dt t) m hcount
  refine ⟨hs.1,hs.2.1,?_,hfast⟩
  intro hB
  obtain ⟨hradius,hnum⟩ := hs.2.2 hB
  exact ⟨fun i => (hradius i).trans hpow, hnum⟩

#print axioms solution
