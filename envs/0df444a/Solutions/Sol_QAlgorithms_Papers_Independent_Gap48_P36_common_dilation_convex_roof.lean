-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.common_dilation_convex_roof
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T00:27:15.301137+00:00
-- url     : https://prove2.me/submissions/c40f4036-2a4b-4466-a642-29df64721b81

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

section roof
variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

def x8v (M : Matrix Y X ℂ) (ψ : EuclideanSpace ℂ X) : EuclideanSpace ℂ Y :=
  WithLp.toLp 2 (M *ᵥ WithLp.ofLp ψ)

omit [DecidableEq X] [DecidableEq Y] in
@[simp] theorem x8v_apply (M : Matrix Y X ℂ) (ψ : EuclideanSpace ℂ X) (y : Y) :
    x8v M ψ y = ∑ x, M y x * ψ x := by
  simp [x8v, mulVec, dotProduct]

omit [DecidableEq X] [DecidableEq Y] in
theorem x8v_comp {Z : Type*} [Fintype Z] (M : Matrix Z Y ℂ) (N : Matrix Y X ℂ) (ψ : EuclideanSpace ℂ X) :
    x8v M (x8v N ψ) = x8v (M * N) ψ := by
  simp [x8v, mulVec_mulVec]

omit [DecidableEq X] [DecidableEq Y] in
theorem x8_pdc (M : Matrix Y X ℂ) (ψ : EuclideanSpace ℂ X) :
    M * pureDensity ψ * Mᴴ = pureDensity (x8v M ψ) := by
  ext y y'
  simp only [mul_apply, pureDensity, of_apply, conjTranspose_apply, x8v_apply, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun x _ => ?_
  simp [RCLike.star_def]; ring

omit [DecidableEq X] in
theorem x8_trpd (ψ : EuclideanSpace ℂ X) : (pureDensity ψ).trace = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [Matrix.trace, diag, pureDensity, of_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem x8_iso_norm (V : Matrix Y X ℂ) (hV : Vᴴ * V = 1) (φ : EuclideanSpace ℂ X) :
    ‖x8v V φ‖ = ‖φ‖ := by
  have h : (pureDensity (x8v V φ)).trace = (pureDensity φ).trace := by
    rw [← x8_pdc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]
  rw [x8_trpd, x8_trpd] at h
  have h2 : ‖x8v V φ‖ ^ 2 = ‖φ‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

omit [DecidableEq X] [DecidableEq Y] in
theorem x8_ens_conj {m : ℕ} (M : Matrix Y X ℂ) (w : Fin m → ℝ) (ψ : Fin m → EuclideanSpace ℂ X) :
    ensembleDensity w (fun k => x8v M (ψ k)) = M * ensembleDensity w ψ * Mᴴ := by
  simp only [ensembleDensity, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, x8_pdc]

theorem x8_roof [Nonempty X] (V : Matrix Y X ℂ) (hV : Vᴴ * V = 1)
    (c1 : EuclideanSpace ℂ Y → ℝ) (c2 : EuclideanSpace ℂ X → ℝ)
    (hc : ∀ φ, IsState φ → c1 (x8v V φ) = c2 φ) (rho : Matrix X X ℂ) :
    convexRoof c1 (V * rho * Vᴴ) = convexRoof c2 rho := by
  unfold convexRoof
  congr 1
  ext a
  constructor
  · rintro ⟨e, he, rfl⟩
    set P : Matrix Y Y ℂ := 1 - V * Vᴴ
    have hPV : P * V = 0 := by
      simp only [P, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one, sub_self]
    have hsumC : ∑ k, ((e.weight k * ‖x8v P (e.vector k)‖ ^ 2 : ℝ) : ℂ) = 0 := by
      have : (P * ensembleDensity e.weight e.vector * Pᴴ).trace = 0 := by
        rw [he, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPV]; simp
      rw [← x8_ens_conj, ensembleDensity, Matrix.trace_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.trace_smul, x8_trpd]; push_cast; rfl
    have hsum : ∑ k, e.weight k * ‖x8v P (e.vector k)‖ ^ 2 = 0 := by
      exact_mod_cast (by rw [← Complex.ofReal_sum] at hsumC; exact hsumC :
        ((∑ k, e.weight k * ‖x8v P (e.vector k)‖ ^ 2 : ℝ) : ℂ) = 0)
    rw [Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (e.nonnegative k) (sq_nonneg _)] at hsum
    have hfix : ∀ k, e.weight k ≠ 0 → x8v (V * Vᴴ) (e.vector k) = e.vector k := by
      intro k hk
      have h0 := hsum k (Finset.mem_univ _)
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hk
      · have h1 : x8v P (e.vector k) = 0 := by
          rw [← norm_eq_zero]; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
        have h2 : x8v P (e.vector k) = e.vector k - x8v (V * Vᴴ) (e.vector k) := by
          ext y; simp [x8v, P, Matrix.sub_mulVec]
        rw [h2, sub_eq_zero] at h1; exact h1.symm
    obtain ⟨x0⟩ := ‹Nonempty X›
    let u0 : EuclideanSpace ℂ X := EuclideanSpace.single x0 1
    have hu0 : IsState u0 := by simp [IsState, u0]
    let φ : Fin e.count → EuclideanSpace ℂ X := fun k =>
      if e.weight k = 0 then u0 else x8v Vᴴ (e.vector k)
    have hVφ : ∀ k, e.weight k ≠ 0 → x8v V (φ k) = e.vector k := by
      intro k hk; simp only [φ, if_neg hk, x8v_comp]; exact hfix k hk
    have hφs : ∀ k, IsState (φ k) := by
      intro k
      by_cases hk : e.weight k = 0
      · simp only [φ, if_pos hk]; exact hu0
      · unfold IsState
        rw [← x8_iso_norm V hV, hVφ k hk]; exact e.normalized k
    refine ⟨⟨e.count, e.weight, φ, e.nonnegative, e.total, hφs⟩, ?_, ?_⟩
    · simp only
      have : ensembleDensity e.weight φ = Vᴴ * ensembleDensity e.weight e.vector * V := by
        simp only [ensembleDensity, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : e.weight k = 0
        · simp [hk]
        · congr 1
          simp only [φ, if_neg hk]
          rw [← x8_pdc, conjTranspose_conjTranspose]
      rw [this, he]
      simp only [← Matrix.mul_assoc, hV, Matrix.one_mul]
      rw [Matrix.mul_assoc, hV, Matrix.mul_one]
    · refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : e.weight k = 0
      · simp [hk]
      · simp only; rw [← hc _ (hφs k), hVφ k hk]
  · rintro ⟨e, he, rfl⟩
    refine ⟨⟨e.count, e.weight, fun k => x8v V (e.vector k), e.nonnegative, e.total,
      fun k => by unfold IsState; rw [x8_iso_norm V hV]; exact e.normalized k⟩, ?_, ?_⟩
    · simp only; rw [x8_ens_conj, he]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only; rw [hc _ (e.normalized k)]

end roof

section ent
open Polynomial
theorem x8_tr_aeval {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (p : Polynomial ℝ) :
    (Polynomial.aeval M p).trace = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℂ) * (M ^ i).trace := by
  rw [Polynomial.aeval_eq_sum_range, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul]
  simp [Complex.real_smul]

theorem x8_tr_cfc_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M1 : Matrix ι ι ℂ) (M2 : Matrix κ κ ℂ) (h1 : M1.IsHermitian) (h2 : M2.IsHermitian)
    (h : ∀ k : ℕ, 1 ≤ k → (M1 ^ k).trace = (M2 ^ k).trace) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f M1).trace = (cfc f M2).trace := by
  classical
  let S : Finset ℝ := Finset.univ.image h1.eigenvalues ∪ Finset.univ.image h2.eigenvalues ∪ {0}
  let p : Polynomial ℝ := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have e1 : cfc f M1 = cfc (fun x => p.eval x) M1 := by
    apply cfc_congr
    intro x hx
    rw [h1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have e2 : cfc f M2 = cfc (fun x => p.eval x) M2 := by
    apply cfc_congr
    intro x hx
    rw [h2.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, hp 0 (by simp [S]), hf]
  rw [e1, e2, cfc_polynomial p M1, cfc_polynomial p M2, x8_tr_aeval, x8_tr_aeval]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [h0]
  · rw [h i hi]

theorem x8_pow_mul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) :
    (V * W) ^ (k + 1) = V * (W * V) ^ k * W := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

theorem x8_tr_pow_swap {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) (hk : 1 ≤ k) :
    ((V * W) ^ k).trace = ((W * V) ^ k).trace := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [x8_pow_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

end ent

theorem x8_ent_marg (ψ : EuclideanSpace ℂ (B × C)) :
    entropy (traceRight (pureDensity ψ)) = entropy (traceLeft (pureDensity ψ)) := by
  set M : Matrix B C ℂ := Matrix.of fun b c => ψ (b, c)
  have h1 : traceRight (pureDensity ψ) = M * Mᴴ := by
    ext b b'; simp [traceRight, pureDensity, M, mul_apply, RCLike.star_def]
  have h2 : traceLeft (pureDensity ψ) = (Mᴴ * M)ᵀ := by
    ext c c'; simp [traceLeft, pureDensity, M, mul_apply, RCLike.star_def, mul_comm]
  rw [h1, h2]
  unfold entropy
  rw [x8_tr_cfc_eq (M * Mᴴ) ((Mᴴ * M)ᵀ) (isHermitian_mul_conjTranspose_self M)
    (isHermitian_conjTranspose_mul_self M).transpose _ _ (by simp)]
  intro k hk
  rw [← Matrix.transpose_pow, Matrix.trace_transpose, x8_tr_pow_swap _ _ k hk]

theorem x8_main5 [Nonempty A] [Nonempty B] [Nonempty C]
    (V : Matrix (B × C) A ℂ) (hV : Vᴴ * V = 1)
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho) :
    entanglementFormation (V * rho * Vᴴ) =
      entropy (receiverChannel V rho) - constrainedHolevo (receiverChannel V) rho ∧
    entanglementFormation (V * rho * Vᴴ) =
      entropy (complementaryChannel V rho) - constrainedHolevo (complementaryChannel V) rho := by

  have hR : ∀ φ : EuclideanSpace ℂ A, receiverChannel V (pureDensity φ) =
      traceRight (pureDensity (x8v V φ)) := fun φ => by
    rw [← x8_pdc]; rfl
  have hC : ∀ φ : EuclideanSpace ℂ A, complementaryChannel V (pureDensity φ) =
      traceLeft (pureDensity (x8v V φ)) := fun φ => by
    rw [← x8_pdc]; rfl
  refine ⟨?_, ?_⟩
  · rw [constrainedHolevo, sub_sub_cancel, hhat, entanglementFormation]
    exact x8_roof V hV _ _ (fun φ _ => by rw [hR]) rho
  · rw [constrainedHolevo, sub_sub_cancel, hhat, entanglementFormation]
    exact x8_roof V hV _ _ (fun φ _ => by rw [hC, x8_ent_marg]) rho

end QAlgorithms.Papers.Independent.Gap48.P36

open scoped Matrix ComplexConjugate in
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P36 QAlgorithms.Papers.Independent.Claimed50.P48
  QAlgorithms.Papers.Independent.Information100.P56 QAlgorithms.Papers.Independent.Information100.P67 in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (V : Matrix (B × C) A ℂ) (hV : Vᴴ * V = 1)
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho) :
    entanglementFormation (V * rho * Vᴴ) =
      entropy (receiverChannel V rho) - constrainedHolevo (receiverChannel V) rho ∧
    entanglementFormation (V * rho * Vᴴ) =
      entropy (complementaryChannel V rho) - constrainedHolevo (complementaryChannel V) rho :=
  x8_main5 V hV rho hrho
