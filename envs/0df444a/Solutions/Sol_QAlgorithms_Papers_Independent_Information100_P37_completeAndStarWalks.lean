-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.completeAndStarWalks
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:05:23.279975+00:00
-- url     : https://prove2.me/submissions/da480fe5-46f4-468f-afd9-f0ceb5566019

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Information100.P37

section ExpLemmas
open scoped Matrix.Norms.Operator

lemma X7_exp_idem {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ)
    (hP : P * P = P) (c : ℂ) :
    NormedSpace.exp (c • P) = 1 + (Complex.exp c - 1) • P := by
  have hpow : ∀ k : ℕ, (c • P) ^ k = c ^ k • P + (if k = 0 then 1 - P else 0) := by
    intro k
    cases k with
    | zero => simp
    | succ k =>
      simp only [smul_pow, Nat.succ_ne_zero, if_false, add_zero]
      congr 1
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ih, hP]
  have h1 : HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹ • c ^ k) • P) (Complex.exp c • P) := by
    have := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c
    rw [← Complex.exp_eq_exp_ℂ] at this
    exact this.smul_const P
  have h2 : HasSum (fun k : ℕ => (if k = 0 then (1 - P) else 0)) (1 - P) :=
    hasSum_ite_eq 0 (1 - P)
  have h3 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • P)
  have h4 : HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹ • (c • P) ^ k))
      (Complex.exp c • P + (1 - P)) := by
    convert h1.add h2 using 1
    funext k
    rw [hpow k, smul_add, smul_smul]
    congr 1
    split_ifs with hk <;> simp [hk]
  refine (h3.unique h4).trans ?_
  rw [sub_smul, one_smul]; abel

lemma X7_exp_cube {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    (hH : H * H * H = H) (c : ℂ) (hc1 : Complex.exp c = -1) (hc2 : Complex.exp (-c) = -1) :
    NormedSpace.exp (c • H) = 1 - (2 : ℂ) • (H * H) := by
  set Pp : Matrix n n ℂ := (1/2 : ℂ) • (H * H + H) with hPp
  set Pm : Matrix n n ℂ := (1/2 : ℂ) • (H * H - H) with hPm
  have h4 : H * H * H * H = H * H := by rw [hH]
  have hPP : Pp * Pp = Pp := by
    simp only [hPp, smul_mul_smul, mul_add, add_mul, ← mul_assoc, hH]
    module
  have hMM : Pm * Pm = Pm := by
    simp only [hPm, smul_mul_smul, mul_sub, sub_mul, ← mul_assoc, hH]
    module
  have hPM : Pp * Pm = 0 := by
    simp only [hPp, hPm, smul_mul_smul, mul_sub, add_mul, ← mul_assoc, hH]
    module
  have hMP : Pm * Pp = 0 := by
    simp only [hPp, hPm, smul_mul_smul, mul_add, sub_mul, ← mul_assoc, hH]
    module
  have hsplit : c • H = c • Pp + (-c) • Pm := by
    simp only [hPp, hPm]; module
  clear_value Pp Pm
  rw [hsplit, Matrix.exp_add_of_commute _ _ (by rw [Commute, SemiconjBy, smul_mul_smul,
      smul_mul_smul, hPM, hMP, smul_zero, smul_zero])]
  rw [X7_exp_idem Pp hPP, X7_exp_idem Pm hMM, hc1, hc2]
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_smul, hPM, smul_zero, add_zero]
  simp only [hPp, hPm]
  module

end ExpLemmas

section NormLemmas
open scoped Matrix.Norms.L2Operator

lemma X7_norm_sq {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hM : Mᴴ = M) (hMM : M * M = (c : ℂ) • M) (h0 : M ≠ 0) : ‖M‖ = c := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self M
  rw [hM, hMM, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc] at h
  have hne : ‖M‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  exact (mul_right_cancel₀ hne h).symm

lemma X7_norm_one {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    ‖(1 : Matrix n n ℂ)‖ = 1 := by
  apply X7_norm_sq _ 1 zero_le_one (by simp) (by simp)
  exact one_ne_zero

lemma X7_norm_invol {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (R : Matrix n n ℂ)
    (hR : Rᴴ = R) (hRR : R * R = 1) : ‖R‖ = 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self R
  rw [hR, hRR, X7_norm_one] at h
  nlinarith [norm_nonneg R]

/-- uniform projector over ℂ -/
def X7_Pi (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := fun _ _ => 1 / (d : ℂ)

lemma X7_Pi_idem (d : ℕ) (hd : 1 ≤ d) : X7_Pi d * X7_Pi d = X7_Pi d := by
  have : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  ext i j
  simp only [X7_Pi, Matrix.mul_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

lemma X7_Pi_herm (d : ℕ) : (X7_Pi d)ᴴ = X7_Pi d := by
  ext i j; simp [X7_Pi]

lemma X7_Pi_ne (d : ℕ) (hd : 1 ≤ d) : X7_Pi d ≠ 0 := by
  intro h
  have := congrFun (congrFun h ⟨0, by omega⟩) ⟨0, by omega⟩
  simp only [X7_Pi, Matrix.zero_apply, one_div, inv_eq_zero, Nat.cast_eq_zero] at this
  omega

lemma X7_complete_eq (d : ℕ) : completeAdjacency d = (d : ℂ) • X7_Pi d - 1 := by
  ext i j
  have : (d : ℂ) ≠ 0 := by
    have := i.pos; exact_mod_cast (show d ≠ 0 by omega)
  by_cases h : i = j
  · subst h; simp [completeAdjacency, X7_Pi, this]
  · simp [completeAdjacency, X7_Pi, h]; field_simp

lemma X7_complete_norm (d : ℕ) (hd : 2 ≤ d) : ‖completeAdjacency d‖ = (d : ℝ) - 1 := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hP := X7_Pi_idem d (by omega)
  have hPn : ‖X7_Pi d‖ = 1 :=
    X7_norm_sq _ 1 zero_le_one (X7_Pi_herm d) (by simp [hP]) (X7_Pi_ne d (by omega))
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  apply le_antisymm
  · set R : Matrix (Fin d) (Fin d) ℂ := (2 : ℂ) • X7_Pi d - 1 with hRdef
    have hR : ‖R‖ = 1 := by
      apply X7_norm_invol
      · simp [hRdef, X7_Pi_herm]
      · simp only [hRdef, sub_mul, mul_sub, hP, mul_one, one_mul, smul_mul_assoc,
          mul_smul_comm]
        module
    have hA : completeAdjacency d = ((((d : ℝ) - 2) / 2 : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)
        + (((d : ℝ) / 2 : ℝ) : ℂ) • R := by
      rw [X7_complete_eq, hRdef]
      push_cast
      module
    rw [hA]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), hR, X7_norm_one]
    linarith
  · have hPA : X7_Pi d * completeAdjacency d = (((d : ℝ) - 1 : ℝ) : ℂ) • X7_Pi d := by
      rw [X7_complete_eq, mul_sub, mul_smul_comm, hP, mul_one]
      push_cast; module
    have h1 := Matrix.l2_opNorm_mul (X7_Pi d) (completeAdjacency d)
    rw [hPA, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), hPn]
      at h1
    linarith

/-- square of the star adjacency -/
def X7_M (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  fun i j => if i.val = 0 ∧ j.val = 0 then (n : ℂ) else if i.val ≠ 0 ∧ j.val ≠ 0 then 1 else 0

lemma X7_SS (n : ℕ) : starAdjacency (n+1) * starAdjacency (n+1) = X7_M n := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, starAdjacency, X7_M]

lemma X7_MM (n : ℕ) : X7_M n * X7_M n = (n : ℂ) • X7_M n := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, X7_M]

lemma X7_SM (n : ℕ) : starAdjacency (n+1) * X7_M n = (n : ℂ) • starAdjacency (n+1) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, X7_M, starAdjacency]

lemma X7_MS (n : ℕ) : X7_M n * starAdjacency (n+1) = (n : ℂ) • starAdjacency (n+1) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, X7_M, starAdjacency]

lemma X7_S_herm (n : ℕ) : (starAdjacency (n+1))ᴴ = starAdjacency (n+1) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, starAdjacency]
  split_ifs <;> simp_all <;> omega

lemma X7_M_herm (n : ℕ) : (X7_M n)ᴴ = X7_M n := by
  ext i j
  simp only [Matrix.conjTranspose_apply, X7_M]
  split_ifs <;> simp_all

lemma X7_star_norm (n : ℕ) (hn : 1 ≤ n) : ‖starAdjacency (n+1)‖ = Real.sqrt n := by
  have hM : ‖X7_M n‖ = n := by
    apply X7_norm_sq _ n (Nat.cast_nonneg n) (X7_M_herm n) (by rw [X7_MM]; rfl)
    intro h
    have := congrFun (congrFun h 0) 0
    simp [X7_M] at this
    omega
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (starAdjacency (n+1))
  rw [X7_S_herm, X7_SS, hM] at h
  rw [h, Real.sqrt_mul_self (norm_nonneg _)]

lemma X7_star_spec (n : ℕ) (hn : 1 ≤ n) : specNorm (starAdjacency (n+1)) = Real.sqrt n :=
  X7_star_norm n hn

lemma X7_complete_spec (d : ℕ) (hd : 2 ≤ d) : specNorm (completeAdjacency d) = (d : ℝ) - 1 :=
  X7_complete_norm d hd

end NormLemmas

lemma X7_star_walk (n : ℕ) (hn : 1 ≤ n) : walk (starAdjacency (n+1)) Real.pi =
    fun i j => if i.val = 0 ∧ j.val = 0 then -1 else
      if i.val ≠ 0 ∧ j.val ≠ 0 then (if i = j then 1 else 0) - 2 / (n : ℂ) else 0 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ = (n : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hnr.le]
  set S := starAdjacency (n+1)
  have hcube : ((Real.sqrt n)⁻¹ • S) * ((Real.sqrt n)⁻¹ • S) * ((Real.sqrt n)⁻¹ • S) =
      (Real.sqrt n)⁻¹ • S := by
    rw [smul_mul_smul, smul_mul_smul, X7_SS, X7_MS, hr, mul_comm, mul_smul]
    congr 1
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    push_cast
    field_simp
    rfl
  have hc1 : Complex.exp (-Complex.I * (Real.pi : ℂ)) = -1 := by
    rw [show -Complex.I * (Real.pi : ℂ) = -(Real.pi * Complex.I) by ring, Complex.exp_neg,
      Complex.exp_pi_mul_I]; norm_num
  have hc2 : Complex.exp (-(-Complex.I * (Real.pi : ℂ))) = -1 := by
    rw [show -(-Complex.I * (Real.pi : ℂ)) = (Real.pi * Complex.I) by ring,
      Complex.exp_pi_mul_I]
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold walk
  rw [X7_star_spec n hn, X7_exp_cube _ hcube _ hc1 hc2, smul_mul_smul, hr, X7_SS]
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [X7_M, Matrix.one_apply, hnc, div_eq_mul_inv, (Fin.succ_ne_zero _).symm]
  norm_num


lemma X7_sum2 (n : ℕ) (i j : Fin n) (a b : ℝ) :
    ∑ k : Fin n, (if k = i then a else b) * (if k = j then a else b) =
      n * b ^ 2 + 2 * b * (a - b) + (if i = j then (a - b) ^ 2 else 0) := by
  have h : ∀ k : Fin n, (if k = i then a else b) * (if k = j then a else b) =
      b ^ 2 + (if k = i then b * (a - b) else 0) + (if k = j then b * (a - b) else 0) +
        (if k = i then (if i = j then (a - b) ^ 2 else 0) else 0) := by
    intro k
    by_cases hi : k = i <;> by_cases hj : k = j
    · subst hi; subst hj; simp; ring
    · subst hi; simp [hj]; ring
    · subst hj; simp [hi]; ring
    · simp only [hi, hj, if_false]; ring
  rw [Finset.sum_congr rfl (fun k _ => h k)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma X7_star_resp (n : ℕ) (hn : 1 ≤ n) : response (walk (starAdjacency (n+1)) Real.pi) =
    (8 * (((n+1 : ℕ) : ℝ) - 3) / (((n+1 : ℕ) : ℝ) - 1) ^ 2) • leafProjector (n+1) := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hT : transition (walk (starAdjacency (n+1)) Real.pi) =
      Matrix.of fun i j => if i.val = 0 ∧ j.val = 0 then (1 : ℝ) else
        if i.val ≠ 0 ∧ j.val ≠ 0 then (if i = j then (1 - 2 / (n : ℝ)) ^ 2 else (2 / (n : ℝ)) ^ 2)
        else 0 := by
    rw [X7_star_walk n hn]
    ext i j
    simp only [transition, Matrix.of_apply]
    split_ifs <;> simp [Complex.normSq_apply] <;> ring
  rw [response, hT]
  ext i j
  rw [Matrix.sub_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Fin.sum_univ_succ, Matrix.one_apply, leafProjector,
      (Fin.succ_ne_zero _).symm]
  have h2 := X7_sum2 n i j ((1 - 2 / (n : ℝ)) ^ 2) ((2 / (n : ℝ)) ^ 2)
  simp only [mul_ite, ite_mul] at h2
  rw [h2]
  split_ifs
  · field_simp; ring
  · field_simp; ring

lemma X7_Pi_map (d : ℕ) : (uniformProjector d).map Complex.ofReal = X7_Pi d := by
  ext i j; simp [uniformProjector, X7_Pi]

lemma X7_complete_walk (d : ℕ) (hd : 2 ≤ d) (t : ℝ) :
    walk (completeAdjacency d) t =
      Complex.exp (-Complex.I * (t : ℂ)) • X7_Pi d +
        Complex.exp (Complex.I * (t : ℂ) / ((d : ℂ) - 1)) • (1 - X7_Pi d) := by
  have hP := X7_Pi_idem d (by omega)
  have hd1 : (d : ℂ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hsplit : (-Complex.I * (t : ℂ)) • (((d : ℝ) - 1)⁻¹ • completeAdjacency d) =
      (-Complex.I * (t : ℂ)) • X7_Pi d +
        (Complex.I * (t : ℂ) / ((d : ℂ) - 1)) • (1 - X7_Pi d) := by
    rw [X7_complete_eq]
    ext i j
    by_cases h : i = j
    · subst h
      simp [X7_Pi, Complex.real_smul]
      field_simp
      ring
    · simp [X7_Pi, Complex.real_smul, h]
      field_simp
      ring
  have hQ : (1 - X7_Pi d) * (1 - X7_Pi d) = 1 - X7_Pi d := by
    rw [sub_mul, mul_sub, mul_sub, hP]; simp
  have h1 : X7_Pi d * (1 - X7_Pi d) = 0 := by rw [mul_sub, hP]; simp
  have h2 : (1 - X7_Pi d) * X7_Pi d = 0 := by rw [sub_mul, hP]; simp
  unfold walk
  rw [X7_complete_spec d hd, hsplit, Matrix.exp_add_of_commute _ _ (by
      rw [Commute, SemiconjBy, smul_mul_smul, smul_mul_smul, h1, h2, smul_zero, smul_zero]),
    X7_exp_idem _ hP, X7_exp_idem _ hQ]
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_smul, h1, smul_zero, add_zero]
  module

lemma X7_expI (x : ℝ) : Complex.exp (Complex.I * (x : ℂ)) = ⟨Real.cos x, Real.sin x⟩ := by
  apply Complex.ext <;> simp [Complex.exp_re, Complex.exp_im]

lemma X7_complete_trans (d : ℕ) (hd : 2 ≤ d) (t : ℝ) :
    transition (walk (completeAdjacency d) t) = uniformProjector d +
        ((((d : ℝ) - 2) + 2 * Real.cos (d * t / ((d : ℝ) - 1))) / d) •
          (1 - uniformProjector d) := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hd1 : (d : ℝ) - 1 ≠ 0 := by intro h; linarith
  set θ : ℝ := t / ((d : ℝ) - 1) with hθ
  have hcos : Real.cos (d * t / ((d : ℝ) - 1)) = Real.cos (t + θ) := by
    congr 1; rw [hθ]; field_simp; ring
  have ea : Complex.exp (-Complex.I * (t : ℂ)) = ⟨Real.cos t, -Real.sin t⟩ := by
    rw [show -Complex.I * (t : ℂ) = Complex.I * ((-t : ℝ) : ℂ) by push_cast; ring, X7_expI,
      Real.cos_neg, Real.sin_neg]
  have eb : Complex.exp (Complex.I * (t : ℂ) / ((d : ℂ) - 1)) = ⟨Real.cos θ, Real.sin θ⟩ := by
    rw [show Complex.I * (t : ℂ) / ((d : ℂ) - 1) = Complex.I * (θ : ℂ) by
      rw [hθ]; push_cast; ring, X7_expI]
  rw [X7_complete_walk d hd t, ea, eb, hcos, Real.cos_add]
  have ht := Real.sin_sq_add_cos_sq t
  have hθ2 := Real.sin_sq_add_cos_sq θ
  ext i j
  by_cases h : i = j
  · subst h
    simp [transition, X7_Pi, uniformProjector, Complex.normSq_apply]
    field_simp
    linear_combination ht + ((d : ℝ) - 1) ^ 2 * hθ2
  · simp [transition, X7_Pi, uniformProjector, Complex.normSq_apply, Matrix.one_apply, h,
      Complex.div_re, Complex.div_im]
    field_simp
    linear_combination (exp := 1) ht + hθ2

end QAlgorithms.Papers.Independent.Information100.P37

end

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix ComplexConjugate Topology

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    (specNorm (completeAdjacency d))⁻¹ • completeAdjacency d =
      (((d : ℂ) - 1)⁻¹) • completeAdjacency d ∧
    (∀ t : ℝ,
      walk (completeAdjacency d) t =
        Complex.exp (-Complex.I * (t : ℂ)) • (uniformProjector d).map Complex.ofReal +
        Complex.exp (Complex.I * (t : ℂ) / ((d : ℂ) - 1)) •
          (1 - (uniformProjector d).map Complex.ofReal) ∧
      transition (walk (completeAdjacency d) t) = uniformProjector d +
        ((((d : ℝ) - 2) + 2 * Real.cos (d * t / ((d : ℝ) - 1))) / d) •
          (1 - uniformProjector d)) ∧
    (specNorm (starAdjacency d))⁻¹ • starAdjacency d =
      (fun i j => (if i.val = 0 then conj (leafState d j) else 0) +
        (if j.val = 0 then leafState d i else 0)) ∧
    response (walk (starAdjacency d) Real.pi) =
      (8 * ((d : ℝ) - 3) / ((d : ℝ) - 1) ^ 2) • leafProjector d := by
  refine ⟨?_, fun t => ⟨?_, X7_complete_trans d hd t⟩, ?_, ?_⟩
  · rw [X7_complete_spec d hd]
    ext i j
    simp [Complex.real_smul]
  · rw [X7_complete_walk d hd t, X7_Pi_map]
  · obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    rw [X7_star_spec n (by omega)]
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [leafState, starAdjacency, Complex.real_smul]
  · obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    exact X7_star_resp n (by omega)

end
