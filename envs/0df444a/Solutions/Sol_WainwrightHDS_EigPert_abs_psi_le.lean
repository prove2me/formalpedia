-- Prove2me | solution 1 for WainwrightHDS.EigPert.abs_psi_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:49:07.360993+00:00
-- url     : https://prove2.me/submissions/64aef9d2-61cf-4fb2-825a-2c01a11dfa5d

import Mathlib
import Definitions.Def_WainwrightHDS_EigPert_opNorm2
import Definitions.Def_WainwrightHDS_EigPert_ptilde
import Definitions.Def_WainwrightHDS_EigPert_psi

open WainwrightHDS.EigPert Matrix

lemma inner_eq_sum {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = ∑ i : Fin n, x i * y i := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]

lemma norm_sq_eq_sum {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = ∑ i : Fin n, (x i) ^ 2 := by
  rw [← @real_inner_self_eq_norm_sq, inner_eq_sum]
  congr 1; ext i; ring

lemma toEuclideanLin_apply_elem {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    (toEuclideanLin M v) i = ∑ j : Fin n, M i j * v j := by
  change (Matrix.toLpLin 2 2 M v).ofLp i = _
  rw [Matrix.toLpLin_apply]
  rfl

lemma inner_toEuclideanLin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x (toEuclideanLin M y) = ∑ i : Fin n, ∑ j : Fin n, x i * M i j * y j := by
  rw [inner_eq_sum]
  congr 1; ext i
  rw [toEuclideanLin_apply_elem, Finset.mul_sum]
  congr 1; ext j
  ring

lemma inner_toEuclideanLin_left {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (toEuclideanLin A x) y = inner ℝ x (toEuclideanLin Aᵀ y) := by
  rw [real_inner_comm, inner_toEuclideanLin, inner_toEuclideanLin]
  rw [Finset.sum_comm]
  congr 1; ext j
  congr 1; ext i
  simp only [transpose_apply]
  ring

lemma toEuclideanLin_apply_def {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    toEuclideanLin M x = WithLp.toLp 2 (M *ᵥ x.ofLp) :=
  Matrix.toLpLin_apply 2 2 M x

lemma toEuclideanLin_mulVec_comp {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    toEuclideanLin A (toEuclideanLin B x) = toEuclideanLin (A * B) x := by
  rw [toEuclideanLin_apply_def, toEuclideanLin_apply_def, toEuclideanLin_apply_def]
  congr 1
  change A *ᵥ (B *ᵥ x.ofLp) = (A * B) *ᵥ x.ofLp
  exact mulVec_mulVec x.ofLp A B

lemma toEuclideanLin_one {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    toEuclideanLin (1 : Matrix (Fin d) (Fin d) ℝ) x = x := by
  rw [toEuclideanLin_apply_def, one_mulVec]

lemma toEuclideanLin_U_UT {d : ℕ} {U : Matrix (Fin d) (Fin d) ℝ} (hU : U ∈ orthogonalGroup (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    toEuclideanLin U (toEuclideanLin Uᵀ x) = x := by
  rw [toEuclideanLin_mulVec_comp, (mem_orthogonalGroup_iff _ _).mp hU, toEuclideanLin_one]

lemma toEuclideanLin_UT_U {d : ℕ} {U : Matrix (Fin d) (Fin d) ℝ} (hU : U ∈ orthogonalGroup (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    toEuclideanLin Uᵀ (toEuclideanLin U x) = x := by
  rw [toEuclideanLin_mulVec_comp, (mem_orthogonalGroup_iff' _ _).mp hU, toEuclideanLin_one]

lemma inner_toEuclideanLin_conj {d : ℕ} (U P : Matrix (Fin d) (Fin d) ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (toEuclideanLin U x) (toEuclideanLin P (toEuclideanLin U y)) =
      inner ℝ x (toEuclideanLin (Uᵀ * P * U) y) := by
  rw [inner_toEuclideanLin_left, toEuclideanLin_mulVec_comp, toEuclideanLin_mulVec_comp]

lemma inner_toEuclideanLin_U_U {d : ℕ} {U : Matrix (Fin d) (Fin d) ℝ} (hU : U ∈ orthogonalGroup (Fin d) ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (toEuclideanLin U x) (toEuclideanLin U y) = inner ℝ x y := by
  rw [inner_toEuclideanLin_left, toEuclideanLin_UT_U hU y]

lemma norm_toEuclideanLin_U {d : ℕ} {U : Matrix (Fin d) (Fin d) ℝ} (hU : U ∈ orthogonalGroup (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖toEuclideanLin U x‖ = ‖x‖ := by
  have : ‖toEuclideanLin U x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← @real_inner_self_eq_norm_sq, ← @real_inner_self_eq_norm_sq, inner_toEuclideanLin_U_U hU]
  rw [← Real.sqrt_sq (norm_nonneg (toEuclideanLin U x)), this, Real.sqrt_sq (norm_nonneg x)]

lemma norm_toEuclideanLin_UT {d : ℕ} {U : Matrix (Fin d) (Fin d) ℝ} (hU : U ∈ orthogonalGroup (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖toEuclideanLin Uᵀ x‖ = ‖x‖ := by
  have hUT : Uᵀ ∈ orthogonalGroup (Fin d) ℝ := by
    rw [mem_orthogonalGroup_iff'] at hU
    rw [mem_orthogonalGroup_iff]
    exact hU
  exact norm_toEuclideanLin_U hUT x

lemma isHermitian_transpose {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.IsHermitian) :
    Pᵀ = P := by
  have := hP.eq
  rwa [conjTranspose_eq_transpose_of_trivial] at this

lemma isHermitian_conj {d : ℕ} (U : Matrix (Fin d) (Fin d) ℝ) {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : P.IsHermitian) : (Uᵀ * P * U)ᵀ = Uᵀ * P * U := by
  have hPt := isHermitian_transpose hP
  simp [transpose_mul, hPt, mul_assoc]

lemma psi_eq {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.IsHermitian)
    (θstar θhat : EuclideanSpace ℝ (Fin d)) :
    psi θstar P (θhat - θstar) =
      inner ℝ θhat (toEuclideanLin P θhat) - inner ℝ θstar (toEuclideanLin P θstar) := by
  have hPt := isHermitian_transpose hP
  have hsymm : inner ℝ θstar (toEuclideanLin P θhat) = inner ℝ θhat (toEuclideanLin P θstar) := by
    rw [real_inner_comm, inner_toEuclideanLin_left, hPt]
  rw [psi]
  simp only [map_sub, inner_sub_left, inner_sub_right]
  rw [hsymm]
  ring

lemma alpha_zero_eq {n : ℕ} {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {θstar θhat : EuclideanSpace ℝ (Fin (n + 1))} (hU0 : ∀ i, U i 0 = θstar i) :
    (toEuclideanLin Uᵀ θhat) 0 = inner ℝ θhat θstar := by
  rw [toEuclideanLin_apply_elem, inner_eq_sum]
  congr 1; ext i
  simp [transpose_apply, hU0 i, mul_comm]

lemma alpha_star_zero {n : ℕ} {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {θstar : EuclideanSpace ℝ (Fin (n + 1))} (hU : U ∈ orthogonalGroup (Fin (n + 1)) ℝ)
    (hU0 : ∀ i, U i 0 = θstar i) :
    (toEuclideanLin Uᵀ θstar) 0 = 1 := by
  rw [toEuclideanLin_apply_elem]
  have : (∑ j : Fin (n + 1), Uᵀ 0 j * θstar j) = (Uᵀ * U) 0 0 := by
    rw [mul_apply]
    congr 1; ext j
    simp [transpose_apply, hU0 j]
  rw [this, (mem_orthogonalGroup_iff' _ _).mp hU]
  simp

lemma alpha_star_succ {n : ℕ} {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {θstar : EuclideanSpace ℝ (Fin (n + 1))} (hU : U ∈ orthogonalGroup (Fin (n + 1)) ℝ)
    (hU0 : ∀ i, U i 0 = θstar i) (i : Fin n) :
    (toEuclideanLin Uᵀ θstar) i.succ = 0 := by
  rw [toEuclideanLin_apply_elem]
  have : (∑ j : Fin (n + 1), Uᵀ i.succ j * θstar j) = (Uᵀ * U) i.succ 0 := by
    rw [mul_apply]
    congr 1; ext j
    simp [transpose_apply, hU0 j]
  rw [this, (mem_orthogonalGroup_iff' _ _).mp hU]
  simp

lemma inner_theta_star_P {n : ℕ} (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (θstar : EuclideanSpace ℝ (Fin (n + 1)))
    (hU : U ∈ orthogonalGroup (Fin (n + 1)) ℝ) (hU0 : ∀ i, U i 0 = θstar i) :
    inner ℝ θstar (toEuclideanLin P θstar) = (Uᵀ * P * U) 0 0 := by
  have hθ : θstar = toEuclideanLin U (toEuclideanLin Uᵀ θstar) := (toEuclideanLin_U_UT hU θstar).symm
  nth_rw 1 [hθ]
  nth_rw 2 [hθ]
  rw [inner_toEuclideanLin_conj, inner_toEuclideanLin]
  rw [Fin.sum_univ_succ]
  have h0 := alpha_star_zero hU hU0
  have hs := alpha_star_succ hU hU0
  simp only [h0, hs, zero_mul, Finset.sum_const_zero, add_zero]
  rw [Fin.sum_univ_succ]
  simp only [h0, hs, mul_zero, Finset.sum_const_zero, add_zero, one_mul, mul_one]

lemma double_sum_succ {n : ℕ} (f : Fin (n + 1) → Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), f i j) =
      f 0 0 + (∑ j : Fin n, f 0 j.succ) + (∑ i : Fin n, f i.succ 0) + (∑ i : Fin n, ∑ j : Fin n, f i.succ j.succ) := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ (fun j => f 0 j)]
  have h_tail : (∑ i : Fin n, ∑ j : Fin (n + 1), f i.succ j) =
      (∑ i : Fin n, f i.succ 0) + (∑ i : Fin n, ∑ j : Fin n, f i.succ j.succ) := by
    rw [← Finset.sum_add_distrib]
    congr 1; ext i
    rw [Fin.sum_univ_succ]
  rw [h_tail]
  ring

lemma decomp_sum {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hM : Mᵀ = M)
    (α : EuclideanSpace ℝ (Fin (n + 1))) :
    let z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => α i.succ)
    let z_ext : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (Fin.cons (α := fun _ => ℝ) 0 (fun i => α i.succ))
    inner ℝ α (toEuclideanLin M α) =
      (α 0) ^ 2 * M 0 0 +
        2 * α 0 * (∑ i : Fin n, z i * M i.succ 0) +
        inner ℝ z_ext (toEuclideanLin M z_ext) := by
  intro z z_ext
  have hM_symm : ∀ i j, M i j = M j i := fun i j => by
    have := congr_fun (congr_fun hM i) j
    rw [transpose_apply] at this
    exact this.symm
  have h_zext_0 : z_ext 0 = 0 := by
    change (Fin.cons (α := fun _ => ℝ) 0 (fun i => α i.succ)) 0 = 0
    exact Fin.cons_zero (α := fun _ => ℝ) 0 _
  have h_zext_succ : ∀ i : Fin n, z_ext i.succ = α i.succ := fun i => by
    change (Fin.cons (α := fun _ => ℝ) 0 (fun i => α i.succ)) i.succ = α i.succ
    exact Fin.cons_succ (α := fun _ => ℝ) 0 _ i
  have h_z_apply : ∀ i : Fin n, z i = α i.succ := fun _ => rfl
  rw [inner_toEuclideanLin M α α, double_sum_succ (fun i j => α i * M i j * α j)]
  rw [inner_toEuclideanLin M z_ext z_ext, double_sum_succ (fun i j => z_ext i * M i j * z_ext j)]
  simp only [h_zext_0, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add]
  simp only [h_zext_succ, h_z_apply]
  have h1 : (∑ j : Fin n, α 0 * M 0 j.succ * α j.succ) = α 0 * ∑ j : Fin n, α j.succ * M j.succ 0 := by
    rw [Finset.mul_sum]
    congr 1; ext j
    rw [hM_symm 0 j.succ]
    ring
  have h2 : (∑ i : Fin n, α i.succ * M i.succ 0 * α 0) = α 0 * ∑ i : Fin n, α i.succ * M i.succ 0 := by
    rw [Finset.mul_sum]
    congr 1; ext i
    ring
  rw [h1, h2]
  ring

lemma norm_z_eq_sqrt {n : ℕ} (α : EuclideanSpace ℝ (Fin (n + 1))) (hα : ‖α‖ = 1) :
    let z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => α i.succ)
    ‖z‖ = Real.sqrt (1 - (α 0) ^ 2) := by
  intro z
  have hsq : ‖z‖ ^ 2 = 1 - (α 0) ^ 2 := by
    have h1 : ‖α‖ ^ 2 = 1 := by rw [hα, one_pow]
    have h2 : ‖α‖ ^ 2 = (α 0) ^ 2 + ‖z‖ ^ 2 := by
      rw [norm_sq_eq_sum α, norm_sq_eq_sum z, Fin.sum_univ_succ]
    linarith
  rw [← Real.sqrt_sq (norm_nonneg z), hsq]

lemma norm_sq_z_ext {n : ℕ} (α : EuclideanSpace ℝ (Fin (n + 1))) (hα : ‖α‖ = 1) :
    let z_ext : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (Fin.cons (α := fun _ => ℝ) 0 (fun i => α i.succ))
    ‖z_ext‖ ^ 2 = 1 - (α 0) ^ 2 := by
  intro z_ext
  have h1 : ‖α‖ ^ 2 = 1 := by rw [hα, one_pow]
  have h_zext_0 : z_ext 0 = 0 := by
    change (Fin.cons (α := fun _ => ℝ) 0 (fun i => α i.succ)) 0 = 0
    exact Fin.cons_zero (α := fun _ => ℝ) 0 _
  have h_zext_succ : ∀ i : Fin n, z_ext i.succ = α i.succ := fun i => by
    change (Fin.cons (α := fun _ => ℝ) 0 (fun i => α i.succ)) i.succ = α i.succ
    exact Fin.cons_succ (α := fun _ => ℝ) 0 _ i
  have h2 : ‖z_ext‖ ^ 2 = ‖α‖ ^ 2 - (α 0) ^ 2 := by
    rw [norm_sq_eq_sum z_ext, norm_sq_eq_sum α, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [h_zext_0, h_zext_succ, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
    ring
  linarith

lemma abs_inner_toEuclideanLin_le {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    |inner ℝ x (toEuclideanLin M x)| ≤ opNorm2 M * ‖x‖ ^ 2 := by
  have h1 : |inner ℝ x (toEuclideanLin M x)| ≤ ‖x‖ * ‖toEuclideanLin M x‖ :=
    abs_real_inner_le_norm x (toEuclideanLin M x)
  have h2 : ‖toEuclideanLin M x‖ ≤ opNorm2 M * ‖x‖ :=
    ContinuousLinearMap.le_opNorm (Matrix.toEuclideanCLM (𝕜 := ℝ) M) x
  have h3 : ‖x‖ * ‖toEuclideanLin M x‖ ≤ ‖x‖ * (opNorm2 M * ‖x‖) :=
    mul_le_mul_of_nonneg_left h2 (norm_nonneg x)
  have h4 : ‖x‖ * (opNorm2 M * ‖x‖) = opNorm2 M * ‖x‖ ^ 2 := by ring
  linarith

set_option linter.deprecated false in
lemma abs_entry_zero_zero_le_opNorm2 {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    |M 0 0| ≤ opNorm2 M := by
  let e0 : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
  have he0_norm_sq : ‖e0‖ ^ 2 = 1 := by
    rw [norm_sq_eq_sum, Fin.sum_univ_succ]
    have h0 : e0 0 = 1 := by
      change (EuclideanSpace.single 0 (1 : ℝ)).ofLp 0 = 1
      rw [EuclideanSpace.single_apply]
      simp
    have hs : ∀ i : Fin n, e0 i.succ = 0 := by
      intro i
      change (EuclideanSpace.single 0 (1 : ℝ)).ofLp i.succ = 0
      rw [EuclideanSpace.single_apply]
      simp
    simp [h0, hs]
  have h_inner : inner ℝ e0 (toEuclideanLin M e0) = M 0 0 := by
    rw [inner_eq_sum, Fin.sum_univ_succ]
    have h0 : e0 0 = 1 := by
      change (EuclideanSpace.single 0 (1 : ℝ)).ofLp 0 = 1
      rw [EuclideanSpace.single_apply]
      simp
    have hs : ∀ i : Fin n, e0 i.succ = 0 := by
      intro i
      change (EuclideanSpace.single 0 (1 : ℝ)).ofLp i.succ = 0
      rw [EuclideanSpace.single_apply]
      simp
    have h_toLin : toEuclideanLin M e0 0 = M 0 0 := by
      rw [toEuclideanLin_apply_elem, Fin.sum_univ_succ]
      simp [h0, hs]
    simp [h0, hs, h_toLin]
  have h_bound : |inner ℝ e0 (toEuclideanLin M e0)| ≤ opNorm2 M * ‖e0‖ ^ 2 :=
    abs_inner_toEuclideanLin_le M e0
  rw [h_inner, he0_norm_sq, mul_one] at h_bound
  exact h_bound

lemma theta_star_norm {n : ℕ} {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {θstar : EuclideanSpace ℝ (Fin (n + 1))} (hU : U ∈ orthogonalGroup (Fin (n + 1)) ℝ)
    (hU0 : ∀ i, U i 0 = θstar i) :
    ‖θstar‖ = 1 := by
  have hsq : ‖θstar‖ ^ 2 = 1 := by
    rw [norm_sq_eq_sum]
    have : (∑ i : Fin (n + 1), (θstar i) ^ 2) = (Uᵀ * U) 0 0 := by
      rw [mul_apply]
      congr 1; ext i
      simp [transpose_apply, hU0 i, sq]
    rw [this, (mem_orthogonalGroup_iff' _ _).mp hU]
    simp
  rw [← Real.sqrt_sq (norm_nonneg θstar), hsq, Real.sqrt_one]

lemma rho_le_one {n : ℕ} {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {θstar : EuclideanSpace ℝ (Fin (n + 1))} (hU : U ∈ orthogonalGroup (Fin (n + 1)) ℝ)
    (hU0 : ∀ i, U i 0 = θstar i) (θhat : EuclideanSpace ℝ (Fin (n + 1))) (hθhat : ‖θhat‖ = 1) :
    inner ℝ θhat θstar ≤ 1 := by
  have h := real_inner_le_norm θhat θstar
  rw [hθhat, theta_star_norm hU hU0, mul_one] at h
  exact h

lemma abs_sq_sub_one {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    |ρ ^ 2 - 1| = 1 - ρ ^ 2 := by
  have : ρ ^ 2 ≤ 1 := by nlinarith
  have hneg : ρ ^ 2 - 1 ≤ 0 := by linarith
  rw [abs_of_nonpos hneg]
  ring

open WainwrightHDS.EigPert Matrix in
theorem solution {n : ℕ} (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
    (θstar : EuclideanSpace ℝ (Fin (n + 1))) (hU0 : ∀ i, U i 0 = θstar i)
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hP : P.IsHermitian)
    (θhat : EuclideanSpace ℝ (Fin (n + 1))) (hθhat : ‖θhat‖ = 1)
    (hρ : 0 ≤ inner ℝ θhat θstar) :
    |psi θstar P (θhat - θstar)| ≤
      2 * (1 - (inner ℝ θhat θstar) ^ 2) * opNorm2 (Uᵀ * P * U) +
        2 * inner ℝ θhat θstar * Real.sqrt (1 - (inner ℝ θhat θstar) ^ 2) * ‖ptilde U P‖ := by
  let Ptilde := Uᵀ * P * U
  have hPtilde_symm : Ptildeᵀ = Ptilde := isHermitian_conj U hP
  let α : EuclideanSpace ℝ (Fin (n + 1)) := toEuclideanLin Uᵀ θhat
  have hα_norm : ‖α‖ = 1 := by
    change ‖toEuclideanLin Uᵀ θhat‖ = 1
    rw [norm_toEuclideanLin_UT hU, hθhat]
  have hα0 : α 0 = inner ℝ θhat θstar := alpha_zero_eq hU0
  let ρ := inner ℝ θhat θstar
  have hρ_le1 : ρ ≤ 1 := rho_le_one hU hU0 θhat hθhat
  have hθhat_decomp : θhat = toEuclideanLin U α := (toEuclideanLin_U_UT hU θhat).symm

  let z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => α i.succ)
  let z_ext : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (Fin.cons (α := fun _ => ℝ) 0 (fun i => α i.succ))

  have h_psi : psi θstar P (θhat - θstar) =
      (ρ ^ 2 - 1) * Ptilde 0 0 +
        2 * ρ * inner ℝ z (ptilde U P) +
        inner ℝ z_ext (toEuclideanLin Ptilde z_ext) := by
    rw [psi_eq hP]
    rw [inner_theta_star_P U P θstar hU hU0]
    rw [hθhat_decomp]
    rw [inner_toEuclideanLin_conj]
    have h_decomp := decomp_sum Ptilde hPtilde_symm α
    dsimp [z, z_ext] at h_decomp ⊢
    rw [h_decomp, hα0]
    have hz_ptilde : (∑ i : Fin n, z i * Ptilde i.succ 0) = inner ℝ z (ptilde U P) := by
      rw [inner_eq_sum]
      rfl
    rw [hz_ptilde]
    ring

  have h_tri : |psi θstar P (θhat - θstar)| ≤
      |(ρ ^ 2 - 1) * Ptilde 0 0| +
        |2 * ρ * inner ℝ z (ptilde U P)| +
        |inner ℝ z_ext (toEuclideanLin Ptilde z_ext)| := by
    rw [h_psi]
    have h1 := abs_add_le ((ρ ^ 2 - 1) * Ptilde 0 0 + 2 * ρ * inner ℝ z (ptilde U P))
      (inner ℝ z_ext (toEuclideanLin Ptilde z_ext))
    have h2 := abs_add_le ((ρ ^ 2 - 1) * Ptilde 0 0) (2 * ρ * inner ℝ z (ptilde U P))
    linarith

  have h_term1 : |(ρ ^ 2 - 1) * Ptilde 0 0| ≤ (1 - ρ ^ 2) * opNorm2 Ptilde := by
    rw [abs_mul, abs_sq_sub_one hρ hρ_le1]
    have := abs_entry_zero_zero_le_opNorm2 Ptilde
    have h_nonneg : 0 ≤ 1 - ρ ^ 2 := by
      have : ρ ^ 2 ≤ 1 := by nlinarith
      linarith
    exact mul_le_mul_of_nonneg_left this h_nonneg

  have h_term2 : |2 * ρ * inner ℝ z (ptilde U P)| ≤ 2 * ρ * Real.sqrt (1 - ρ ^ 2) * ‖ptilde U P‖ := by
    have h_pos : 0 ≤ 2 * ρ := by linarith
    have h_abs_inner := abs_real_inner_le_norm z (ptilde U P)
    have hz_norm : ‖z‖ = Real.sqrt (1 - ρ ^ 2) := by
      have := norm_z_eq_sqrt α hα_norm
      dsimp [z] at this ⊢
      rwa [hα0] at this
    rw [hz_norm] at h_abs_inner
    rw [abs_mul, abs_of_nonneg h_pos]
    have := mul_le_mul_of_nonneg_left h_abs_inner h_pos
    linarith

  have h_term3 : |inner ℝ z_ext (toEuclideanLin Ptilde z_ext)| ≤ (1 - ρ ^ 2) * opNorm2 Ptilde := by
    have h_bound := abs_inner_toEuclideanLin_le Ptilde z_ext
    have hz_ext_norm_sq : ‖z_ext‖ ^ 2 = 1 - ρ ^ 2 := by
      have := norm_sq_z_ext α hα_norm
      dsimp [z_ext] at this ⊢
      rwa [hα0] at this
    rw [hz_ext_norm_sq] at h_bound
    linarith

  linarith
