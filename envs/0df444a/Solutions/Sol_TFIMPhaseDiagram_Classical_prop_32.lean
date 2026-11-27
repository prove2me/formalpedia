-- Prove2me | solution 1 for TFIMPhaseDiagram.Classical.prop_32
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:10:51.637309+00:00
-- url     : https://prove2.me/submissions/3cfb9225-fbf9-41f8-b3f9-5f16ac9a6dba

import Definitions.Def_TFIMPhaseDiagram_Classical_traceSetup

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.Operator
noncomputable section

namespace TFIMPhaseDiagram.Classical.P32

open Matrix

variable {d : ℕ}

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

lemma unitary_inv (V : Mat d) (hV : V ∈ unitaryGroup (Fin d) ℂ) : V⁻¹ = star V := by
  rw [mem_unitaryGroup_iff] at hV
  exact inv_eq_right_inv hV

lemma unitary_isUnit (V : Mat d) (hV : V ∈ unitaryGroup (Fin d) ℂ) : IsUnit V := by
  rw [mem_unitaryGroup_iff] at hV
  exact ⟨⟨V, star V, hV, mul_eq_one_comm.mp hV⟩, rfl⟩

lemma exp_herm (H : Mat d) (hH : H.IsHermitian) (s : ℝ) :
    NormedSpace.exp (s • H) =
      hH.eigenvectorUnitary.1 *
        diagonal (fun a => ((Real.exp (s * hH.eigenvalues a) : ℝ) : ℂ)) *
        star hH.eigenvectorUnitary.1 := by
  set V : Mat d := hH.eigenvectorUnitary.1
  have hVu : V ∈ unitaryGroup (Fin d) ℂ := hH.eigenvectorUnitary.2
  have hspec : H = V * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star V := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  have h1 : s • H = V * diagonal (fun a => ((s * hH.eigenvalues a : ℝ) : ℂ)) * V⁻¹ := by
    have := congrArg (fun X => s • X) hspec
    rw [this, unitary_inv V hVu]
    have hd : (diagonal fun a => (((s * hH.eigenvalues a : ℝ)) : ℂ)) =
        s • diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
      rw [← diagonal_smul]; congr 1; funext a; simp [Complex.real_smul]
    rw [hd, mul_smul_comm, smul_mul_assoc]
  rw [h1, exp_conj _ _ (unitary_isUnit V hVu), exp_diagonal, unitary_inv V hVu]
  congr 2
  funext a
  simp only [Pi.exp_def]
  simp [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]


def Qf (lam : Fin d → ℝ) (x : Fin d → Fin d → ℂ) : ℝ :=
  ∑ a, ∑ b, Real.exp (lam a) * ‖x a b‖ ^ 2

lemma Qf_nonneg (lam : Fin d → ℝ) (x : Fin d → Fin d → ℂ) : 0 ≤ Qf lam x := by
  unfold Qf; positivity

lemma weighted_le (lam : Fin d → ℝ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (x : Fin d → Fin d → ℂ) (hx : ∀ a b, ‖x a b‖ = ‖x b a‖) :
    ∑ a, ∑ b, Real.exp (s * lam a) * Real.exp ((1 - s) * lam b) * ‖x a b‖ ^ 2 ≤ Qf lam x := by
  have hw : ∀ a b, Real.exp (s * lam a) * Real.exp ((1 - s) * lam b) ≤
      s * Real.exp (lam a) + (1 - s) * Real.exp (lam b) := by
    intro a b
    rw [← Real.exp_add]
    have := convexOn_exp.2 (Set.mem_univ (lam a)) (Set.mem_univ (lam b)) hs0 (by linarith)
      (by ring : s + (1 - s) = 1)
    simpa [smul_eq_mul] using this
  calc ∑ a, ∑ b, Real.exp (s * lam a) * Real.exp ((1 - s) * lam b) * ‖x a b‖ ^ 2
      ≤ ∑ a, ∑ b, (s * Real.exp (lam a) + (1 - s) * Real.exp (lam b)) * ‖x a b‖ ^ 2 := by
        gcongr with a _ b _; exact hw a b
    _ = s * (∑ a, ∑ b, Real.exp (lam a) * ‖x a b‖ ^ 2) +
        (1 - s) * (∑ a, ∑ b, Real.exp (lam b) * ‖x a b‖ ^ 2) := by
        simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> (apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring)
    _ = Qf lam x := by
        have : (∑ a, ∑ b, Real.exp (lam b) * ‖x a b‖ ^ 2) = Qf lam x := by
          unfold Qf; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
          rw [hx]
        rw [this]; unfold Qf; ring

lemma cs_bound (lam : Fin d → ℝ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (x y : Fin d → Fin d → ℂ) (hx : ∀ a b, ‖x a b‖ = ‖x b a‖) (hy : ∀ a b, ‖y a b‖ = ‖y b a‖) :
    ‖∑ a, ∑ b, (Real.exp (s * lam a) : ℂ) * x a b * (Real.exp ((1 - s) * lam b) : ℂ) * y b a‖ ≤
      Real.sqrt (Qf lam x) * Real.sqrt (Qf lam y) := by
  set w : Fin d → Fin d → ℝ := fun a b => Real.exp (s * lam a) * Real.exp ((1 - s) * lam b)
  have hw0 : ∀ a b, 0 ≤ w a b := fun a b => by positivity
  have h1 : ‖∑ a, ∑ b, (Real.exp (s * lam a) : ℂ) * x a b * (Real.exp ((1 - s) * lam b) : ℂ) * y b a‖
      ≤ ∑ p : Fin d × Fin d, (Real.sqrt (w p.1 p.2) * ‖x p.1 p.2‖) * (Real.sqrt (w p.1 p.2) * ‖y p.2 p.1‖) := by
    rw [← Fintype.sum_prod_type']
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    apply Finset.sum_congr rfl; intro p _
    have : Real.sqrt (w p.1 p.2) * ‖x p.1 p.2‖ * (Real.sqrt (w p.1 p.2) * ‖y p.2 p.1‖) =
        w p.1 p.2 * ‖x p.1 p.2‖ * ‖y p.2 p.1‖ := by
      have := Real.mul_self_sqrt (hw0 p.1 p.2)
      calc Real.sqrt (w p.1 p.2) * ‖x p.1 p.2‖ * (Real.sqrt (w p.1 p.2) * ‖y p.2 p.1‖)
          = (Real.sqrt (w p.1 p.2) * Real.sqrt (w p.1 p.2)) * ‖x p.1 p.2‖ * ‖y p.2 p.1‖ := by ring
        _ = _ := by rw [this]
    rw [this]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), w]
    ring
  refine h1.trans ((Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_)
  have e1 : ∀ (z : Fin d → Fin d → ℂ) (σ : Fin d × Fin d → Fin d × Fin d),
      (∑ p : Fin d × Fin d, (Real.sqrt (w p.1 p.2) * ‖z (σ p).1 (σ p).2‖) ^ 2) =
      ∑ a, ∑ b, w a b * ‖z (σ (a, b)).1 (σ (a,b)).2‖ ^ 2 := by
    intro z σ
    rw [← Fintype.sum_prod_type']
    apply Finset.sum_congr rfl; intro p _
    rw [mul_pow, Real.sq_sqrt (hw0 _ _)]
  have ex := e1 x id
  have ey := e1 y Prod.swap
  simp only [id, Prod.swap] at ex ey
  rw [ex, ey]
  gcongr
  · exact weighted_le lam s hs0 hs1 x hx
  · have := weighted_le lam s hs0 hs1 (fun a b => y b a) (fun a b => hy b a)
    refine this.trans (le_of_eq ?_)
    unfold Qf
    apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; rw [hy]


lemma opnorm_bound (C : Mat d) (v : Fin d → ℂ) (hv : ∑ k, ‖v k‖ ^ 2 = 1) :
    ∑ k, ‖(C *ᵥ v) k‖ ^ 2 ≤ (euclideanOpNorm C) ^ 2 := by
  set x : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 v
  have hx : ‖x‖ = 1 := by
    rw [EuclideanSpace.norm_eq]; simp [x, hv]
  set r := ‖WithLp.toLp 2 (C.mulVec (fun i => x i))‖
  have hr : r ^ 2 = ∑ k, ‖(C *ᵥ v) k‖ ^ 2 := by
    simp only [r, EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (by positivity)]
  have hmem : r ∈ {r | ∃ x : EuclideanSpace ℂ (Fin d), ‖x‖ = 1 ∧
      r = ‖WithLp.toLp 2 (C.mulVec (fun i => x i))‖} := ⟨x, hx, rfl⟩
  have hbdd : BddAbove {r | ∃ x : EuclideanSpace ℂ (Fin d), ‖x‖ = 1 ∧
      r = ‖WithLp.toLp 2 (C.mulVec (fun i => x i))‖} := by
    open scoped Matrix.Norms.L2Operator in
    refine ⟨‖C‖, ?_⟩
    rintro r ⟨y, hy, rfl⟩
    have := Matrix.l2_opNorm_mulVec C y
    rw [hy, mul_one] at this
    exact this
  have hle : r ≤ euclideanOpNorm C := le_csSup hbdd hmem
  rw [← hr]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

lemma tr_diag_sandwich (e f : Fin d → ℂ) (M N : Mat d) :
    trace (diagonal e * M * diagonal f * N) = ∑ a, ∑ b, e a * M a b * f b * N b a := by
  simp only [trace, diag]
  apply Finset.sum_congr rfl; intro a _
  rw [mul_apply]
  apply Finset.sum_congr rfl; intro b _
  rw [mul_diagonal, diagonal_mul]


lemma tr_coords (H X S : Mat d) (hH : H.IsHermitian) (s : ℝ) :
    trace (NormedSpace.exp (s • H) * X * NormedSpace.exp ((1 - s) • H) * S) =
      ∑ a, ∑ b, ((Real.exp (s * hH.eigenvalues a) : ℝ) : ℂ) *
        (star hH.eigenvectorUnitary.1 * X * hH.eigenvectorUnitary.1) a b *
        ((Real.exp ((1 - s) * hH.eigenvalues b) : ℝ) : ℂ) *
        (star hH.eigenvectorUnitary.1 * S * hH.eigenvectorUnitary.1) b a := by
  rw [exp_herm H hH s, exp_herm H hH (1 - s), ← tr_diag_sandwich]
  set V := hH.eigenvectorUnitary.1
  set E1 := diagonal (fun a => ((Real.exp (s * hH.eigenvalues a) : ℝ) : ℂ))
  set E2 := diagonal (fun a => ((Real.exp ((1 - s) * hH.eigenvalues a) : ℝ) : ℂ))
  have : V * E1 * star V * X * (V * E2 * star V) * S =
      V * (E1 * (star V * X * V) * E2 * (star V * S)) := by
    simp only [Matrix.mul_assoc]
  rw [this, trace_mul_comm]
  simp only [Matrix.mul_assoc]


lemma rownorm (M : Mat d) (a : Fin d) : ∑ b, ‖M a b‖ ^ 2 = ((M * Mᴴ) a a).re := by
  rw [mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl; intro b _
  rw [conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

lemma colnorm (M : Mat d) (a : Fin d) : ∑ b, ‖M b a‖ ^ 2 = ((Mᴴ * M) a a).re := by
  rw [mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl; intro b _
  rw [conjTranspose_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

lemma conj_herm (V X : Mat d) (hX : X.IsHermitian) : (star V * X * V).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, hX.eq]
  simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

lemma herm_norm_symm (M : Mat d) (hM : M.IsHermitian) (a b : Fin d) : ‖M a b‖ = ‖M b a‖ := by
  rw [← hM.apply a b, norm_star]

lemma unit_mul_star (V : Mat d) (hV : V ∈ unitaryGroup (Fin d) ℂ) : V * star V = 1 :=
  (mem_unitaryGroup_iff).1 hV

lemma star_mul_unit (V : Mat d) (hV : V ∈ unitaryGroup (Fin d) ℂ) : star V * V = 1 :=
  (mem_unitaryGroup_iff').1 hV

lemma Qf_S (lam : Fin d → ℝ) (V S : Mat d) (hV : V ∈ unitaryGroup (Fin d) ℂ)
    (hS : S.IsHermitian) (hSS : S * S = 1) :
    Qf lam (fun a b => (star V * S * V) a b) = ∑ a, Real.exp (lam a) := by
  unfold Qf
  apply Finset.sum_congr rfl; intro a _
  rw [← Finset.mul_sum, rownorm]
  have : star V * S * V * (star V * S * V)ᴴ = 1 := by
    rw [conjTranspose_mul, conjTranspose_mul, hS.eq, ← Matrix.star_eq_conjTranspose,
      ← Matrix.star_eq_conjTranspose, star_star]
    calc _ = star V * S * (V * star V) * S * V := by
          simp only [Matrix.mul_assoc]
      _ = star V * (S * S) * V := by rw [unit_mul_star V hV]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = 1 := by rw [hSS, Matrix.mul_one, star_mul_unit V hV]
  rw [this]; simp


lemma row_center (M : Mat d) (c : ℝ) (a : Fin d) :
    ∑ b, ‖(M - (c : ℂ) • (1 : Mat d)) a b‖ ^ 2 = ∑ b, ‖M a b‖ ^ 2 - 2 * c * (M a a).re + c ^ 2 := by
  have h : ∀ b, ‖(M - (c : ℂ) • (1 : Mat d)) a b‖ ^ 2 =
      ‖M a b‖ ^ 2 - (if a = b then 2 * c * (M a a).re - c ^ 2 else 0) := by
    intro b
    by_cases hab : a = b
    · subst hab
      simp only [Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, if_true]
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
      simp [Complex.normSq_ofReal, Complex.mul_re]
      ring
    · simp [Matrix.sub_apply, one_apply_ne hab, hab]
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

lemma Qf_center (lam : Fin d → ℝ) (M : Mat d) (c : ℝ) :
    Qf lam (fun a b => (M - (c : ℂ) • (1 : Mat d)) a b) =
      Qf lam (fun a b => M a b) - 2 * c * ∑ a, Real.exp (lam a) * (M a a).re +
        c ^ 2 * ∑ a, Real.exp (lam a) := by
  calc Qf lam (fun a b => (M - (c : ℂ) • (1 : Mat d)) a b)
      = ∑ a, Real.exp (lam a) * (∑ b, ‖M a b‖ ^ 2 - 2 * c * (M a a).re + c ^ 2) := by
        unfold Qf; apply Finset.sum_congr rfl; intro a _; rw [← Finset.mul_sum, row_center]
    _ = ∑ a, (Real.exp (lam a) * ∑ b, ‖M a b‖ ^ 2) - 2 * c * ∑ a, Real.exp (lam a) * (M a a).re +
        c ^ 2 * ∑ a, Real.exp (lam a) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro a _; ring
    _ = _ := by
        unfold Qf; congr 2
        apply Finset.sum_congr rfl; intro a _; rw [Finset.mul_sum]

lemma Qf_C_le (lam : Fin d → ℝ) (V C : Mat d) (hV : V ∈ unitaryGroup (Fin d) ℂ)
    (hC : C.IsHermitian) :
    Qf lam (fun a b => (star V * C * V) a b) ≤ (∑ a, Real.exp (lam a)) * (euclideanOpNorm C) ^ 2 := by
  unfold Qf
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum; intro a _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hsym := herm_norm_symm _ (conj_herm V C hC)
  rw [show (∑ b, ‖(star V * C * V) a b‖ ^ 2) = ∑ b, ‖(star V * C * V) b a‖ ^ 2 from
    Finset.sum_congr rfl (fun b _ => by rw [hsym])]
  rw [colnorm]
  have e : (star V * C * V)ᴴ * (star V * C * V) = (C * V)ᴴ * (C * V) := by
    rw [conjTranspose_mul, conjTranspose_mul, hC.eq, ← Matrix.star_eq_conjTranspose (star V), star_star,
      conjTranspose_mul, hC.eq]
    rw [← Matrix.star_eq_conjTranspose V]
    calc _ = star V * C * (V * star V) * C * V := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [unit_mul_star V hV, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e, ← colnorm]
  have hv : ∑ k, ‖V k a‖ ^ 2 = 1 := by
    rw [colnorm, ← Matrix.star_eq_conjTranspose, star_mul_unit V hV]; simp
  have := opnorm_bound C (fun k => V k a) hv
  refine le_of_eq_of_le ?_ this
  apply Finset.sum_congr rfl; intro k _
  rfl


lemma tr_exp_mul (H M : Mat d) (hH : H.IsHermitian) :
    trace (NormedSpace.exp H * M) =
      ∑ a, ((Real.exp (hH.eigenvalues a) : ℝ) : ℂ) *
        (star hH.eigenvectorUnitary.1 * M * hH.eigenvectorUnitary.1) a a := by
  have := exp_herm H hH 1
  rw [one_smul] at this
  rw [this]
  set V := hH.eigenvectorUnitary.1
  rw [show V * diagonal (fun a => ((Real.exp (1 * hH.eigenvalues a) : ℝ) : ℂ)) * star V * M =
      V * (diagonal (fun a => ((Real.exp (1 * hH.eigenvalues a) : ℝ) : ℂ)) * (star V * M)) by
      simp only [Matrix.mul_assoc], trace_mul_comm]
  simp only [trace, diag, Matrix.mul_assoc, diagonal_mul, one_mul]

lemma tr_exp_eq (H : Mat d) (hH : H.IsHermitian) :
    trace (NormedSpace.exp H) = ((∑ a, Real.exp (hH.eigenvalues a) : ℝ) : ℂ) := by
  have := tr_exp_mul H 1 hH
  rw [Matrix.mul_one, Matrix.mul_one, star_mul_unit _ hH.eigenvectorUnitary.2] at this
  rw [this]; push_cast; simp

lemma opNorm_nonneg (C : Mat d) : 0 ≤ euclideanOpNorm C := by
  unfold euclideanOpNorm
  apply Real.sSup_nonneg
  rintro r ⟨x, -, rfl⟩; exact norm_nonneg _

lemma integrand_bound (H C S : Mat d) (hH : H.IsHermitian) (hC : C.IsHermitian)
    (hS : S.IsHermitian) (hSS : S * S = 1) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (c : ℝ)
    (hc : c * (∑ a, Real.exp (hH.eigenvalues a)) = (trace (NormedSpace.exp H * C)).re) :
    ‖trace (NormedSpace.exp (s • H) * (C - (c : ℂ) • (1 : Mat d)) *
        NormedSpace.exp ((1 - s) • H) * S)‖ ≤
      (∑ a, Real.exp (hH.eigenvalues a)) * euclideanOpNorm C := by
  set lam := hH.eigenvalues
  set V := hH.eigenvectorUnitary.1
  have hV : V ∈ unitaryGroup (Fin d) ℂ := hH.eigenvectorUnitary.2
  set z := ∑ a, Real.exp (lam a)
  have hz : 0 ≤ z := by positivity
  rw [tr_coords H _ S hH s]
  have hX : (star V * (C - (c : ℂ) • (1 : Mat d)) * V) = star V * C * V - (c : ℂ) • (1 : Mat d) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      star_mul_unit V hV]
  have hXh : (star V * (C - (c : ℂ) • (1 : Mat d)) * V).IsHermitian := by
    apply conj_herm
    unfold IsHermitian
    rw [conjTranspose_sub, hC.eq, conjTranspose_smul, conjTranspose_one]
    simp
  refine (cs_bound lam s hs0 hs1 _ _ (herm_norm_symm _ hXh)
    (herm_norm_symm _ (conj_herm V S hS))).trans ?_
  have hQS := Qf_S lam V S hV hS hSS
  have hQX : Qf lam (fun a b => (star V * (C - (c : ℂ) • (1 : Mat d)) * V) a b) ≤
      z * euclideanOpNorm C ^ 2 := by
    rw [hX, Qf_center]
    have htr := tr_exp_mul H C hH
    have hre : (∑ a, Real.exp (lam a) * ((star V * C * V) a a).re) = c * z := by
      rw [hc, htr, Complex.re_sum]
      apply Finset.sum_congr rfl; intro a _
      rw [Complex.re_ofReal_mul]
    rw [hre]
    have := Qf_C_le lam V C hV hC
    nlinarith [sq_nonneg c, hz]
  rw [hQS]
  calc Real.sqrt (Qf lam _) * Real.sqrt z ≤ Real.sqrt (z * euclideanOpNorm C ^ 2) * Real.sqrt z := by
        gcongr
    _ = z * euclideanOpNorm C := by
        rw [Real.sqrt_mul hz, Real.sqrt_sq (opNorm_nonneg C)]
        rw [mul_comm (Real.sqrt z), mul_assoc, Real.mul_self_sqrt hz]; ring


section Calc
open scoped Matrix.Norms.Operator

def trCLM (d : ℕ) : Mat d →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin d) ℝ ℂ)

lemma trCLM_apply (M : Mat d) : trCLM d M = trace M := rfl

lemma hasDerivAt_tr {f : ℝ → Mat d} {f' : Mat d} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => trace (f t)) (trace f') x := by
  exact (trCLM d).hasFDerivAt.comp_hasDerivAt x hf

lemma duhamel_deriv (A B S : Mat d) (s : ℝ) :
    HasDerivAt (fun u : ℝ => trace (NormedSpace.exp (u • (A + B)) * NormedSpace.exp ((1 - u) • A) * S))
      (trace (NormedSpace.exp (s • (A + B)) * B * NormedSpace.exp ((1 - s) • A) * S)) s := by
  have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (A + B)))
      (NormedSpace.exp (s • (A + B)) * (A + B)) s := hasDerivAt_exp_smul_const (A + B) s
  have h2' : HasDerivAt (fun v : ℝ => NormedSpace.exp (v • A)) (A * NormedSpace.exp ((1 - s) • A)) (1 - s) :=
    hasDerivAt_exp_smul_const' A (1 - s)
  have hl : HasDerivAt (fun u : ℝ => 1 - u) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have h2 : HasDerivAt (fun u : ℝ => NormedSpace.exp ((1 - u) • A))
      ((-1 : ℝ) • (A * NormedSpace.exp ((1 - s) • A))) s := h2'.scomp s hl
  have h3 := ((h1.fun_mul h2).mul_const S)
  have e : (NormedSpace.exp (s • (A + B)) * (A + B) * NormedSpace.exp ((1 - s) • A) +
        NormedSpace.exp (s • (A + B)) * ((-1 : ℝ) • (A * NormedSpace.exp ((1 - s) • A)))) * S =
      NormedSpace.exp (s • (A + B)) * B * NormedSpace.exp ((1 - s) • A) * S := by
    rw [neg_one_smul]
    noncomm_ring
  rw [e] at h3
  exact hasDerivAt_tr h3

lemma cont_integrand (A C S : Mat d) :
    Continuous (fun p : ℝ × ℝ => trace (NormedSpace.exp (p.2 • (A + p.1 • C)) * C *
      NormedSpace.exp ((1 - p.2) • A) * S)) := by
  have he : Continuous (NormedSpace.exp : Mat d → Mat d) := NormedSpace.exp_continuous
  have h1 : Continuous (fun p : ℝ × ℝ => NormedSpace.exp (p.2 • (A + p.1 • C))) :=
    he.comp (continuous_snd.smul (continuous_const.add (continuous_fst.smul continuous_const)))
  have h2 : Continuous (fun p : ℝ × ℝ => NormedSpace.exp ((1 - p.2) • A)) :=
    he.comp ((continuous_const.sub continuous_snd).smul continuous_const)
  exact (trCLM d).continuous.comp (((h1.mul continuous_const).mul h2).mul continuous_const)

lemma duhamel (A B S : Mat d) :
    trace (NormedSpace.exp (A + B) * S) - trace (NormedSpace.exp A * S) =
      ∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • (A + B)) * B * NormedSpace.exp ((1 - s) • A) * S) := by
  have hc : Continuous (fun s : ℝ => trace (NormedSpace.exp (s • (A + B)) * B *
      NormedSpace.exp ((1 - s) • A) * S)) := by
    have := (cont_integrand A B S).comp (continuous_const.prodMk continuous_id : Continuous (fun s : ℝ => ((1:ℝ), s)))
    simpa [Function.comp_def, one_smul] using this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => duhamel_deriv A B S s)
    (hc.intervalIntegrable _ _)]
  simp

lemma hasDerivAt_trexp (K C S : Mat d) (t : ℝ) :
    HasDerivAt (fun u : ℝ => trace (NormedSpace.exp (K + u • C) * S))
      (∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • (K + t • C)) * C *
        NormedSpace.exp ((1 - s) • (K + t • C)) * S)) t := by
  set A := K + t • C
  set Φ : ℝ → ℂ := fun h => ∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • (A + h • C)) * C *
      NormedSpace.exp ((1 - s) • A) * S)
  have hΦc : Continuous Φ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (cont_integrand A C S) 0 1
  have hdiff : ∀ h : ℝ, trace (NormedSpace.exp (K + (t + h) • C) * S) -
      trace (NormedSpace.exp (K + t • C) * S) = (h : ℂ) * Φ h := by
    intro h
    have e : K + (t + h) • C = A + h • C := by simp only [A, add_smul, add_assoc]
    rw [e, duhamel]
    simp only [Φ]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro s _
    simp only
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, trace_smul, Complex.real_smul]
  have hΦ0 : Φ 0 = ∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • A) * C *
      NormedSpace.exp ((1 - s) • A) * S) := by simp [Φ]
  rw [← hΦ0, hasDerivAt_iff_tendsto_slope_zero]
  have hT : Filter.Tendsto Φ (nhdsWithin 0 {0}ᶜ) (nhds (Φ 0)) :=
    (hΦc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [hdiff h, Complex.real_smul, ← mul_assoc]
  have : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  push_cast
  rw [inv_mul_cancel₀ this, one_mul]

lemma exp_smul_mul (H : Mat d) (a b : ℝ) :
    NormedSpace.exp (a • H) * NormedSpace.exp (b • H) = NormedSpace.exp ((a + b) • H) := by
  rw [add_smul, Matrix.exp_add_of_commute _ _ ((Commute.refl H).smul_left a |>.smul_right b)]

lemma int_center (H C S : Mat d) (c : ℝ) :
    (∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • H) * C * NormedSpace.exp ((1 - s) • H) * S)) -
      (c : ℂ) * trace (NormedSpace.exp H * S) =
    ∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • H) * (C - (c : ℂ) • (1 : Mat d)) *
      NormedSpace.exp ((1 - s) • H) * S) := by
  have hc1 : Continuous (fun s : ℝ => trace (NormedSpace.exp (s • H) * C *
      NormedSpace.exp ((1 - s) • H) * S)) := by
    have := (cont_integrand H C S).comp (continuous_const.prodMk continuous_id : Continuous (fun s : ℝ => ((0:ℝ), s)))
    simpa [Function.comp_def] using this
  have hconst : ∀ s : ℝ, trace (NormedSpace.exp (s • H) * ((c : ℂ) • (1 : Mat d)) *
      NormedSpace.exp ((1 - s) • H) * S) = (c : ℂ) * trace (NormedSpace.exp H * S) := by
    intro s
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, exp_smul_mul, Matrix.smul_mul, trace_smul,
      smul_eq_mul]
    congr 3; simp
  have : (∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • H) * ((c : ℂ) • (1 : Mat d)) *
      NormedSpace.exp ((1 - s) • H) * S)) = (c : ℂ) * trace (NormedSpace.exp H * S) := by
    simp only [hconst]; simp
  rw [← this, ← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _)]
  · apply intervalIntegral.integral_congr; intro s _
    simp only [Matrix.mul_sub, Matrix.sub_mul, trace_sub]
  · simp only [hconst]; exact intervalIntegrable_const

lemma int_Z (H C : Mat d) :
    (∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • H) * C * NormedSpace.exp ((1 - s) • H) * 1)) =
      trace (NormedSpace.exp H * C) := by
  have : ∀ s : ℝ, trace (NormedSpace.exp (s • H) * C * NormedSpace.exp ((1 - s) • H) * 1) =
      trace (NormedSpace.exp H * C) := by
    intro s
    rw [Matrix.mul_one, trace_mul_cycle, exp_smul_mul, trace_mul_comm,
      show (1 - s + s) = (1:ℝ) by ring, one_smul, trace_mul_comm]
  simp only [this]; simp

lemma herm_line (K C : Mat d) (hK : K.IsHermitian) (hC : C.IsHermitian) (t : ℝ) :
    (K + t • C).IsHermitian := by
  apply hK.add
  unfold IsHermitian
  rw [conjTranspose_smul, hC.eq, star_trivial]

lemma tr_expC_real (H C : Mat d) (hH : H.IsHermitian) (hC : C.IsHermitian) :
    trace (NormedSpace.exp H * C) = (((trace (NormedSpace.exp H * C)).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    rw [tr_exp_mul H C hH, Complex.im_sum]
    apply Finset.sum_eq_zero; intro a _
    rw [Complex.im_ofReal_mul]
    have h := (conj_herm hH.eigenvectorUnitary.1 C hC).apply a a
    have : ((star hH.eigenvectorUnitary.1 * C * hH.eigenvectorUnitary.1) a a).im = 0 := by
      have := congrArg Complex.im h
      rw [Complex.star_def, Complex.conj_im] at this
      linarith
    rw [this, mul_zero]

lemma z_pos (H : Mat d) (hH : H.IsHermitian) (hd : 0 < d) :
    0 < ∑ a, Real.exp (hH.eigenvalues a) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact Finset.sum_pos (fun a _ => Real.exp_pos _) Finset.univ_nonempty

theorem g_bound (hd : 0 < d) (K C S : Mat d) (hK : K.IsHermitian) (hC : C.IsHermitian)
    (hS : S.IsHermitian) (hSS : S * S = 1) :
    (trace (NormedSpace.exp (K + C) * S) / trace (NormedSpace.exp (K + C))).re -
      (trace (NormedSpace.exp K * S) / trace (NormedSpace.exp K)).re ≤ euclideanOpNorm C := by
  set g : ℝ → ℝ := fun t => (trace (NormedSpace.exp (K + t • C) * S) /
    trace (NormedSpace.exp (K + t • C) * 1)).re
  have hderiv : ∀ t, ∃ g', HasDerivAt g g' t ∧ g' ≤ euclideanOpNorm C := by
    intro t
    set H := K + t • C
    have hH : H.IsHermitian := herm_line K C hK hC t
    set zr := ∑ a, Real.exp (hH.eigenvalues a)
    have hzr : 0 < zr := z_pos H hH hd
    have hZv : trace (NormedSpace.exp H * 1) = (zr : ℂ) := by
      rw [Matrix.mul_one]; exact tr_exp_eq H hH
    have hN := hasDerivAt_trexp K C S t
    have hZ := hasDerivAt_trexp K C 1 t
    have hZne : trace (NormedSpace.exp (K + t • C) * 1) ≠ 0 := by
      rw [hZv]; exact_mod_cast hzr.ne'
    have hG := hN.div hZ hZne
    have hg := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt t hG
    refine ⟨_, hg, ?_⟩
    simp only [Complex.reCLM_apply]
    set c := (trace (NormedSpace.exp H * C)).re / zr
    have hc : c * zr = (trace (NormedSpace.exp H * C)).re := by
      simp only [c]; field_simp
    have hz' : (∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • H) * C *
        NormedSpace.exp ((1 - s) • H) * 1)) = ((c * zr : ℝ) : ℂ) := by
      rw [int_Z, hc]; exact tr_expC_real H C hH hC
    rw [hz', hZv]
    set n' := ∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • H) * C * NormedSpace.exp ((1 - s) • H) * S)
    set N := trace (NormedSpace.exp H * S)
    have hcen := int_center H C S c
    have hzc : (zr : ℂ) ≠ 0 := by exact_mod_cast hzr.ne'
    have e : (n' * (zr : ℂ) - N * ((c * zr : ℝ) : ℂ)) / (zr : ℂ) ^ 2 =
        (zr : ℂ)⁻¹ * (n' - (c : ℂ) * N) := by
      push_cast; field_simp
    rw [e, hcen]
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzr]
    have hb : ‖∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • H) * (C - (c : ℂ) • (1 : Mat d)) *
        NormedSpace.exp ((1 - s) • H) * S)‖ ≤ (zr * euclideanOpNorm C) * |(1:ℝ) - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [Set.uIoc_of_le zero_le_one] at hs
      exact integrand_bound H C S hH hC hS hSS s hs.1.le hs.2 c hc
    rw [sub_zero, abs_one, mul_one] at hb
    calc zr⁻¹ * ‖_‖ ≤ zr⁻¹ * (zr * euclideanOpNorm C) := by gcongr
      _ = euclideanOpNorm C := by field_simp
  have hdiff : Differentiable ℝ g := fun t => (hderiv t).choose_spec.1.differentiableAt
  have hd' : ∀ t, deriv g t ≤ euclideanOpNorm C := by
    intro t
    rw [(hderiv t).choose_spec.1.deriv]; exact (hderiv t).choose_spec.2
  have := image_sub_le_mul_sub_of_deriv_le hdiff hd' (zero_le_one' ℝ)
  simp only [g, one_smul, zero_smul, add_zero, Matrix.mul_one, sub_zero, mul_one] at this
  exact this

end Calc


lemma charpoly_conj (V D : Mat d) (hV : V ∈ unitaryGroup (Fin d) ℂ) :
    (V * D * star V).charpoly = D.charpoly := by
  rw [Matrix.mul_assoc, charpoly_mul_comm, Matrix.mul_assoc, star_mul_unit V hV, Matrix.mul_one]

lemma spec_of (Y : Mat d) (hY : Y.IsHermitian) :
    Y = hY.eigenvectorUnitary.1 * diagonal (fun a => ((hY.eigenvalues a : ℝ) : ℂ)) *
      star hY.eigenvectorUnitary.1 := by
  conv_lhs => rw [hY.spectral_theorem]
  rfl

lemma schatten_eq (Y : Mat d) (hY : Y.IsHermitian) :
    schattenOne Y = ∑ a, |hY.eigenvalues a| := by
  unfold schattenOne
  set B := Yᴴ * Y
  have hB : B.IsHermitian := isHermitian_conjTranspose_mul_self Y
  set V := hY.eigenvectorUnitary.1
  have hV : V ∈ unitaryGroup (Fin d) ℂ := hY.eigenvectorUnitary.2
  set lam := hY.eigenvalues
  have hBe : B = V * diagonal (fun a => (((lam a) ^ 2 : ℝ) : ℂ)) * star V := by
    simp only [B]
    rw [hY.eq]
    conv_lhs => rw [spec_of Y hY]
    calc _ = V * diagonal (fun a => ((lam a : ℝ) : ℂ)) * (star V * V) *
          diagonal (fun a => ((lam a : ℝ) : ℂ)) * star V := by simp only [V, lam, Matrix.mul_assoc]
      _ = _ := by
        rw [star_mul_unit V hV, Matrix.mul_one, Matrix.mul_assoc V, diagonal_mul_diagonal]
        congr 3; funext a; push_cast; ring
  have hroots := hB.roots_charpoly_eq_eigenvalues
  have hcp : B.charpoly.roots = Multiset.map (fun a => (((lam a) ^ 2 : ℝ) : ℂ)) Finset.univ.val := by
    have key : ∀ f : Fin d → ℝ, (∏ i, (Polynomial.X - Polynomial.C ((f i : ℝ) : ℂ))).roots =
        Multiset.map (fun a => ((f a : ℝ) : ℂ)) Finset.univ.val := by
      intro f
      rw [Polynomial.roots_prod]
      · simp
      · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
    rw [hBe, charpoly_conj V _ hV, charpoly_diagonal]
    exact key (fun a => lam a ^ 2)
  rw [hcp] at hroots
  have hsum := congrArg (fun m : Multiset ℂ => (m.map (fun z => Real.sqrt z.re)).sum) hroots
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at hsum
  have e1 : ∀ f : Fin d → ℝ, (Multiset.map f Finset.univ.val).sum = ∑ a, f a := fun f => rfl
  rw [e1, e1] at hsum
  calc _ = ∑ a, Real.sqrt (hB.eigenvalues a) := rfl
    _ = ∑ a, Real.sqrt (lam a ^ 2) := hsum.symm
    _ = _ := Finset.sum_congr rfl (fun a _ => Real.sqrt_sq_eq_abs _)

def sgn (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

lemma sgn_sq (x : ℝ) : sgn x * sgn x = 1 := by unfold sgn; split_ifs <;> norm_num

lemma mul_sgn (x : ℝ) : x * sgn x = |x| := by
  unfold sgn; split_ifs with h
  · rw [abs_of_nonneg h, mul_one]
  · rw [abs_of_neg (not_le.1 h)]; ring

theorem exists_sign (Y : Mat d) (hY : Y.IsHermitian) :
    ∃ S : Mat d, S.IsHermitian ∧ S * S = 1 ∧ schattenOne Y = (trace (Y * S)).re := by
  set V := hY.eigenvectorUnitary.1
  have hV : V ∈ unitaryGroup (Fin d) ℂ := hY.eigenvectorUnitary.2
  set lam := hY.eigenvalues
  set Sg := diagonal (fun a => ((sgn (lam a) : ℝ) : ℂ))
  refine ⟨V * Sg * star V, ?_, ?_, ?_⟩
  · unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, ← Matrix.star_eq_conjTranspose (star V), star_star,
      diagonal_conjTranspose, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    congr 2; congr 1; funext a; simp
  · calc V * Sg * star V * (V * Sg * star V) = V * Sg * (star V * V) * Sg * star V := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [star_mul_unit V hV, Matrix.mul_one, Matrix.mul_assoc V, diagonal_mul_diagonal]
        have : (fun a => ((sgn (lam a) : ℝ) : ℂ) * ((sgn (lam a) : ℝ) : ℂ)) = fun _ => 1 := by
          funext a; rw [← Complex.ofReal_mul, sgn_sq]; simp
        rw [this, diagonal_one, Matrix.mul_one, unit_mul_star V hV]
  · rw [schatten_eq Y hY]
    conv_rhs => rw [spec_of Y hY]
    have : V * diagonal (fun a => ((lam a : ℝ) : ℂ)) * star V * (V * Sg * star V) =
        V * (diagonal (fun a => ((lam a : ℝ) : ℂ)) * Sg * star V) := by
      calc _ = V * (diagonal (fun a => ((lam a : ℝ) : ℂ)) * (star V * V) * Sg * star V) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [star_mul_unit V hV, Matrix.mul_one]
    rw [this, trace_mul_comm, Matrix.mul_assoc _ (star V), star_mul_unit V hV, Matrix.mul_one,
      diagonal_mul_diagonal, trace_diagonal, Complex.re_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [← Complex.ofReal_mul, Complex.ofReal_re, mul_sgn]


lemma exp_isHerm (H : Mat d) (hH : H.IsHermitian) : (NormedSpace.exp H).IsHermitian := by
  have := exp_herm H hH 1
  rw [one_smul] at this
  rw [this]
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, ← Matrix.star_eq_conjTranspose (star _), star_star,
    diagonal_conjTranspose, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  congr 2; congr 1; funext a
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]

lemma gibbs_herm (H : Mat d) (hH : H.IsHermitian) :
    ((trace (NormedSpace.exp H))⁻¹ • NormedSpace.exp H).IsHermitian := by
  rw [tr_exp_eq H hH]
  unfold IsHermitian
  rw [conjTranspose_smul, (exp_isHerm H hH).eq]
  congr 1
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]

end TFIMPhaseDiagram.Classical.P32

open TFIMPhaseDiagram.Classical.P32 in
theorem solution (d : ℕ) (hd : 0 < d) (K C : Matrix (Fin d) (Fin d) ℂ)
    (hK : K.IsHermitian) (hC : C.IsHermitian) :
  TFIMPhaseDiagram.Classical.schattenOne
    ((Matrix.trace (TFIMPhaseDiagram.Classical.matrixExp (K+C)))⁻¹ •
        TFIMPhaseDiagram.Classical.matrixExp (K+C) -
      (Matrix.trace (TFIMPhaseDiagram.Classical.matrixExp K))⁻¹ •
        TFIMPhaseDiagram.Classical.matrixExp K) ≤ TFIMPhaseDiagram.Classical.euclideanOpNorm C := by
  unfold TFIMPhaseDiagram.Classical.matrixExp
  have hKC : (K + C).IsHermitian := hK.add hC
  have hY := (gibbs_herm (K + C) hKC).sub (gibbs_herm K hK)
  obtain ⟨S, hS, hSS, hY1⟩ := exists_sign _ hY
  rw [hY1]
  have hb := g_bound hd K C S hK hC hS hSS
  refine le_of_eq_of_le ?_ hb
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul,
    Matrix.trace_smul, smul_eq_mul, smul_eq_mul, inv_mul_eq_div, inv_mul_eq_div]
