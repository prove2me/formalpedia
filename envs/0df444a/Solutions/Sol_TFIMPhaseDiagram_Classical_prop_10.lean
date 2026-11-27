-- Prove2me | solution 1 for TFIMPhaseDiagram.Classical.prop_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:41:31.677496+00:00
-- url     : https://prove2.me/submissions/c51ded54-6f23-4be6-99c2-e13280bb108c

import Definitions.Def_TFIMPhaseDiagram_Classical_traceSetup

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical.P32G

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]
set_option linter.unusedSectionVars false

abbrev Mat (ι : Type) [Fintype ι] [DecidableEq ι] := Matrix ι ι ℂ

lemma unitary_inv (V : Mat ι) (hV : V ∈ unitaryGroup ι ℂ) : V⁻¹ = star V := by
  rw [mem_unitaryGroup_iff] at hV
  exact inv_eq_right_inv hV

lemma unitary_isUnit (V : Mat ι) (hV : V ∈ unitaryGroup ι ℂ) : IsUnit V := by
  rw [mem_unitaryGroup_iff] at hV
  exact ⟨⟨V, star V, hV, mul_eq_one_comm.mp hV⟩, rfl⟩

lemma exp_herm (H : Mat ι) (hH : H.IsHermitian) (s : ℝ) :
    NormedSpace.exp (s • H) =
      hH.eigenvectorUnitary.1 *
        diagonal (fun a => ((Real.exp (s * hH.eigenvalues a) : ℝ) : ℂ)) *
        star hH.eigenvectorUnitary.1 := by
  set V : Mat ι := hH.eigenvectorUnitary.1
  have hVu : V ∈ unitaryGroup ι ℂ := hH.eigenvectorUnitary.2
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


def Qf (lam : ι → ℝ) (x : ι → ι → ℂ) : ℝ :=
  ∑ a, ∑ b, Real.exp (lam a) * ‖x a b‖ ^ 2

lemma Qf_nonneg (lam : ι → ℝ) (x : ι → ι → ℂ) : 0 ≤ Qf lam x := by
  unfold Qf; positivity

lemma weighted_le (lam : ι → ℝ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (x : ι → ι → ℂ) (hx : ∀ a b, ‖x a b‖ = ‖x b a‖) :
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

lemma cs_bound (lam : ι → ℝ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (x y : ι → ι → ℂ) (hx : ∀ a b, ‖x a b‖ = ‖x b a‖) (hy : ∀ a b, ‖y a b‖ = ‖y b a‖) :
    ‖∑ a, ∑ b, (Real.exp (s * lam a) : ℂ) * x a b * (Real.exp ((1 - s) * lam b) : ℂ) * y b a‖ ≤
      Real.sqrt (Qf lam x) * Real.sqrt (Qf lam y) := by
  set w : ι → ι → ℝ := fun a b => Real.exp (s * lam a) * Real.exp ((1 - s) * lam b)
  have hw0 : ∀ a b, 0 ≤ w a b := fun a b => by positivity
  have h1 : ‖∑ a, ∑ b, (Real.exp (s * lam a) : ℂ) * x a b * (Real.exp ((1 - s) * lam b) : ℂ) * y b a‖
      ≤ ∑ p : ι × ι, (Real.sqrt (w p.1 p.2) * ‖x p.1 p.2‖) * (Real.sqrt (w p.1 p.2) * ‖y p.2 p.1‖) := by
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
  have e1 : ∀ (z : ι → ι → ℂ) (σ : ι × ι → ι × ι),
      (∑ p : ι × ι, (Real.sqrt (w p.1 p.2) * ‖z (σ p).1 (σ p).2‖) ^ 2) =
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


lemma opnorm_bound (C : Mat ι) (v : ι → ℂ) (hv : ∑ k, ‖v k‖ ^ 2 = 1) :
    ∑ k, ‖(C *ᵥ v) k‖ ^ 2 ≤ (euclideanOpNorm C) ^ 2 := by
  set x : EuclideanSpace ℂ ι := WithLp.toLp 2 v
  have hx : ‖x‖ = 1 := by
    rw [EuclideanSpace.norm_eq]; simp [x, hv]
  set r := ‖WithLp.toLp 2 (C.mulVec (fun i => x i))‖
  have hr : r ^ 2 = ∑ k, ‖(C *ᵥ v) k‖ ^ 2 := by
    simp only [r, EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (by positivity)]
  have hmem : r ∈ {r | ∃ x : EuclideanSpace ℂ ι, ‖x‖ = 1 ∧
      r = ‖WithLp.toLp 2 (C.mulVec (fun i => x i))‖} := ⟨x, hx, rfl⟩
  have hbdd : BddAbove {r | ∃ x : EuclideanSpace ℂ ι, ‖x‖ = 1 ∧
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

lemma tr_diag_sandwich (e f : ι → ℂ) (M N : Mat ι) :
    trace (diagonal e * M * diagonal f * N) = ∑ a, ∑ b, e a * M a b * f b * N b a := by
  simp only [trace, diag]
  apply Finset.sum_congr rfl; intro a _
  rw [mul_apply]
  apply Finset.sum_congr rfl; intro b _
  rw [mul_diagonal, diagonal_mul]


lemma tr_coords (H X S : Mat ι) (hH : H.IsHermitian) (s : ℝ) :
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


lemma rownorm (M : Mat ι) (a : ι) : ∑ b, ‖M a b‖ ^ 2 = ((M * Mᴴ) a a).re := by
  rw [mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl; intro b _
  rw [conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

lemma colnorm (M : Mat ι) (a : ι) : ∑ b, ‖M b a‖ ^ 2 = ((Mᴴ * M) a a).re := by
  rw [mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl; intro b _
  rw [conjTranspose_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

lemma conj_herm (V X : Mat ι) (hX : X.IsHermitian) : (star V * X * V).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, hX.eq]
  simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

lemma herm_norm_symm (M : Mat ι) (hM : M.IsHermitian) (a b : ι) : ‖M a b‖ = ‖M b a‖ := by
  rw [← hM.apply a b, norm_star]

lemma unit_mul_star (V : Mat ι) (hV : V ∈ unitaryGroup ι ℂ) : V * star V = 1 :=
  (mem_unitaryGroup_iff).1 hV

lemma star_mul_unit (V : Mat ι) (hV : V ∈ unitaryGroup ι ℂ) : star V * V = 1 :=
  (mem_unitaryGroup_iff').1 hV

lemma Qf_S (lam : ι → ℝ) (V S : Mat ι) (hV : V ∈ unitaryGroup ι ℂ)
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


lemma row_center (M : Mat ι) (c : ℝ) (a : ι) :
    ∑ b, ‖(M - (c : ℂ) • (1 : Mat ι)) a b‖ ^ 2 = ∑ b, ‖M a b‖ ^ 2 - 2 * c * (M a a).re + c ^ 2 := by
  have h : ∀ b, ‖(M - (c : ℂ) • (1 : Mat ι)) a b‖ ^ 2 =
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

lemma Qf_center (lam : ι → ℝ) (M : Mat ι) (c : ℝ) :
    Qf lam (fun a b => (M - (c : ℂ) • (1 : Mat ι)) a b) =
      Qf lam (fun a b => M a b) - 2 * c * ∑ a, Real.exp (lam a) * (M a a).re +
        c ^ 2 * ∑ a, Real.exp (lam a) := by
  calc Qf lam (fun a b => (M - (c : ℂ) • (1 : Mat ι)) a b)
      = ∑ a, Real.exp (lam a) * (∑ b, ‖M a b‖ ^ 2 - 2 * c * (M a a).re + c ^ 2) := by
        unfold Qf; apply Finset.sum_congr rfl; intro a _; rw [← Finset.mul_sum, row_center]
    _ = ∑ a, (Real.exp (lam a) * ∑ b, ‖M a b‖ ^ 2) - 2 * c * ∑ a, Real.exp (lam a) * (M a a).re +
        c ^ 2 * ∑ a, Real.exp (lam a) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro a _; ring
    _ = _ := by
        unfold Qf; congr 2
        apply Finset.sum_congr rfl; intro a _; rw [Finset.mul_sum]

lemma Qf_C_le (lam : ι → ℝ) (V C : Mat ι) (hV : V ∈ unitaryGroup ι ℂ)
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


lemma tr_exp_mul (H M : Mat ι) (hH : H.IsHermitian) :
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

lemma tr_exp_eq (H : Mat ι) (hH : H.IsHermitian) :
    trace (NormedSpace.exp H) = ((∑ a, Real.exp (hH.eigenvalues a) : ℝ) : ℂ) := by
  have := tr_exp_mul H 1 hH
  rw [Matrix.mul_one, Matrix.mul_one, star_mul_unit _ hH.eigenvectorUnitary.2] at this
  rw [this]; push_cast; simp

lemma opNorm_nonneg (C : Mat ι) : 0 ≤ euclideanOpNorm C := by
  unfold euclideanOpNorm
  apply Real.sSup_nonneg
  rintro r ⟨x, -, rfl⟩; exact norm_nonneg _

lemma integrand_bound (H C S : Mat ι) (hH : H.IsHermitian) (hC : C.IsHermitian)
    (hS : S.IsHermitian) (hSS : S * S = 1) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (c : ℝ)
    (hc : c * (∑ a, Real.exp (hH.eigenvalues a)) = (trace (NormedSpace.exp H * C)).re) :
    ‖trace (NormedSpace.exp (s • H) * (C - (c : ℂ) • (1 : Mat ι)) *
        NormedSpace.exp ((1 - s) • H) * S)‖ ≤
      (∑ a, Real.exp (hH.eigenvalues a)) * euclideanOpNorm C := by
  set lam := hH.eigenvalues
  set V := hH.eigenvectorUnitary.1
  have hV : V ∈ unitaryGroup ι ℂ := hH.eigenvectorUnitary.2
  set z := ∑ a, Real.exp (lam a)
  have hz : 0 ≤ z := by positivity
  rw [tr_coords H _ S hH s]
  have hX : (star V * (C - (c : ℂ) • (1 : Mat ι)) * V) = star V * C * V - (c : ℂ) • (1 : Mat ι) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      star_mul_unit V hV]
  have hXh : (star V * (C - (c : ℂ) • (1 : Mat ι)) * V).IsHermitian := by
    apply conj_herm
    unfold IsHermitian
    rw [conjTranspose_sub, hC.eq, conjTranspose_smul, conjTranspose_one]
    simp
  refine (cs_bound lam s hs0 hs1 _ _ (herm_norm_symm _ hXh)
    (herm_norm_symm _ (conj_herm V S hS))).trans ?_
  have hQS := Qf_S lam V S hV hS hSS
  have hQX : Qf lam (fun a b => (star V * (C - (c : ℂ) • (1 : Mat ι)) * V) a b) ≤
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

def trCLM (ι : Type) [Fintype ι] [DecidableEq ι] : Mat ι →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap ι ℝ ℂ)

lemma trCLM_apply (M : Mat ι) : trCLM ι M = trace M := rfl

lemma hasDerivAt_tr {f : ℝ → Mat ι} {f' : Mat ι} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => trace (f t)) (trace f') x := by
  exact (trCLM ι).hasFDerivAt.comp_hasDerivAt x hf

lemma duhamel_deriv (A B S : Mat ι) (s : ℝ) :
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

lemma cont_integrand (A C S : Mat ι) :
    Continuous (fun p : ℝ × ℝ => trace (NormedSpace.exp (p.2 • (A + p.1 • C)) * C *
      NormedSpace.exp ((1 - p.2) • A) * S)) := by
  have he : Continuous (NormedSpace.exp : Mat ι → Mat ι) := NormedSpace.exp_continuous
  have h1 : Continuous (fun p : ℝ × ℝ => NormedSpace.exp (p.2 • (A + p.1 • C))) :=
    he.comp (continuous_snd.smul (continuous_const.add (continuous_fst.smul continuous_const)))
  have h2 : Continuous (fun p : ℝ × ℝ => NormedSpace.exp ((1 - p.2) • A)) :=
    he.comp ((continuous_const.sub continuous_snd).smul continuous_const)
  exact (trCLM ι).continuous.comp (((h1.mul continuous_const).mul h2).mul continuous_const)

lemma duhamel (A B S : Mat ι) :
    trace (NormedSpace.exp (A + B) * S) - trace (NormedSpace.exp A * S) =
      ∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • (A + B)) * B * NormedSpace.exp ((1 - s) • A) * S) := by
  have hc : Continuous (fun s : ℝ => trace (NormedSpace.exp (s • (A + B)) * B *
      NormedSpace.exp ((1 - s) • A) * S)) := by
    have := (cont_integrand A B S).comp (continuous_const.prodMk continuous_id : Continuous (fun s : ℝ => ((1:ℝ), s)))
    simpa [Function.comp_def, one_smul] using this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => duhamel_deriv A B S s)
    (hc.intervalIntegrable _ _)]
  simp

lemma hasDerivAt_trexp (K C S : Mat ι) (t : ℝ) :
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

lemma exp_smul_mul (H : Mat ι) (a b : ℝ) :
    NormedSpace.exp (a • H) * NormedSpace.exp (b • H) = NormedSpace.exp ((a + b) • H) := by
  rw [add_smul, Matrix.exp_add_of_commute _ _ ((Commute.refl H).smul_left a |>.smul_right b)]

lemma int_center (H C S : Mat ι) (c : ℝ) :
    (∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • H) * C * NormedSpace.exp ((1 - s) • H) * S)) -
      (c : ℂ) * trace (NormedSpace.exp H * S) =
    ∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • H) * (C - (c : ℂ) • (1 : Mat ι)) *
      NormedSpace.exp ((1 - s) • H) * S) := by
  have hc1 : Continuous (fun s : ℝ => trace (NormedSpace.exp (s • H) * C *
      NormedSpace.exp ((1 - s) • H) * S)) := by
    have := (cont_integrand H C S).comp (continuous_const.prodMk continuous_id : Continuous (fun s : ℝ => ((0:ℝ), s)))
    simpa [Function.comp_def] using this
  have hconst : ∀ s : ℝ, trace (NormedSpace.exp (s • H) * ((c : ℂ) • (1 : Mat ι)) *
      NormedSpace.exp ((1 - s) • H) * S) = (c : ℂ) * trace (NormedSpace.exp H * S) := by
    intro s
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, exp_smul_mul, Matrix.smul_mul, trace_smul,
      smul_eq_mul]
    congr 3; simp
  have : (∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • H) * ((c : ℂ) • (1 : Mat ι)) *
      NormedSpace.exp ((1 - s) • H) * S)) = (c : ℂ) * trace (NormedSpace.exp H * S) := by
    simp only [hconst]; simp
  rw [← this, ← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _)]
  · apply intervalIntegral.integral_congr; intro s _
    simp only [Matrix.mul_sub, Matrix.sub_mul, trace_sub]
  · simp only [hconst]; exact intervalIntegrable_const

lemma int_Z (H C : Mat ι) :
    (∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • H) * C * NormedSpace.exp ((1 - s) • H) * 1)) =
      trace (NormedSpace.exp H * C) := by
  have : ∀ s : ℝ, trace (NormedSpace.exp (s • H) * C * NormedSpace.exp ((1 - s) • H) * 1) =
      trace (NormedSpace.exp H * C) := by
    intro s
    rw [Matrix.mul_one, trace_mul_cycle, exp_smul_mul, trace_mul_comm,
      show (1 - s + s) = (1:ℝ) by ring, one_smul, trace_mul_comm]
  simp only [this]; simp

lemma herm_line (K C : Mat ι) (hK : K.IsHermitian) (hC : C.IsHermitian) (t : ℝ) :
    (K + t • C).IsHermitian := by
  apply hK.add
  unfold IsHermitian
  rw [conjTranspose_smul, hC.eq, star_trivial]

lemma tr_expC_real (H C : Mat ι) (hH : H.IsHermitian) (hC : C.IsHermitian) :
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

lemma z_pos (H : Mat ι) (hH : H.IsHermitian) [Nonempty ι] :
    0 < ∑ a, Real.exp (hH.eigenvalues a) := by
  exact Finset.sum_pos (fun a _ => Real.exp_pos _) Finset.univ_nonempty

theorem g_bound [Nonempty ι] (K C S : Mat ι) (hK : K.IsHermitian) (hC : C.IsHermitian)
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
    have hzr : 0 < zr := z_pos H hH
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
    have hb : ‖∫ s in (0:ℝ)..1, trace (NormedSpace.exp (s • H) * (C - (c : ℂ) • (1 : Mat ι)) *
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


lemma charpoly_conj (V D : Mat ι) (hV : V ∈ unitaryGroup ι ℂ) :
    (V * D * star V).charpoly = D.charpoly := by
  rw [Matrix.mul_assoc, charpoly_mul_comm, Matrix.mul_assoc, star_mul_unit V hV, Matrix.mul_one]

lemma spec_of (Y : Mat ι) (hY : Y.IsHermitian) :
    Y = hY.eigenvectorUnitary.1 * diagonal (fun a => ((hY.eigenvalues a : ℝ) : ℂ)) *
      star hY.eigenvectorUnitary.1 := by
  conv_lhs => rw [hY.spectral_theorem]
  rfl

lemma schatten_eq (Y : Mat ι) (hY : Y.IsHermitian) :
    schattenOne Y = ∑ a, |hY.eigenvalues a| := by
  unfold schattenOne
  set B := Yᴴ * Y
  have hB : B.IsHermitian := isHermitian_conjTranspose_mul_self Y
  set V := hY.eigenvectorUnitary.1
  have hV : V ∈ unitaryGroup ι ℂ := hY.eigenvectorUnitary.2
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
    have key : ∀ f : ι → ℝ, (∏ i, (Polynomial.X - Polynomial.C ((f i : ℝ) : ℂ))).roots =
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
  have e1 : ∀ f : ι → ℝ, (Multiset.map f Finset.univ.val).sum = ∑ a, f a := fun f => rfl
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

theorem exists_sign (Y : Mat ι) (hY : Y.IsHermitian) :
    ∃ S : Mat ι, S.IsHermitian ∧ S * S = 1 ∧ schattenOne Y = (trace (Y * S)).re := by
  set V := hY.eigenvectorUnitary.1
  have hV : V ∈ unitaryGroup ι ℂ := hY.eigenvectorUnitary.2
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


lemma exp_isHerm (H : Mat ι) (hH : H.IsHermitian) : (NormedSpace.exp H).IsHermitian := by
  have := exp_herm H hH 1
  rw [one_smul] at this
  rw [this]
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, ← Matrix.star_eq_conjTranspose (star _), star_star,
    diagonal_conjTranspose, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  congr 2; congr 1; funext a
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]

lemma gibbs_herm (H : Mat ι) (hH : H.IsHermitian) :
    ((trace (NormedSpace.exp H))⁻¹ • NormedSpace.exp H).IsHermitian := by
  rw [tr_exp_eq H hH]
  unfold IsHermitian
  rw [conjTranspose_smul, (exp_isHerm H hH).eq]
  congr 1
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]


theorem gibbs_diff [Nonempty ι] (K C O : Mat ι) (hK : K.IsHermitian) (hC : C.IsHermitian)
    (hO : O.IsHermitian) (hOO : O * O = 1) :
    ‖trace (NormedSpace.exp (K + C) * O) / trace (NormedSpace.exp (K + C)) -
      trace (NormedSpace.exp K * O) / trace (NormedSpace.exp K)‖ ≤ euclideanOpNorm C := by
  have hKC : (K + C).IsHermitian := hK.add hC
  have real_q : ∀ H : Mat ι, H.IsHermitian →
      trace (NormedSpace.exp H * O) / trace (NormedSpace.exp H) =
        (((trace (NormedSpace.exp H * O) / trace (NormedSpace.exp H)).re : ℝ) : ℂ) := by
    intro H hH
    rw [tr_expC_real H O hH hO, tr_exp_eq H hH, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [real_q _ hKC, real_q _ hK, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have h1 := g_bound K C O hK hC hO hOO
  have hnO : (-O).IsHermitian := hO.neg
  have h2 := g_bound K C (-O) hK hC hnO (by rw [neg_mul_neg, hOO])
  simp only [Matrix.mul_neg, trace_neg, neg_div, Complex.neg_re] at h2
  constructor <;> linarith

end TFIMPhaseDiagram.Classical.P32G

open scoped Nat


namespace TFIMPhaseDiagram.Classical.P10T

set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

lemma norm_term_le (x : 𝔸) (n : ℕ) : ‖((n ! : ℂ)⁻¹) • x ^ n‖ ≤ ‖x‖ ^ n / n ! := by
  rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity)

lemma real_exp_hasSum (r : ℝ) : HasSum (fun n : ℕ => r ^ n / n !) (Real.exp r) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp r

lemma norm_exp_le (x : 𝔸) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  refine (norm_tsum_le_tsum_norm (NormedSpace.norm_expSeries_summable' x)).trans ?_
  exact ((NormedSpace.norm_expSeries_summable' x).tsum_le_tsum (norm_term_le x)
    (real_exp_hasSum _).summable).trans (real_exp_hasSum _).tsum_eq.le

/-- Tail bound: the exponential series from index `k` on has norm at most `‖x‖^k e^{‖x‖}`. -/
lemma norm_tail_le (x : 𝔸) (k : ℕ) :
    ‖NormedSpace.exp x - ∑ i ∈ Finset.range k, ((i ! : ℂ)⁻¹) • x ^ i‖ ≤ ‖x‖ ^ k * Real.exp ‖x‖ := by
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℂ) x
  have hrep : NormedSpace.exp x - ∑ i ∈ Finset.range k, ((i ! : ℂ)⁻¹) • x ^ i =
      ∑' n : ℕ, (((n + k) ! : ℂ)⁻¹) • x ^ (n + k) := by
    rw [NormedSpace.exp_eq_tsum ℂ]
    simp only
    rw [← hs.sum_add_tsum_nat_add k]
    abel
  rw [hrep]
  have hsn : Summable (fun n : ℕ => ‖(((n + k) ! : ℂ)⁻¹) • x ^ (n + k)‖) :=
    (summable_nat_add_iff k).2 (NormedSpace.norm_expSeries_summable' x)
  refine (norm_tsum_le_tsum_norm hsn).trans ?_
  have hb : ∀ n : ℕ, ‖(((n + k) ! : ℂ)⁻¹) • x ^ (n + k)‖ ≤ ‖x‖ ^ k * (‖x‖ ^ n / n !) := by
    intro n
    refine (norm_term_le x (n+k)).trans ?_
    rw [pow_add, mul_comm (‖x‖ ^ n), mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast Nat.factorial_le (by omega)
  calc ∑' n, ‖(((n + k) ! : ℂ)⁻¹) • x ^ (n + k)‖ ≤ ∑' n : ℕ, ‖x‖ ^ k * (‖x‖ ^ n / n !) :=
        hsn.tsum_le_tsum hb ((real_exp_hasSum _).summable.mul_left _)
    _ = ‖x‖ ^ k * Real.exp ‖x‖ := by rw [tsum_mul_left, (real_exp_hasSum _).tsum_eq]

def T2 (z : 𝔸) : 𝔸 := 1 + z + (2:ℂ)⁻¹ • (z * z)

lemma norm_R1 (x : 𝔸) : ‖NormedSpace.exp x - 1‖ ≤ ‖x‖ * Real.exp ‖x‖ := by
  have := norm_tail_le x 1
  simpa using this

lemma norm_R3 (x : 𝔸) : ‖NormedSpace.exp x - T2 x‖ ≤ ‖x‖ ^ 3 * Real.exp ‖x‖ := by
  have := norm_tail_le x 3
  have e : ∑ i ∈ Finset.range 3, ((i ! : ℂ)⁻¹) • x ^ i = T2 x := by
    simp [Finset.sum_range_succ, T2, pow_two]
  rwa [e] at this

lemma norm_T2 (x : 𝔸) : ‖T2 x‖ ≤ Real.exp ‖x‖ := by
  have h1 : ‖T2 x‖ ≤ 1 + ‖x‖ + ‖x‖ ^ 2 / 2 := by
    unfold T2
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (by rw [norm_one])) ?_
    rw [norm_smul, norm_inv, Complex.norm_ofNat]
    have := norm_mul_le x x
    nlinarith [norm_nonneg (x * x)]
  refine h1.trans ?_
  have := Real.quadratic_le_exp_of_nonneg (norm_nonneg x)
  linarith

lemma sym_identity (x y : 𝔸) :
    NormedSpace.exp x * NormedSpace.exp y * NormedSpace.exp x - NormedSpace.exp (x + y + x) =
      (NormedSpace.exp x - T2 x) * NormedSpace.exp y * NormedSpace.exp x +
      T2 x * (NormedSpace.exp y - T2 y) * NormedSpace.exp x +
      T2 x * T2 y * (NormedSpace.exp x - T2 x) +
      ((2:ℂ)⁻¹ • (x * (y * y)) + (2:ℂ)⁻¹ • (x * x * y) + (4:ℂ)⁻¹ • (x * x * (y * y)) +
      (2:ℂ)⁻¹ • (y * (x * x)) + (2:ℂ)⁻¹ • (y * y * x) + (4:ℂ)⁻¹ • (y * y * (x * x)) +
      x * x * x + (4:ℂ)⁻¹ • (x * x * (x * x)) +
        (x + (2:ℂ)⁻¹ • (x * x)) * (y + (2:ℂ)⁻¹ • (y * y)) * (x + (2:ℂ)⁻¹ • (x * x))) -
      (NormedSpace.exp (x + y + x) - T2 (x + y + x)) := by
  have hD : T2 x * T2 y * T2 x - T2 (x + y + x) =
      (2:ℂ)⁻¹ • (x * (y * y)) + (2:ℂ)⁻¹ • (x * x * y) + (4:ℂ)⁻¹ • (x * x * (y * y)) +
      (2:ℂ)⁻¹ • (y * (x * x)) + (2:ℂ)⁻¹ • (y * y * x) + (4:ℂ)⁻¹ • (y * y * (x * x)) +
      x * x * x + (4:ℂ)⁻¹ • (x * x * (x * x)) +
        (x + (2:ℂ)⁻¹ • (x * x)) * (y + (2:ℂ)⁻¹ • (y * y)) * (x + (2:ℂ)⁻¹ • (x * x)) := by
    simp only [T2, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc, smul_add,
      mul_one, one_mul, smul_smul, sub_eq_add_neg, neg_add]
    module
  rw [← hD]
  noncomm_ring


lemma norm_half (z : 𝔸) (c : ℝ) (hc : ‖z‖ ≤ c) : ‖(2:ℂ)⁻¹ • z‖ ≤ c / 2 := by
  rw [norm_smul, norm_inv, Complex.norm_ofNat]; linarith

lemma norm_quarter (z : 𝔸) (c : ℝ) (hc : ‖z‖ ≤ c) : ‖(4:ℂ)⁻¹ • z‖ ≤ c / 4 := by
  rw [norm_smul, norm_inv, Complex.norm_ofNat]; linarith

lemma nm2 (x y : 𝔸) : ‖x * y‖ ≤ ‖x‖ * ‖y‖ := norm_mul_le x y

lemma nm3 (x y z : 𝔸) : ‖x * y * z‖ ≤ ‖x‖ * ‖y‖ * ‖z‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

lemma norm_D (x y : 𝔸) :
    ‖(2:ℂ)⁻¹ • (x * (y * y)) + (2:ℂ)⁻¹ • (x * x * y) + (4:ℂ)⁻¹ • (x * x * (y * y)) +
      (2:ℂ)⁻¹ • (y * (x * x)) + (2:ℂ)⁻¹ • (y * y * x) + (4:ℂ)⁻¹ • (y * y * (x * x)) +
      x * x * x + (4:ℂ)⁻¹ • (x * x * (x * x)) +
        (x + (2:ℂ)⁻¹ • (x * x)) * (y + (2:ℂ)⁻¹ • (y * y)) * (x + (2:ℂ)⁻¹ • (x * x))‖ ≤
    ‖x‖ * (‖y‖ * ‖y‖) / 2 + ‖x‖ * ‖x‖ * ‖y‖ / 2 + ‖x‖ * ‖x‖ * (‖y‖ * ‖y‖) / 4 +
      ‖y‖ * (‖x‖ * ‖x‖) / 2 + ‖y‖ * ‖y‖ * ‖x‖ / 2 + ‖y‖ * ‖y‖ * (‖x‖ * ‖x‖) / 4 +
      ‖x‖ * ‖x‖ * ‖x‖ + ‖x‖ * ‖x‖ * (‖x‖ * ‖x‖) / 4 +
      (‖x‖ + ‖x‖ * ‖x‖ / 2) * (‖y‖ + ‖y‖ * ‖y‖ / 2) * (‖x‖ + ‖x‖ * ‖x‖ / 2) := by
  have hx0 := norm_nonneg x
  have hy0 := norm_nonneg y
  have m2 : ∀ a b : 𝔸, ‖a * b‖ ≤ ‖a‖ * ‖b‖ := nm2
  have p2 : ∀ a b : 𝔸, ∀ c d : ℝ, ‖a‖ ≤ c → ‖b‖ ≤ d → ‖a * b‖ ≤ c * d := fun a b c d ha hb =>
    (m2 a b).trans (mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha))
  have hxx : ‖x * x‖ ≤ ‖x‖ * ‖x‖ := m2 x x
  have hyy : ‖y * y‖ ≤ ‖y‖ * ‖y‖ := m2 y y
  have hu : ‖x + (2:ℂ)⁻¹ • (x * x)‖ ≤ ‖x‖ + ‖x‖ * ‖x‖ / 2 :=
    (norm_add_le _ _).trans (add_le_add le_rfl (norm_half _ _ hxx))
  have hv : ‖y + (2:ℂ)⁻¹ • (y * y)‖ ≤ ‖y‖ + ‖y‖ * ‖y‖ / 2 :=
    (norm_add_le _ _).trans (add_le_add le_rfl (norm_half _ _ hyy))
  have h1 := norm_half _ _ (p2 x (y * y) _ _ le_rfl hyy)
  have h2 := norm_half _ _ (p2 (x * x) y _ _ hxx le_rfl)
  have h3 := norm_quarter _ _ (p2 (x * x) (y * y) _ _ hxx hyy)
  have h4 := norm_half _ _ (p2 y (x * x) _ _ le_rfl hxx)
  have h5 := norm_half _ _ (p2 (y * y) x _ _ hyy le_rfl)
  have h6 := norm_quarter _ _ (p2 (y * y) (x * x) _ _ hyy hxx)
  have h7 : ‖x * x * x‖ ≤ ‖x‖ * ‖x‖ * ‖x‖ := p2 (x * x) x _ _ hxx le_rfl
  have h8 := norm_quarter _ _ (p2 (x * x) (x * x) _ _ hxx hxx)
  have h9 := p2 _ _ _ _ (p2 _ _ _ _ hu hv) hu
  refine (norm_add_le _ _).trans (add_le_add ?_ h9)
  refine (norm_add_le _ _).trans (add_le_add ?_ h8)
  refine (norm_add_le _ _).trans (add_le_add ?_ h7)
  refine (norm_add_le _ _).trans (add_le_add ?_ h6)
  refine (norm_add_le _ _).trans (add_le_add ?_ h5)
  refine (norm_add_le _ _).trans (add_le_add ?_ h4)
  refine (norm_add_le _ _).trans (add_le_add ?_ h3)
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

theorem sym3 (x y : 𝔸) (r : ℝ) (hr : 2 * ‖x‖ + ‖y‖ ≤ r) (hr1 : r ≤ 1 / 10) :
    ‖NormedSpace.exp x * NormedSpace.exp y * NormedSpace.exp x - NormedSpace.exp (x + y + x)‖ ≤
      8 * r ^ 3 := by
  set α := ‖x‖ with hα
  set β := ‖y‖ with hβ
  have hα0 : 0 ≤ α := norm_nonneg _
  have hβ0 : 0 ≤ β := norm_nonneg _
  have hr0 : 0 ≤ r := by linarith
  have hE : Real.exp r ≤ 6 / 5 := by
    have := Real.exp_bound_div_one_sub_of_interval hr0 (by linarith)
    refine this.trans ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hEa : Real.exp α ≤ 6 / 5 := (Real.exp_le_exp.2 (by linarith)).trans hE
  have hEb : Real.exp β ≤ 6 / 5 := (Real.exp_le_exp.2 (by linarith)).trans hE
  have hxyx : ‖x + y + x‖ ≤ r := by
    have := norm_add_le (x + y) x
    have := norm_add_le x y
    linarith
  have hExyx : Real.exp ‖x + y + x‖ ≤ 6 / 5 := (Real.exp_le_exp.2 hxyx).trans hE
  have eA : ‖NormedSpace.exp x‖ ≤ 6 / 5 := (norm_exp_le x).trans hEa
  have eB : ‖NormedSpace.exp y‖ ≤ 6 / 5 := (norm_exp_le y).trans hEb
  have tA : ‖T2 x‖ ≤ 6 / 5 := (norm_T2 x).trans hEa
  have tB : ‖T2 y‖ ≤ 6 / 5 := (norm_T2 y).trans hEb
  have rA : ‖NormedSpace.exp x - T2 x‖ ≤ α ^ 3 * (6 / 5) :=
    (norm_R3 x).trans (mul_le_mul_of_nonneg_left hEa (by positivity))
  have rB : ‖NormedSpace.exp y - T2 y‖ ≤ β ^ 3 * (6 / 5) :=
    (norm_R3 y).trans (mul_le_mul_of_nonneg_left hEb (by positivity))
  have rC : ‖NormedSpace.exp (x + y + x) - T2 (x + y + x)‖ ≤ r ^ 3 * (6 / 5) :=
    (norm_R3 _).trans (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxyx 3) hExyx (by positivity)
      (by positivity))
  have p3 : ∀ a b c : 𝔸, ∀ ca cb cc : ℝ, ‖a‖ ≤ ca → ‖b‖ ≤ cb → ‖c‖ ≤ cc →
      ‖a * b * c‖ ≤ ca * cb * cc := fun a b c ca cb cc ha hb hc =>
    (nm3 a b c).trans (mul_le_mul (mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)) hc
      (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans ha) ((norm_nonneg _).trans hb)))
  have hD := norm_D x y
  rw [sym_identity]
  have k1 := p3 _ _ _ _ _ _ rA eB eA
  have k2 := p3 _ _ _ _ _ _ tA rB eA
  have k3 := p3 _ _ _ _ _ _ tA tB rA
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add k1 k2)) k3)) hD)) rC).trans ?_
  have ha : α ≤ r / 2 := by linarith
  have hb : β ≤ r := by linarith
  have hmono : α ^ 3 * (6 / 5) * (6 / 5) * (6 / 5) + 6 / 5 * (β ^ 3 * (6 / 5)) * (6 / 5) +
      6 / 5 * (6 / 5) * (α ^ 3 * (6 / 5)) +
      (α * (β * β) / 2 + α * α * β / 2 + α * α * (β * β) / 4 + β * (α * α) / 2 + β * β * α / 2 +
        β * β * (α * α) / 4 + α * α * α + α * α * (α * α) / 4 +
        (α + α * α / 2) * (β + β * β / 2) * (α + α * α / 2)) + r ^ 3 * (6 / 5) ≤
      (r/2) ^ 3 * (6 / 5) * (6 / 5) * (6 / 5) + 6 / 5 * (r ^ 3 * (6 / 5)) * (6 / 5) +
      6 / 5 * (6 / 5) * ((r/2) ^ 3 * (6 / 5)) +
      ((r/2) * (r * r) / 2 + (r/2) * (r/2) * r / 2 + (r/2) * (r/2) * (r * r) / 4 + r * ((r/2) * (r/2)) / 2 +
        r * r * (r/2) / 2 + r * r * ((r/2) * (r/2)) / 4 + (r/2) * (r/2) * (r/2) +
        (r/2) * (r/2) * ((r/2) * (r/2)) / 4 +
        ((r/2) + (r/2) * (r/2) / 2) * (r + r * r / 2) * ((r/2) + (r/2) * (r/2) / 2)) + r ^ 3 * (6 / 5) := by
    gcongr
  refine hmono.trans ?_
  have hr2 : r ^ 4 ≤ r ^ 3 / 10 := by
    have : r ^ 4 = r ^ 3 * r := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left hr1 (by positivity) |>.trans (by ring_nf; rfl)
  nlinarith [pow_nonneg hr0 3, pow_nonneg hr0 4, pow_nonneg hr0 5, pow_nonneg hr0 6,
    mul_le_mul_of_nonneg_left hr1 (pow_nonneg hr0 4), mul_le_mul_of_nonneg_left hr1 (pow_nonneg hr0 5)]


theorem conj_bound (a O : 𝔸) (hO : ‖O‖ ≤ 1) :
    ‖NormedSpace.exp a * O * NormedSpace.exp (-a) - O‖ ≤ 2 * ‖a‖ * Real.exp (2 * ‖a‖) := by
  have e : NormedSpace.exp a * O * NormedSpace.exp (-a) - O =
      (NormedSpace.exp a - 1) * O * NormedSpace.exp (-a) + O * (NormedSpace.exp (-a) - 1) := by
    noncomm_ring
  rw [e]
  have h1 := norm_R1 a
  have h2 := norm_R1 (-a)
  rw [norm_neg] at h2
  have h3 := norm_exp_le (-a)
  rw [norm_neg] at h3
  have ha := norm_nonneg a
  have hE1 : 1 ≤ Real.exp ‖a‖ := Real.one_le_exp ha
  calc ‖(NormedSpace.exp a - 1) * O * NormedSpace.exp (-a) + O * (NormedSpace.exp (-a) - 1)‖
      ≤ ‖NormedSpace.exp a - 1‖ * ‖O‖ * ‖NormedSpace.exp (-a)‖ + ‖O‖ * ‖NormedSpace.exp (-a) - 1‖ :=
        (norm_add_le _ _).trans (add_le_add (nm3 _ _ _) (norm_mul_le _ _))
    _ ≤ (‖a‖ * Real.exp ‖a‖) * 1 * Real.exp ‖a‖ + 1 * (‖a‖ * Real.exp ‖a‖) := by gcongr
    _ ≤ 2 * ‖a‖ * Real.exp (2 * ‖a‖) := by
        rw [show 2 * ‖a‖ = ‖a‖ + ‖a‖ by ring, Real.exp_add]
        nlinarith [Real.exp_pos ‖a‖, mul_nonneg ha (Real.exp_pos ‖a‖).le]

end TFIMPhaseDiagram.Classical.P10T
section L2sec
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder


namespace TFIMPhaseDiagram.Classical.P10L
open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
set_option linter.unusedSectionVars false

abbrev Mt (ι : Type) [Fintype ι] [DecidableEq ι] := Matrix ι ι ℂ


lemma norm_le_of_sandwich (X : Mt ι) (hX : IsSelfAdjoint X) (c : ℝ)
    (h1 : X ≤ algebraMap ℝ (Mt ι) c) (h2 : algebraMap ℝ (Mt ι) (-c) ≤ X) : ‖X‖ ≤ c := by
  have hs1 := (le_algebraMap_iff_spectrum_le hX).1 h1
  have hs2 := (algebraMap_le_iff_le_spectrum hX).1 h2
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum hX with h | h
  · exact hs1 _ h
  · have := hs2 _ h; linarith

lemma exp_ge (P : Mt ι) (hP : IsSelfAdjoint P) :
    algebraMap ℝ (Mt ι) (Real.exp (-‖P‖)) ≤ NormedSpace.exp P := by
  rw [← CFC.real_exp_eq_normedSpace_exp hP]
  refine algebraMap_le_cfc _ _ _ (fun x hx => ?_) (by fun_prop) hP
  apply Real.exp_le_exp.2
  have := spectrum.norm_le_norm_of_mem hx
  rw [Real.norm_eq_abs] at this
  linarith [neg_abs_le x]

lemma exp_add_alg (P : Mt ι) (c : ℝ) :
    NormedSpace.exp (P + algebraMap ℝ (Mt ι) c) = Real.exp c • NormedSpace.exp P := by
  rw [Matrix.exp_add_of_commute _ _ (Algebra.commutes c P).symm, Real.exp_eq_exp_ℝ,
    ← NormedSpace.algebraMap_exp_comm, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]


lemma log_bound (S P : Mt ι) (hP : IsSelfAdjoint P) (hS : IsStrictlyPositive S) (δ : ℝ)
    (hδ : ‖S - NormedSpace.exp P‖ * Real.exp ‖P‖ ≤ δ) (hδ1 : δ ≤ 1 / 2) :
    ‖CFC.log S - P‖ ≤ 2 * δ := by
  set ε := ‖S - NormedSpace.exp P‖
  have hε0 : 0 ≤ ε := norm_nonneg _
  have hδ0 : 0 ≤ δ := le_trans (by positivity) hδ
  have hSa : IsSelfAdjoint S := hS.isSelfAdjoint
  have hEa : IsSelfAdjoint (S - NormedSpace.exp P) := hSa.sub (IsSelfAdjoint.exp hP)
  have hexp0 : 0 ≤ NormedSpace.exp P := hP.exp_nonneg
  have hge := exp_ge P hP
  -- ε ≤ δ e^{-‖P‖}
  have hεδ : ε ≤ δ * Real.exp (-‖P‖) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]; exact hδ
  have hE1 : S - NormedSpace.exp P ≤ δ • NormedSpace.exp P := by
    calc S - NormedSpace.exp P ≤ algebraMap ℝ (Mt ι) ε := hEa.le_algebraMap_norm_self
      _ ≤ algebraMap ℝ (Mt ι) (δ * Real.exp (-‖P‖)) := by
          exact algebraMap_le_algebraMap.2 hεδ |>.trans le_rfl
      _ = δ • algebraMap ℝ (Mt ι) (Real.exp (-‖P‖)) := by rw [map_mul, Algebra.smul_def]
      _ ≤ δ • NormedSpace.exp P := smul_le_smul_of_nonneg_left hge hδ0
  have hE2 : -(δ • NormedSpace.exp P) ≤ S - NormedSpace.exp P := by
    calc -(δ • NormedSpace.exp P) ≤ -(algebraMap ℝ (Mt ι) (δ * Real.exp (-‖P‖))) := by
          rw [neg_le_neg_iff, map_mul, ← Algebra.smul_def]
          exact smul_le_smul_of_nonneg_left hge hδ0
      _ ≤ -(algebraMap ℝ (Mt ι) ε) := neg_le_neg (algebraMap_le_algebraMap.2 hεδ)
      _ ≤ S - NormedSpace.exp P := hEa.neg_algebraMap_norm_le_self
  have hup : S ≤ NormedSpace.exp (P + algebraMap ℝ (Mt ι) δ) := by
    rw [exp_add_alg]
    calc S = NormedSpace.exp P + (S - NormedSpace.exp P) := by abel
      _ ≤ NormedSpace.exp P + δ • NormedSpace.exp P := add_le_add_right hE1 _
      _ = (1 + δ) • NormedSpace.exp P := by rw [add_smul, one_smul]
      _ ≤ Real.exp δ • NormedSpace.exp P := by
          apply smul_le_smul_of_nonneg_right _ hexp0
          linarith [Real.add_one_le_exp δ]
  have hlo : NormedSpace.exp (P + algebraMap ℝ (Mt ι) (-(2 * δ))) ≤ S := by
    rw [exp_add_alg]
    have hb : Real.exp (-(2 * δ)) ≤ 1 - δ := by
      have h1 : Real.exp (-(2 * δ)) * (1 + 2 * δ) ≤ 1 := by
        have := Real.add_one_le_exp (2 * δ)
        have h2 : Real.exp (-(2 * δ)) * Real.exp (2 * δ) = 1 := by
          rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (-(2 * δ))]
      have h3 : 1 ≤ (1 - δ) * (1 + 2 * δ) := by nlinarith
      nlinarith [Real.exp_pos (-(2 * δ))]
    calc Real.exp (-(2 * δ)) • NormedSpace.exp P ≤ (1 - δ) • NormedSpace.exp P :=
          smul_le_smul_of_nonneg_right hb hexp0
      _ = NormedSpace.exp P + -(δ • NormedSpace.exp P) := by rw [sub_smul, one_smul]; abel
      _ ≤ NormedSpace.exp P + (S - NormedSpace.exp P) := add_le_add_right hE2 _
      _ = S := by abel
  have hsa1 : IsSelfAdjoint (P + algebraMap ℝ (Mt ι) δ) :=
    hP.add (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all δ))
  have hsa2 : IsSelfAdjoint (P + algebraMap ℝ (Mt ι) (-(2 * δ))) :=
    hP.add (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all _))
  have hpos : IsStrictlyPositive (NormedSpace.exp (P + algebraMap ℝ (Mt ι) (-(2 * δ)))) :=
    (Matrix.isUnit_exp _).isStrictlyPositive hsa2.exp_nonneg
  have hL1 := CFC.log_le_log hup hS
  rw [CFC.log_exp _ hsa1] at hL1
  have hL2 := CFC.log_le_log hlo hpos
  rw [CFC.log_exp _ hsa2] at hL2
  apply norm_le_of_sandwich _ ((IsSelfAdjoint.log).sub hP)
  · calc CFC.log S - P ≤ P + algebraMap ℝ (Mt ι) δ - P := sub_le_sub_right hL1 _
      _ = algebraMap ℝ (Mt ι) δ := by abel
      _ ≤ algebraMap ℝ (Mt ι) (2 * δ) := algebraMap_le_algebraMap.2 (by linarith)
  · calc algebraMap ℝ (Mt ι) (-(2 * δ)) = P + algebraMap ℝ (Mt ι) (-(2 * δ)) - P := by abel
      _ ≤ CFC.log S - P := sub_le_sub_right hL2 _

end TFIMPhaseDiagram.Classical.P10L

end L2sec


namespace TFIMPhaseDiagram.Classical.P10
open TFIMPhaseDiagram.Classical Matrix

lemma entry_herm (p : Pauli) (x y : Bool) : star (pauliEntry p x y) = pauliEntry p y x := by
  cases p <;> cases x <;> cases y <;>
    simp [pauliEntry, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.one_apply]

lemma entry_sq (p : Pauli) (x y : Bool) :
    ∑ β : Bool, pauliEntry p x β * pauliEntry p β y = if x = y then 1 else 0 := by
  cases p <;> cases x <;> cases y <;>
    simp [pauliEntry, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.one_apply,
      Fintype.sum_bool]

lemma pauli_herm {n : ℕ} (P : Fin n → Pauli) : (pauliString P).IsHermitian := by
  ext a b
  simp only [conjTranspose_apply, pauliString, star_prod, entry_herm]

lemma pauli_sq {n : ℕ} (P : Fin n → Pauli) : pauliString P * pauliString P = 1 := by
  ext a c
  rw [mul_apply]
  simp only [pauliString, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i β => pauliEntry (P i) (a i) β * pauliEntry (P i) β (c i))]
  simp only [entry_sq]
  rw [one_apply]
  by_cases h : a = c
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ : ∃ k, a k ≠ c k := by
      by_contra hh; push_neg at hh; exact h (funext hh)
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

end TFIMPhaseDiagram.Classical.P10

section L2main
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace TFIMPhaseDiagram.Classical.P10
open TFIMPhaseDiagram.Classical Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]
set_option linter.unusedSectionVars false

lemma eop_le (X : Matrix ι ι ℂ) : euclideanOpNorm X ≤ ‖X‖ := by
  unfold euclideanOpNorm
  apply Real.sSup_le _ (norm_nonneg _)
  rintro r ⟨x, hx, rfl⟩
  have := Matrix.l2_opNorm_mulVec X x
  rw [hx, mul_one] at this
  exact this

lemma entry_le (X : Matrix ι ι ℂ) (a : ι) : ‖X a a‖ ≤ ‖X‖ := by
  have h1 := Matrix.l2_opNorm_mulVec X (EuclideanSpace.single a (1 : ℂ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℂ).symm (X *ᵥ (EuclideanSpace.single a (1:ℂ)))) a
  have e : ((EuclideanSpace.equiv ι ℂ).symm (X *ᵥ (EuclideanSpace.single a (1:ℂ)))) a = X a a := by
    simp [EuclideanSpace.single, mulVec, dotProduct, Pi.single_apply]
  rw [e] at h2
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at h1
  exact h2.trans h1

lemma norm_inv_herm (O : Matrix ι ι ℂ) (hO : star O * O = 1) : ‖O‖ ≤ 1 := by
  have h := CStarRing.norm_star_mul_self (x := O)
  rw [hO] at h
  have h1 : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · rw [Subsingleton.elim (1 : Matrix ι ι ℂ) 0, norm_zero]; norm_num
    · rw [norm_one]
  nlinarith [norm_nonneg O]

lemma tr_exp_bound (K X : Matrix ι ι ℂ) (hK : K.IsHermitian) :
    ‖trace (NormedSpace.exp K * X)‖ ≤ ‖X‖ * (trace (NormedSpace.exp K)).re := by
  rw [P32G.tr_exp_mul K X hK, P32G.tr_exp_eq K hK, Complex.ofReal_re, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  set V := hK.eigenvectorUnitary.1
  have hV : V ∈ unitaryGroup ι ℂ := hK.eigenvectorUnitary.2
  have hV1 : ‖V‖ ≤ 1 := norm_inv_herm V (P32G.star_mul_unit V hV)
  have hV2 : ‖star V‖ ≤ 1 := norm_inv_herm (star V) (by rw [star_star]; exact P32G.unit_mul_star V hV)
  have hb : ‖(star V * X * V) a a‖ ≤ ‖X‖ := by
    refine (entry_le _ a).trans ?_
    calc ‖star V * X * V‖ ≤ ‖star V‖ * ‖X‖ * ‖V‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ‖X‖ * 1 := by gcongr
      _ = ‖X‖ := by ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le


lemma localZ_eq {n : ℕ} (i : Fin n) :
    localPauli .Z i = diagonal (fun a : Bits n => if a i then (-1 : ℂ) else 1) := by
  ext a b
  simp only [localPauli, pauliString, diagonal_apply]
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    rw [Finset.prod_eq_single i]
    · simp [pauliEntry, QAlgorithms.pauliZ]
    · intro k _ hk; simp [hk, pauliEntry]
    · simp
  · rw [if_neg hab]
    obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
      by_contra h; push Not at h; exact hab (funext h)
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    by_cases hki : k = i
    · simp [hki, pauliEntry, QAlgorithms.pauliZ, diagonal_apply]
      subst hki; simp [hk]
    · simp [hki, pauliEntry, hk]

lemma sa_pauli {n : ℕ} (P : Fin n → Pauli) : IsSelfAdjoint (pauliString P) := pauli_herm P

lemma norm_pauli {n : ℕ} (P : Fin n → Pauli) : ‖pauliString P‖ ≤ 1 :=
  norm_inv_herm _ (by rw [(sa_pauli P).star_eq]; exact pauli_sq P)

lemma sa_real_smul {n : ℕ} (r : ℝ) (X : QMat n) (hX : IsSelfAdjoint X) :
    IsSelfAdjoint ((r : ℂ) • X) := IsSelfAdjoint.smul (Complex.conj_ofReal r) hX

lemma ZZ_sa {n : ℕ} (i j : Fin n) : IsSelfAdjoint (localPauli .Z i * localPauli .Z j) := by
  rw [localZ_eq, localZ_eq, diagonal_mul_diagonal]
  unfold IsSelfAdjoint
  rw [star_eq_conjTranspose, diagonal_conjTranspose]
  congr 1; funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

lemma hz_sa {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) : IsSelfAdjoint (hz J h) := by
  unfold hz
  refine IsSelfAdjoint.add (IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) ?_) ?_
  · exact isSelfAdjoint_sum _ fun i _ => isSelfAdjoint_sum _ fun j _ => sa_real_smul _ _ (ZZ_sa i j)
  · exact isSelfAdjoint_sum _ fun i _ => sa_real_smul _ _ (sa_pauli _)

lemma hx_sa {n : ℕ} (η : Fin n → ℝ) : IsSelfAdjoint (hx η) := by
  unfold hx
  exact isSelfAdjoint_sum _ fun i _ => sa_real_smul _ _ (sa_pauli _)

lemma norm_hz {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) :
    ‖hz J h‖ ≤ (1 / 2) * ∑ i, ∑ j, |J i j| + ∑ i, |h i| := by
  unfold hz
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have := (norm_mul_le (localPauli .Z i) (localPauli .Z j)).trans
      (mul_le_one₀ (norm_pauli _) (norm_nonneg _) (norm_pauli _))
    nlinarith [abs_nonneg (J i j)]
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have := norm_pauli (n := n) (fun j => if j = i then Pauli.Z else Pauli.I)
    have h2 : ‖localPauli Pauli.Z i‖ ≤ 1 := this
    nlinarith [abs_nonneg (h i)]

lemma norm_hx {n : ℕ} (η : Fin n → ℝ) : ‖hx η‖ ≤ ∑ i, |η i| := by
  unfold hx
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖localPauli Pauli.X i‖ ≤ 1 := norm_pauli _
  nlinarith [abs_nonneg (η i)]


lemma sum_le_rowNorm {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) :
    ∑ i, ∑ j, |J i j| ≤ n * rowNorm J := by
  have : ∀ i, ∑ j, |J i j| ≤ rowNorm J := fun i =>
    le_ciSup (f := fun i => ∑ j, |J i j|) (Set.finite_range _).bddAbove i
  calc ∑ i, ∑ j, |J i j| ≤ ∑ _i : Fin n, rowNorm J := Finset.sum_le_sum fun i _ => this i
    _ = n * rowNorm J := by simp

lemma sum_le_maxField {n : ℕ} (h : Fin n → ℝ) : ∑ i, |h i| ≤ n * maxField h := by
  have : ∀ i, |h i| ≤ maxField h := fun i =>
    le_ciSup (f := fun i => |h i|) (Set.finite_range _).bddAbove i
  calc ∑ i, |h i| ≤ ∑ _i : Fin n, maxField h := Finset.sum_le_sum fun i _ => this i
    _ = n * maxField h := by simp

lemma rowNorm_nonneg {n : ℕ} (hn : 0 < n) (J : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ rowNorm J :=
  le_trans (Finset.sum_nonneg fun j _ => abs_nonneg (J ⟨0, hn⟩ j))
    (le_ciSup (f := fun i => ∑ j, |J i j|) (Set.finite_range _).bddAbove ⟨0, hn⟩)

lemma maxField_nonneg {n : ℕ} (hn : 0 < n) (h : Fin n → ℝ) : 0 ≤ maxField h :=
  le_trans (abs_nonneg (h ⟨0, hn⟩))
    (le_ciSup (f := fun i => |h i|) (Set.finite_range _).bddAbove ⟨0, hn⟩)

lemma pow_conj {R : Type*} [Monoid R] (u u' v : R) (h : u' * u = 1) (M : ℕ) :
    u' * (u * v) ^ M * u = (v * u) ^ M := by
  have key : ∀ m : ℕ, (u * v) ^ m * u = u * (v * u) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc (u * v) ^ (m + 1) * u = (u * v) ^ m * u * (v * u) := by
            rw [pow_succ]; simp only [mul_assoc]
        _ = u * (v * u) ^ m * (v * u) := by rw [ih]
        _ = u * (v * u) ^ (m + 1) := by rw [pow_succ, mul_assoc]
  rw [mul_assoc, key, ← mul_assoc, h, one_mul]

end TFIMPhaseDiagram.Classical.P10

open TFIMPhaseDiagram.Classical TFIMPhaseDiagram.Classical.P10 in
theorem solution {n : ℕ} (hn : 0 < n) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : J.IsSymm) (h η : Fin n → ℝ) (hη : ∀ i, 0 ≤ η i)
    (P : Fin n → Pauli) (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (M : ℕ) (hM : 3 ≤ M)
    (hmesh : let c := rowNorm J + maxField h + maxField η
      (M : ℝ) ≥ 15 * max ((n : ℝ)*c/ε) (Real.sqrt (((n : ℝ)*c)^3/ε))) :
  ‖Matrix.trace (pauliString P * trotter J h η M) / Matrix.trace (trotter J h η M) -
    Matrix.trace (pauliString P * density J h η)‖ ≤ ε := by
  obtain ⟨hε0, hε1⟩ := hε
  set c := rowNorm J + maxField h + maxField η with hc
  have hm : (M : ℝ) ≥ 15 * max ((n : ℝ)*c/ε) (Real.sqrt (((n : ℝ)*c)^3/ε)) := hmesh
  have hrow0 := rowNorm_nonneg hn J
  have hmh0 := maxField_nonneg hn h
  have hmη0 := maxField_nonneg hn η
  have hc0 : 0 ≤ c := by linarith
  have hMpos : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  set nc := (n:ℝ) * c with hnc
  have hnc0 : 0 ≤ nc := by positivity
  have hm1 : 15 * (nc / ε) ≤ M := by
    have := le_max_left (nc / ε) (Real.sqrt (nc ^ 3 / ε)); linarith
  have hm2 : 225 * (nc ^ 3 / ε) ≤ (M:ℝ) ^ 2 := by
    have h1 := le_max_right (nc / ε) (Real.sqrt (nc ^ 3 / ε))
    have h2 : 15 * Real.sqrt (nc ^ 3 / ε) ≤ M := by linarith
    have h3 := Real.sq_sqrt (show 0 ≤ nc ^ 3 / ε by positivity)
    have h4 := Real.sqrt_nonneg (nc ^ 3 / ε)
    nlinarith
  -- operators
  set A := hx η with hAdef
  set B := hz J h with hBdef
  have hAB : ‖A‖ + ‖B‖ ≤ nc := by
    have h1 := norm_hx η
    have h2 := norm_hz J h
    have h3 := sum_le_rowNorm J
    have h4 := sum_le_maxField h
    have h5 := sum_le_maxField η
    have hn0 : (0:ℝ) ≤ n := by positivity
    have : (n:ℝ) * rowNorm J / 2 ≤ n * rowNorm J := by nlinarith
    simp only [hnc, hc]
    nlinarith
  set a : QMat n := (2:ℂ)⁻¹ • ((1/(M:ℂ)) • A) with hadef
  set b : QMat n := (1/(M:ℂ)) • B with hbdef
  have hMc : ‖(1/(M:ℂ))‖ = 1 / M := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  have hna : ‖a‖ = ‖A‖ / (2 * M) := by
    rw [hadef, norm_smul, norm_smul, hMc, norm_inv, Complex.norm_ofNat]; field_simp
  have hnb : ‖b‖ = ‖B‖ / M := by
    rw [hbdef, norm_smul, hMc]; field_simp
  set r := (‖A‖ + ‖B‖) / M with hrdef
  have hr : 2 * ‖a‖ + ‖b‖ = r := by rw [hna, hnb, hrdef]; field_simp
  have hr0 : 0 ≤ r := div_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) hMpos.le
  have hrε : r ≤ ε / 15 := by
    rw [hrdef, div_le_iff₀ hMpos]
    have : nc ≤ ε / 15 * M := by
      have := hm1
      rw [mul_div_assoc'] at this
      rw [div_le_iff₀ hε0] at this
      nlinarith
    linarith
  have hr1 : r ≤ 1 / 10 := by linarith
  have hEr : Real.exp r ≤ 6 / 5 := by
    have := Real.exp_bound_div_one_sub_of_interval hr0 (by linarith)
    refine this.trans ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  -- self-adjointness
  have hAsa : IsSelfAdjoint A := hx_sa η
  have hBsa : IsSelfAdjoint B := hz_sa J h
  have hsc : ∀ (x : ℝ) (X : QMat n), IsSelfAdjoint X → IsSelfAdjoint ((x : ℂ) • X) :=
    fun x X hX => sa_real_smul x X hX
  have hasa : IsSelfAdjoint a := by
    have e : a = (((2:ℝ)⁻¹ * (1 / (M:ℝ)) : ℝ) : ℂ) • A := by
      rw [hadef, smul_smul]; congr 1; push_cast; ring
    rw [e]; exact hsc _ _ hAsa
  have hbsa : IsSelfAdjoint b := by
    have e : b = ((1 / (M:ℝ) : ℝ) : ℂ) • B := by rw [hbdef]; congr 1; push_cast; ring
    rw [e]; exact hsc _ _ hBsa
  have hM0 : (M:ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have haa : a + a = (1/(M:ℂ)) • A := by
    rw [hadef, ← add_smul]; norm_num
  have hexpinv : NormedSpace.exp (-a) * NormedSpace.exp a = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl a)), neg_add_cancel,
      NormedSpace.exp_zero]
  have htrot : trotter J h η M = NormedSpace.exp (-a) *
      (NormedSpace.exp a * NormedSpace.exp b * NormedSpace.exp a) ^ M * NormedSpace.exp a := by
    have := pow_conj (NormedSpace.exp a) (NormedSpace.exp (-a))
      (NormedSpace.exp b * NormedSpace.exp a) hexpinv M
    unfold trotter matrixExp
    rw [← haa, Matrix.exp_add_of_commute a a (Commute.refl a)]
    rw [show NormedSpace.exp a * NormedSpace.exp b * NormedSpace.exp a =
      NormedSpace.exp a * (NormedSpace.exp b * NormedSpace.exp a) by rw [mul_assoc], this, mul_assoc]
  -- the symmetric Trotter factor
  set S : QMat n := NormedSpace.exp a * NormedSpace.exp b * NormedSpace.exp a with hSdef
  have hSpos : IsStrictlyPositive S := by
    have hb2sa : IsSelfAdjoint ((((2:ℝ)⁻¹ : ℝ) : ℂ) • b) := hsc _ _ hbsa
    have hbb : NormedSpace.exp ((((2:ℝ)⁻¹ : ℝ) : ℂ) • b) * NormedSpace.exp ((((2:ℝ)⁻¹ : ℝ) : ℂ) • b) =
        NormedSpace.exp b := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul]; norm_num
    have e : S = star (NormedSpace.exp ((((2:ℝ)⁻¹ : ℝ) : ℂ) • b) * NormedSpace.exp a) *
        (NormedSpace.exp ((((2:ℝ)⁻¹ : ℝ) : ℂ) • b) * NormedSpace.exp a) := by
      rw [star_mul, (IsSelfAdjoint.exp hasa).star_eq, (IsSelfAdjoint.exp hb2sa).star_eq, hSdef]
      rw [← hbb]; simp only [mul_assoc]
    refine IsUnit.isStrictlyPositive ?_ ?_
    · exact ((Matrix.isUnit_exp a).mul (Matrix.isUnit_exp b)).mul (Matrix.isUnit_exp a)
    · rw [e]; exact star_mul_self_nonneg _
  set L : QMat n := CFC.log S with hLdef
  have hLsa : IsSelfAdjoint L := IsSelfAdjoint.log
  have hSL : NormedSpace.exp L = S := CFC.exp_log S hSpos
  have hSM : S ^ M = NormedSpace.exp ((M:ℂ) • L) := by
    rw [← hSL, ← Matrix.exp_nsmul, Nat.cast_smul_eq_nsmul]
  set Pm : QMat n := a + b + a with hPmdef
  have hPsa : IsSelfAdjoint Pm := (hasa.add hbsa).add hasa
  have hPn : ‖Pm‖ ≤ r := by
    have h1 := norm_add_le (a + b) a
    have h2 := norm_add_le a b
    linarith
  have hK : (M:ℂ) • Pm = hamiltonian J h η := by
    rw [hPmdef, show a + b + a = (a + a) + b by abel, haa, hbdef, smul_add, smul_smul, smul_smul,
      mul_one_div_cancel hM0, one_smul, one_smul]
    unfold hamiltonian; abel
  have h3 : ‖S - NormedSpace.exp Pm‖ ≤ 8 * r ^ 3 := P10T.sym3 a b r hr.le hr1
  have hEP : Real.exp ‖Pm‖ ≤ 6 / 5 := (Real.exp_le_exp.2 hPn).trans hEr
  have hδ : ‖S - NormedSpace.exp Pm‖ * Real.exp ‖Pm‖ ≤ 8 * r ^ 3 * (6 / 5) :=
    mul_le_mul h3 hEP (Real.exp_pos _).le (by have := pow_nonneg hr0 3; linarith)
  have hδ12 : ‖S - NormedSpace.exp Pm‖ * Real.exp ‖Pm‖ ≤ 1 / 2 := by
    refine hδ.trans ?_
    have : r ^ 3 ≤ (1/10) ^ 3 := pow_le_pow_left₀ hr0 hr1 3
    nlinarith
  have hlog := P10L.log_bound S Pm hPsa hSpos _ le_rfl hδ12
  -- the Gibbs comparison
  have hMr : ((M:ℝ) : ℂ) = (M:ℂ) := Complex.ofReal_natCast M
  have hMsa : ∀ X : QMat n, IsSelfAdjoint X → IsSelfAdjoint ((M:ℂ) • X) := by
    intro X hX; rw [← hMr]; exact hsc _ _ hX
  set K : QMat n := hamiltonian J h η with hKdef
  have hKsa : IsSelfAdjoint K := by rw [← hK]; exact hMsa _ hPsa
  set C : QMat n := (M:ℂ) • L - K with hCdef
  have hCsa : IsSelfAdjoint C := (hMsa _ hLsa).sub hKsa
  have hKC : K + C = (M:ℂ) • L := by rw [hCdef]; abel
  have hCn : euclideanOpNorm C ≤ M * (2 * (‖S - NormedSpace.exp Pm‖ * Real.exp ‖Pm‖)) := by
    refine (eop_le C).trans ?_
    have e : C = (M:ℂ) • (L - Pm) := by rw [hCdef, smul_sub, hK]
    rw [e, norm_smul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hlog hMpos.le
  set O : QMat n := pauliString P with hOdef
  have hg := P32G.gibbs_diff K C O hKsa hCsa (pauli_herm P) (pauli_sq P)
  rw [hKC, ← hSM] at hg
  -- conjugation error
  set X : QMat n := NormedSpace.exp a * O * NormedSpace.exp (-a) - O with hXdef
  have h2a : 2 * ‖a‖ ≤ r := by have := norm_nonneg b; linarith
  have hXn : ‖X‖ ≤ r * (6 / 5) := by
    refine (P10T.conj_bound a O (norm_pauli P)).trans ?_
    have hE2 : Real.exp (2 * ‖a‖) ≤ 6 / 5 := (Real.exp_le_exp.2 h2a).trans hEr
    exact mul_le_mul h2a hE2 (Real.exp_pos _).le hr0
  have hMLh : ((M:ℂ) • L).IsHermitian := hMsa _ hLsa
  have htb := tr_exp_bound ((M:ℂ) • L) X hMLh
  rw [← hSM] at htb
  have hzT := P32G.tr_exp_eq ((M:ℂ) • L) hMLh
  have hzpos := P32G.z_pos ((M:ℂ) • L) hMLh
  rw [← hSM] at hzT
  set z := ∑ i, Real.exp (hMLh.eigenvalues i) with hzdef
  -- algebra
  have hexpinv' : NormedSpace.exp a * NormedSpace.exp (-a) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl a)), add_neg_cancel,
      NormedSpace.exp_zero]
  have e1 : Matrix.trace (O * trotter J h η M) =
      Matrix.trace (S ^ M * X) + Matrix.trace (S ^ M * O) := by
    rw [htrot, ← Matrix.trace_add, ← Matrix.mul_add, hXdef, sub_add_cancel]
    rw [show O * (NormedSpace.exp (-a) * S ^ M * NormedSpace.exp a) =
      (O * NormedSpace.exp (-a) * S ^ M) * NormedSpace.exp a by simp only [mul_assoc],
      Matrix.trace_mul_comm]
    rw [show NormedSpace.exp a * (O * NormedSpace.exp (-a) * S ^ M) =
      (NormedSpace.exp a * O * NormedSpace.exp (-a)) * S ^ M by simp only [mul_assoc],
      Matrix.trace_mul_comm]
  have e2 : Matrix.trace (trotter J h η M) = Matrix.trace (S ^ M) := by
    rw [htrot, Matrix.trace_mul_comm, ← mul_assoc, hexpinv', one_mul]
  have e3 : Matrix.trace (O * density J h η) =
      Matrix.trace (NormedSpace.exp K * O) / Matrix.trace (NormedSpace.exp K) := by
    unfold density partition matrixExp
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm O, inv_mul_eq_div]
  rw [e1, e2, e3, add_div]
  have hTne : Matrix.trace (S ^ M) ≠ 0 := by rw [hzT]; exact_mod_cast hzpos.ne'
  calc ‖Matrix.trace (S ^ M * X) / Matrix.trace (S ^ M) + Matrix.trace (S ^ M * O) /
        Matrix.trace (S ^ M) - Matrix.trace (NormedSpace.exp K * O) / Matrix.trace (NormedSpace.exp K)‖
      ≤ ‖Matrix.trace (S ^ M * X) / Matrix.trace (S ^ M)‖ +
        ‖Matrix.trace (S ^ M * O) / Matrix.trace (S ^ M) -
          Matrix.trace (NormedSpace.exp K * O) / Matrix.trace (NormedSpace.exp K)‖ := by
        rw [add_sub_assoc]; exact norm_add_le _ _
    _ ≤ ‖X‖ + M * (2 * (‖S - NormedSpace.exp Pm‖ * Real.exp ‖Pm‖)) := by
        refine add_le_add ?_ (hg.trans hCn)
        rw [norm_div, hzT, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzpos,
          div_le_iff₀ hzpos]
        rw [hzT, Complex.ofReal_re] at htb
        exact htb
    _ ≤ r * (6 / 5) + M * (2 * (8 * r ^ 3 * (6 / 5))) := by
        gcongr
    _ ≤ ε := by
        have hMr3 : (M:ℝ) * r ^ 3 ≤ ε / 225 := by
          have hs : ‖A‖ + ‖B‖ ≤ nc := hAB
          have hs0 : 0 ≤ ‖A‖ + ‖B‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
          have e : (M:ℝ) * r ^ 3 = (‖A‖ + ‖B‖) ^ 3 / (M:ℝ) ^ 2 := by
            rw [hrdef]; field_simp
          rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
          have h1 : (‖A‖ + ‖B‖) ^ 3 ≤ nc ^ 3 := pow_le_pow_left₀ hs0 hs 3
          have h2 : 225 * nc ^ 3 ≤ ε * (M:ℝ) ^ 2 := by
            have := hm2
            rw [mul_div_assoc', div_le_iff₀ hε0] at this
            linarith
          linarith [mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 225)]
        have e4 : (M:ℝ) * (2 * (8 * r ^ 3 * (6 / 5))) = 96 / 5 * ((M:ℝ) * r ^ 3) := by ring
        rw [e4]
        linarith
end L2main