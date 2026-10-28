-- Prove2me | solution 2 for YuanDGD.Linear.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T03:39:37.361207+00:00
-- url     : https://prove2.me/submissions/c39293e2-ec3d-4465-a7ad-6e8f7fb625cb

import Mathlib
import Definitions.Def_YuanDGD_Linear_Setting
import Theorems.Thm_Gradient_convex_first_order
import Theorems.Thm_Gradient_descent_lemma
import Theorems.Thm_Gradient_hasDerivAt_line

-- carved verbatim out of submission 7ebba3b7-cfe0-4a19-8613-21bb6aa9d9f3, lines 1212-1222

section
set_option autoImplicit false
open scoped InnerProductSpace RealInnerProductSpace
open YuanDGD.Linear Matrix

noncomputable def dgdC {n p : ℕ} (v : E p) : Stack n p := WithLp.toLp 2 (fun _ => v)

noncomputable def dgdE (n : ℕ) : Fin (Fintype.card (Fin n)) ≃ Fin n :=
  Fintype.equivOfCardEq (Fintype.card_fin _)

noncomputable def dgdH {n p : ℕ} (f : Fin n → E p → ℝ) (y : Stack n p) : Stack n p :=
  WithLp.toLp 2 (fun i => gradient (f i) (y i))

noncomputable def dgdXi {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → E p → ℝ) (α : ℝ)
    (y : Stack n p) : ℝ :=
  ∑ i, f i (y i) + (1 / (2 * α)) * (‖y‖ ^ 2 - ⟪y, mix W y⟫_ℝ)

theorem dgd_C_sub_smul {n p : ℕ} (a b : E p) (t : ℝ) :
    (dgdC (a - t • b) : Stack n p) = dgdC a - t • dgdC b := by
  ext i c; simp [dgdC]

theorem dgd_Gbar_lip {n p : ℕ} {G : SimpleGraph (Fin n)} {W : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → E p → ℝ} {Lf : Fin n → ℝ} (hA : Assumption1 G W f Lf) (a b : E p) :
    ‖(1 / (n : ℝ)) • gradSum f a - (1 / (n : ℝ)) • gradSum f b‖ ≤ Lbar Lf * ‖a - b‖ := by
  have hn : (0:ℝ) ≤ 1 / (n : ℝ) := by positivity
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hn]
  have h1 : gradSum f a - gradSum f b = ∑ i, (gradient (f i) a - gradient (f i) b) := by
    simp [gradSum, Finset.sum_sub_distrib]
  rw [h1]
  calc 1 / (n : ℝ) * ‖∑ i, (gradient (f i) a - gradient (f i) b)‖
      ≤ 1 / (n : ℝ) * ∑ i, ‖gradient (f i) a - gradient (f i) b‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) hn
    _ ≤ 1 / (n : ℝ) * ∑ i, Lf i * ‖a - b‖ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hA.lipschitz i a b) hn
    _ = Lbar Lf * ‖a - b‖ := by rw [← Finset.sum_mul]; unfold Lbar; ring

theorem dgd_hasGrad {n p : ℕ} {G : SimpleGraph (Fin n)} {W : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → E p → ℝ} {Lf : Fin n → ℝ} (hA : Assumption1 G W f Lf) (i : Fin n) (x : E p) :
    HasGradientAt (f i) (gradient (f i) x) x :=
  (hA.differentiable i x).hasGradientAt

theorem dgd_fbar_grad {n p : ℕ} {G : SimpleGraph (Fin n)} {W : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → E p → ℝ} {Lf : Fin n → ℝ} (hA : Assumption1 G W f Lf) (x : E p) :
    HasGradientAt (fbar f) ((1 / (n : ℝ)) • gradSum f x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have : ∀ i ∈ Finset.univ, HasFDerivAt (f i) (InnerProductSpace.toDual ℝ (E p)
      (gradient (f i) x)) x := fun i _ => hasGradientAt_iff_hasFDerivAt.1 (dgd_hasGrad hA i x)
  have h := (HasFDerivAt.sum this).const_mul (1 / (n : ℝ))
  have e : InnerProductSpace.toDual ℝ (E p) ((1 / (n : ℝ)) • gradSum f x) =
      (1 / (n : ℝ)) • ∑ i, InnerProductSpace.toDual ℝ (E p) (gradient (f i) x) := by
    simp [gradSum, map_sum]
  have e2 : fbar f = fun y => 1 / (n : ℝ) * (∑ i, f i) y := by
    funext y; simp [fbar, Finset.sum_apply]
  rw [e, e2]
  exact h

theorem dgd_Gbar_up {n p : ℕ} {G : SimpleGraph (Fin n)} {W : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → E p → ℝ} {Lf : Fin n → ℝ} (hA : Assumption1 G W f Lf) (x y : E p) :
    fbar f y ≤ fbar f x + ⟪(1 / (n : ℝ)) • gradSum f x, y - x⟫ + Lbar Lf / 2 * ‖y - x‖ ^ 2 :=
  Gradient.descent_lemma (G := fun z => (1 / (n : ℝ)) • gradSum f z) (dgd_fbar_grad hA) (dgd_Gbar_lip hA) x y

theorem dgd_Lbar_pos {n p : ℕ} {G : SimpleGraph (Fin n)} {W : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → E p → ℝ} {Lf : Fin n → ℝ} (hA : Assumption1 G W f Lf) : 0 < Lbar Lf := by
  have hn := hA.two_le
  unfold Lbar
  have : 0 < ∑ i, Lf i := Finset.sum_pos (fun i _ => hA.Lf_pos i) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  positivity

theorem dgd_gradsq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} {G : E → E} {L m : ℝ} (hL : 0 < L)
    (hup : ∀ x y, F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (hm : ∀ z, m ≤ F z) (x : E) : ‖G x‖ ^ 2 ≤ 2 * L * (F x - m) := by
  have h := hup x (x - (1 / L) • G x)
  have e1 : x - (1 / L) • G x - x = -((1 / L) • G x) := by abel
  rw [e1, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / L), real_inner_self_eq_norm_sq] at h
  have h2 := hm (x - (1 / L) • G x)
  have hL' : L ≠ 0 := hL.ne'
  have h5 : L / 2 * (1 / L * ‖G x‖) ^ 2 = 1 / (2 * L) * ‖G x‖ ^ 2 := by field_simp
  have h6 : 1 / L * ‖G x‖ ^ 2 = 2 * (1 / (2 * L) * ‖G x‖ ^ 2) := by field_simp
  have h7 : 2 * L * (1 / (2 * L) * ‖G x‖ ^ 2) = ‖G x‖ ^ 2 := by field_simp
  nlinarith

theorem dgd_Gbar_zero {n p : ℕ} {f : Fin n → E p → ℝ} {xs : E p} (hxs : xs ∈ Xstar f)
    {Lf : Fin n → ℝ} {G : SimpleGraph (Fin n)} {W : Matrix (Fin n) (Fin n) ℝ}
    (hA : Assumption1 G W f Lf) :
    (1 / (n : ℝ)) • gradSum f xs = 0 := by
  have hL := dgd_Lbar_pos hA
  have hn : (0:ℝ) < n := by have := hA.two_le; exact_mod_cast (by omega : 0 < n)
  have hup : ∀ x y, fbar f y ≤ fbar f x + ⟪(1 / (n : ℝ)) • gradSum f x, y - x⟫ +
      Lbar Lf / 2 * ‖y - x‖ ^ 2 := fun x y =>
    Gradient.descent_lemma (dgd_fbar_grad hA) (dgd_Gbar_lip hA) x y
  have hm : ∀ z, fbar f xs ≤ fbar f z := by
    intro z; unfold fbar
    have := hxs z
    have hn' : (0:ℝ) ≤ 1 / (n : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left this hn'
  have h := dgd_gradsq hL hup hm xs
  rw [sub_self, mul_zero] at h
  have h2 : ‖(1 / (n : ℝ)) • gradSum f xs‖ ^ 2 = 0 := le_antisymm h (sq_nonneg _)
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)

theorem dgd_Lf_le_Lh {n : ℕ} (Lf : Fin n → ℝ) (i : Fin n) : Lf i ≤ Lh Lf :=
  le_ciSup (Set.finite_range Lf).bddAbove i

theorem dgd_Lh_pos {n p : ℕ} {G : SimpleGraph (Fin n)} {W : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → E p → ℝ} {Lf : Fin n → ℝ} (hA : Assumption1 G W f Lf) : 0 < Lh Lf := by
  have hn := hA.two_le
  exact lt_of_lt_of_le (hA.Lf_pos ⟨0, by omega⟩) (dgd_Lf_le_Lh Lf _)

theorem dgd_mix_coord {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) (i : Fin n)
    (c : Fin p) : (mix W x) i c = ∑ j, W i j * x j c := by
  simp [mix]

theorem dgd_Xi_zero {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → E p → ℝ) (α : ℝ) :
    dgdXi W f α 0 = ∑ i, f i 0 := by
  unfold dgdXi
  have h : mix W (0 : Stack n p) = 0 := by ext i c; simp [dgd_mix_coord]
  simp [h]

theorem dgd_herm {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} (hW : Wᵀ = W) : W.IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact hW

theorem dgd_mix_add {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (x y : Stack n p) :
    mix W (x + y) = mix W x + mix W y := by
  ext i c
  simp [dgd_mix_coord, mul_add, Finset.sum_add_distrib]

theorem dgd_inner_coord {n p : ℕ} (x y : Stack n p) :
    ⟪x, y⟫_ℝ = ∑ c : Fin p, ∑ i : Fin n, x i c * y i c := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem dgd_mix_inner_symm {n p : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} (hW : Wᵀ = W)
    (x y : Stack n p) : ⟪mix W x, y⟫_ℝ = ⟪x, mix W y⟫_ℝ := by
  have hs : ∀ i k, W i k = W k i := fun i k => by
    have := congrFun (congrFun hW k) i; simpa using this
  rw [dgd_inner_coord, dgd_inner_coord]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [dgd_mix_coord, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hs i j]; ring

theorem dgd_inner_mix_coord {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (d : Stack n p) :
    ⟪d, mix W d⟫_ℝ = ∑ c : Fin p, ∑ i : Fin n, d i c * (W *ᵥ (fun j => d j c)) i := by
  rw [dgd_inner_coord]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
  rw [dgd_mix_coord]; rfl

theorem dgd_norm_sq_coord {n p : ℕ} (x : Stack n p) :
    ‖x‖ ^ 2 = ∑ c : Fin p, ∑ i : Fin n, x i c ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, dgd_inner_coord]
  simp [sq]

theorem dgd_lamN_le {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} (hh : W.IsHermitian) (hn : 2 ≤ n)
    (j : Fin n) : lamN W ≤ hh.eigenvalues j := by
  have h : lamN W = hh.eigenvalues₀ ⟨Fintype.card (Fin n) - 1, by rw [Fintype.card_fin]; omega⟩ := by
    unfold lamN; rw [dif_pos ⟨hh, hn⟩]
  rw [h]
  show _ ≤ hh.eigenvalues₀ _
  refine hh.eigenvalues₀_antitone ?_
  rw [Fin.le_def]
  have := ((dgdE n).symm j).isLt
  simp only
  omega

theorem dgd_parseval2 {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} (hh : W.IsHermitian)
    (u v : Fin n → ℝ) :
    ∑ j, (∑ i, (hh.eigenvectorBasis j) i * u i) * (∑ i, (hh.eigenvectorBasis j) i * v i) =
      ∑ i, u i * v i := by
  have h := (hh.eigenvectorBasis).sum_inner_mul_inner (WithLp.toLp 2 u) (WithLp.toLp 2 v)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h
  convert h using 2 <;> simp [mul_comm]

theorem dgd_spec_coeff {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} (hh : W.IsHermitian)
    (v : Fin n → ℝ) (j : Fin n) :
    ∑ i, (hh.eigenvectorBasis j) i * (W *ᵥ v) i =
      hh.eigenvalues j * ∑ i, (hh.eigenvectorBasis j) i * v i := by
  have hsymm : ∀ i k, W i k = W k i := by
    intro i k
    have := hh.apply k i
    simpa using this
  have hev := hh.mulVec_eigenvectorBasis j
  calc ∑ i, (hh.eigenvectorBasis j) i * (W *ᵥ v) i
      = ∑ i, (hh.eigenvectorBasis j) i * ∑ k, W i k * v k := by
        simp [Matrix.mulVec, dotProduct]
    _ = ∑ k, (∑ i, W i k * (hh.eigenvectorBasis j) i) * v k := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ k, (W *ᵥ ⇑(hh.eigenvectorBasis j)) k * v k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        congr 1
        simp [Matrix.mulVec, dotProduct, hsymm _ k]
    _ = hh.eigenvalues j * ∑ i, (hh.eigenvectorBasis j) i * v i := by
        rw [hev, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [mul_assoc]

theorem dgd_quad {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} (hh : W.IsHermitian) (v : Fin n → ℝ) :
    ∑ i, v i * (W *ᵥ v) i =
      ∑ j, hh.eigenvalues j * (∑ i, (hh.eigenvectorBasis j) i * v i) ^ 2 := by
  rw [← dgd_parseval2 hh v (W *ᵥ v)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dgd_spec_coeff hh v j]; ring

theorem dgd_rayleigh {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} (hh : W.IsHermitian) (hn : 2 ≤ n)
    (v : Fin n → ℝ) : lamN W * ∑ i, v i ^ 2 ≤ ∑ i, v i * (W *ᵥ v) i := by
  rw [dgd_quad hh v]
  have h2 := dgd_parseval2 hh v v
  have h3 : ∑ i, v i ^ 2 = ∑ j, (∑ i, (hh.eigenvectorBasis j) i * v i) ^ 2 := by
    rw [show ∑ i, v i ^ 2 = ∑ i, v i * v i by simp [sq], ← h2]
    simp [sq]
  rw [h3, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (dgd_lamN_le hh hn j) (sq_nonneg _)

theorem dgd_mix_rayleigh_low {n p : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} (hh : W.IsHermitian)
    (hn : 2 ≤ n) (d : Stack n p) : lamN W * ‖d‖ ^ 2 ≤ ⟪d, mix W d⟫_ℝ := by
  rw [dgd_inner_mix_coord, dgd_norm_sq_coord, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  have := dgd_rayleigh hh hn (fun j => d j c)
  simpa using this

theorem dgd_lyap_step {n p : ℕ} {G : SimpleGraph (Fin n)} {W : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → E p → ℝ} {Lf : Fin n → ℝ} (hA : Assumption1 G W f Lf)
    {α : ℝ} (hα : 0 < α) (hα1 : α < (1 + lamN W) / Lh Lf) (y : Stack n p) :
    dgdXi W f α (mix W y - α • dgdH f y) ≤ dgdXi W f α y := by
  have hLh : 0 < Lh Lf := dgd_Lh_pos hA
  have hLhα : α * Lh Lf < 1 + lamN W := by
    rw [lt_div_iff₀ hLh] at hα1; linarith
  have hh := dgd_herm hA.symm
  have hn := hA.two_le
  obtain ⟨H, hH⟩ : ∃ H, H = dgdH f y := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = y - mix W y := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = mix W y - α • H - y := ⟨_, rfl⟩
  have hyp : mix W y - α • H = y + d := by rw [hd]; abel
  have hd' : d = -(α • H + u) := by rw [hd, hu]; abel
  rw [← hH, hyp]
  -- agent-wise descent
  have hA1 : ∑ i, f i ((y + d) i) ≤ ∑ i, f i (y i) + ⟪H, d⟫_ℝ + Lh Lf / 2 * ‖d‖ ^ 2 := by
    have hi : ∀ i, f i ((y + d) i) ≤ f i (y i) + ⟪H i, d i⟫_ℝ + Lh Lf / 2 * ‖d i‖ ^ 2 := by
      intro i
      have := Gradient.descent_lemma (dgd_hasGrad hA i) (hA.lipschitz i) (y i) ((y + d) i)
      have e : (y + d) i - y i = d i := by simp
      rw [e] at this
      have hHi : H i = gradient (f i) (y i) := by rw [hH]; rfl
      rw [hHi]
      have h2 : Lf i / 2 * ‖d i‖ ^ 2 ≤ Lh Lf / 2 * ‖d i‖ ^ 2 := by
        have := dgd_Lf_le_Lh Lf i
        gcongr
      linarith
    calc ∑ i, f i ((y + d) i) ≤ ∑ i, (f i (y i) + ⟪H i, d i⟫_ℝ + Lh Lf / 2 * ‖d i‖ ^ 2) :=
          Finset.sum_le_sum fun i _ => hi i
      _ = ∑ i, f i (y i) + ⟪H, d⟫_ℝ + Lh Lf / 2 * ‖d‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, PiLp.inner_apply,
            PiLp.norm_sq_eq_of_L2, ← Finset.mul_sum]
  -- quadratic part
  have hA2 : ‖y + d‖ ^ 2 - ⟪y + d, mix W (y + d)⟫_ℝ ≤
      (‖y‖ ^ 2 - ⟪y, mix W y⟫_ℝ) + 2 * ⟪u, d⟫_ℝ + (1 - lamN W) * ‖d‖ ^ 2 := by
    have h1 := norm_add_sq_real y d
    have h2 : ⟪y + d, mix W (y + d)⟫_ℝ = ⟪y, mix W y⟫_ℝ + 2 * ⟪mix W y, d⟫_ℝ + ⟪d, mix W d⟫_ℝ := by
      rw [dgd_mix_add, inner_add_left, inner_add_right, inner_add_right,
        ← dgd_mix_inner_symm hA.symm y d, real_inner_comm (mix W y) d]
      ring
    have h3 := dgd_mix_rayleigh_low (p := p) hh hn d
    have h4 : ⟪u, d⟫_ℝ = ⟪y, d⟫_ℝ - ⟪mix W y, d⟫_ℝ := by rw [hu, inner_sub_left]
    rw [h2, h1, h4]
    nlinarith
  have hid : α * ⟪H, d⟫_ℝ + ⟪u, d⟫_ℝ = -‖d‖ ^ 2 := by
    have : ⟪α • H + u, d⟫_ℝ = -‖d‖ ^ 2 := by
      rw [show α • H + u = -d by rw [hd']; simp, inner_neg_left, real_inner_self_eq_norm_sq]
    rw [inner_add_left, real_inner_smul_left] at this
    exact this
  unfold dgdXi
  have hc : 0 ≤ 1 / (2 * α) := by positivity
  have h5 := mul_le_mul_of_nonneg_left hA2 hc
  have e1 : α * (1 / (2 * α)) = 1 / 2 := by field_simp
  have hN : 0 ≤ ‖d‖ ^ 2 := by positivity
  have key : α * (⟪H, d⟫_ℝ + Lh Lf / 2 * ‖d‖ ^ 2 +
      1 / (2 * α) * (2 * ⟪u, d⟫_ℝ + (1 - lamN W) * ‖d‖ ^ 2)) ≤ 0 := by
    have : α * (⟪H, d⟫_ℝ + Lh Lf / 2 * ‖d‖ ^ 2 +
        1 / (2 * α) * (2 * ⟪u, d⟫_ℝ + (1 - lamN W) * ‖d‖ ^ 2)) =
        (α * Lh Lf - 1 - lamN W) / 2 * ‖d‖ ^ 2 := by
      have e2 : α * (1 / (2 * α) * (2 * ⟪u, d⟫_ℝ + (1 - lamN W) * ‖d‖ ^ 2)) =
          ⟪u, d⟫_ℝ + (1 - lamN W) / 2 * ‖d‖ ^ 2 := by
        field_simp
      calc _ = α * ⟪H, d⟫_ℝ + α * (Lh Lf / 2 * ‖d‖ ^ 2) +
          α * (1 / (2 * α) * (2 * ⟪u, d⟫_ℝ + (1 - lamN W) * ‖d‖ ^ 2)) := by ring
        _ = _ := by rw [e2]; linear_combination hid
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hN
  have key' : ⟪H, d⟫_ℝ + Lh Lf / 2 * ‖d‖ ^ 2 +
      1 / (2 * α) * (2 * ⟪u, d⟫_ℝ + (1 - lamN W) * ‖d‖ ^ 2) ≤ 0 := by
    by_contra hcon
    replace hcon := not_le.1 hcon
    have := mul_pos hα hcon
    linarith
  nlinarith [key', h5, hA1]

theorem dgd_succ {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → E p → ℝ) (α : ℝ) (k : ℕ) :
    dgd W f α (k + 1) = mix W (dgd W f α k) - α • dgdH f (dgd W f α k) := rfl

theorem dgd_zero {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → E p → ℝ) (α : ℝ) :
    dgd W f α 0 = 0 := rfl

theorem dgd_Xi_mono {n p : ℕ} {G : SimpleGraph (Fin n)} {W : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → E p → ℝ} {Lf : Fin n → ℝ} (hA : Assumption1 G W f Lf)
    {α : ℝ} (hα : 0 < α) (hα1 : α < (1 + lamN W) / Lh Lf) (k : ℕ) :
    dgdXi W f α (dgd W f α k) ≤ ∑ i, f i 0 := by
  induction k with
  | zero => rw [dgd_zero, dgd_Xi_zero]
  | succ k ih =>
    rw [dgd_succ]
    exact le_trans (dgd_lyap_step hA hα hα1 _) ih

theorem dgd_ds_rows {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} (hds : W ∈ doublyStochastic ℝ (Fin n)) :
    (∀ i j, 0 ≤ W i j) ∧ (∀ i, ∑ j, W i j = 1) ∧ (∀ j, ∑ i, W i j = 1) := by
  rw [mem_doublyStochastic] at hds
  obtain ⟨h0, h1, h2⟩ := hds
  refine ⟨h0, fun i => ?_, fun j => ?_⟩
  · have := congrFun h1 i
    simpa [Matrix.mulVec, dotProduct] using this
  · have := congrFun h2 j
    simpa [Matrix.vecMul, dotProduct] using this

theorem dgd_rayleigh_up {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hds : W ∈ doublyStochastic ℝ (Fin n)) (v : Fin n → ℝ) :
    ∑ i, v i * (W *ᵥ v) i ≤ ∑ i, v i ^ 2 := by
  obtain ⟨h0, hr, hc⟩ := dgd_ds_rows hds
  have h1 : ∑ i, v i * (W *ᵥ v) i = ∑ i, ∑ j, W i j * (v i * v j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ i, ∑ j, W i j * (v i * v j) ≤ ∑ i, ∑ j, W i j * ((v i ^ 2 + v j ^ 2) / 2) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (h0 i j)
    nlinarith [sq_nonneg (v i - v j)]
  have h3 : ∑ i, ∑ j, W i j * ((v i ^ 2 + v j ^ 2) / 2) = ∑ i, v i ^ 2 := by
    have e1 : ∑ i, ∑ j, W i j * (v i ^ 2 / 2) = ∑ i, v i ^ 2 / 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_mul, hr i, one_mul]
    have e2 : ∑ i, ∑ j, W i j * (v j ^ 2 / 2) = ∑ j, v j ^ 2 / 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_mul, hc j, one_mul]
    calc ∑ i, ∑ j, W i j * ((v i ^ 2 + v j ^ 2) / 2)
        = ∑ i, ∑ j, (W i j * (v i ^ 2 / 2) + W i j * (v j ^ 2 / 2)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i, v i ^ 2 / 2 + ∑ j, v j ^ 2 / 2 := by
          simp only [Finset.sum_add_distrib]; rw [e1, e2]
      _ = ∑ i, v i ^ 2 := by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  linarith

theorem dgd_mix_rayleigh_up {n p : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hds : W ∈ doublyStochastic ℝ (Fin n)) (d : Stack n p) : ⟪d, mix W d⟫_ℝ ≤ ‖d‖ ^ 2 := by
  rw [dgd_inner_mix_coord, dgd_norm_sq_coord]
  refine Finset.sum_le_sum fun c _ => ?_
  have := dgd_rayleigh_up hds (fun j => d j c)
  simpa using this

theorem dgd_sum_le {n p : ℕ} {G : SimpleGraph (Fin n)} {W : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → E p → ℝ} {Lf : Fin n → ℝ} (hA : Assumption1 G W f Lf)
    {α : ℝ} (hα : 0 < α) (hα1 : α < (1 + lamN W) / Lh Lf) (k : ℕ) :
    ∑ i, f i (dgd W f α k i) ≤ ∑ i, f i 0 := by
  refine le_trans ?_ (dgd_Xi_mono hA hα hα1 k)
  unfold dgdXi
  have h := dgd_mix_rayleigh_up (p := p) hA.doublyStochastic (dgd W f α k)
  have hc : 0 ≤ 1 / (2 * α) := by positivity
  have : 0 ≤ (1 / (2 * α)) * (‖dgd W f α k‖ ^ 2 - ⟪dgd W f α k, mix W (dgd W f α k)⟫_ℝ) :=
    mul_nonneg hc (by linarith)
  linarith

theorem dgd_H_bound {n p : ℕ} {G : SimpleGraph (Fin n)} {W : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → E p → ℝ} {Lf : Fin n → ℝ} (hA : Assumption1 G W f Lf)
    {α : ℝ} (hα : 0 < α) (hα1 : α < (1 + lamN W) / Lh Lf) (k : ℕ) :
    ‖dgdH f (dgd W f α k)‖ ≤ D f Lf := by
  set y := dgd W f α k with hy
  have hsum := dgd_sum_le hA hα hα1 k
  have hfo : ∀ i z, fo f i ≤ f i z := fun i z => ciInf_le (hA.bddBelow i) z
  have hLh := dgd_Lh_pos hA
  have hi : ∀ i, ‖gradient (f i) (y i)‖ ^ 2 ≤ 2 * Lh Lf * (f i (y i) - fo f i) := by
    intro i
    have := dgd_gradsq (hA.Lf_pos i) (fun x z => Gradient.descent_lemma (dgd_hasGrad hA i) (hA.lipschitz i) x z)
      (hfo i) (y i)
    have h2 : 2 * Lf i * (f i (y i) - fo f i) ≤ 2 * Lh Lf * (f i (y i) - fo f i) := by
      have := dgd_Lf_le_Lh Lf i
      have h0 : 0 ≤ f i (y i) - fo f i := sub_nonneg.2 (hfo i _)
      nlinarith
    linarith
  have hnorm : ‖dgdH f y‖ ^ 2 = ∑ i, ‖gradient (f i) (y i)‖ ^ 2 := by
    rw [dgdH, PiLp.norm_sq_eq_of_L2]
  have hD : D f Lf = Real.sqrt (2 * Lh Lf * ∑ i, (f i 0 - fo f i)) := rfl
  have hle : ‖dgdH f y‖ ^ 2 ≤ 2 * Lh Lf * ∑ i, (f i 0 - fo f i) := by
    rw [hnorm]
    calc ∑ i, ‖gradient (f i) (y i)‖ ^ 2 ≤ ∑ i, 2 * Lh Lf * (f i (y i) - fo f i) :=
          Finset.sum_le_sum fun i _ => hi i
      _ = 2 * Lh Lf * (∑ i, f i (y i) - ∑ i, fo f i) := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      _ ≤ 2 * Lh Lf * ∑ i, (f i 0 - fo f i) := by
          rw [Finset.sum_sub_distrib]
          gcongr
  rw [hD]
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt hle)

theorem dgd_inner_scale {n p : ℕ} (f : Fin n → E p → ℝ) (c : ℝ) (a b : E p)
    (h : c * ‖a - b‖ ^ 2 ≤ ⟪gradSum f a - gradSum f b, a - b⟫_ℝ) :
    c / (n : ℝ) * ‖a - b‖ ^ 2 ≤
      ⟪(1 / (n : ℝ)) • gradSum f a - (1 / (n : ℝ)) • gradSum f b, a - b⟫_ℝ := by
  rw [← smul_sub, real_inner_smul_left]
  have hn : (0:ℝ) ≤ 1 / (n : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left h hn
  calc c / (n : ℝ) * ‖a - b‖ ^ 2 = 1 / (n : ℝ) * (c * ‖a - b‖ ^ 2) := by ring
    _ ≤ _ := this

theorem dgd_c2_small {n p : ℕ} {G : SimpleGraph (Fin n)} {W : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → E p → ℝ} {Lf : Fin n → ℝ} (hA : Assumption1 G W f Lf) {α : ℝ} (hα : 0 < α)
    {c1 c2 : ℝ} (hc : Lemma3Consts f Lf c1 c2) (hα2 : α < c1) :
    α * c2 ≤ 1 / 4 ∨ ∀ x xs : E p, IsProj (Xstar f) x xs → x = xs := by
  have hn : (0:ℝ) < n := by have := hA.two_le; exact_mod_cast (by omega : 0 < n)
  have hL := dgd_Lbar_pos hA
  rcases hc with ⟨μ, ⟨hμ0, hμ⟩, hc1, hc2⟩ | ⟨ν, θ, ⟨hν0, hν⟩, hθ, hc1, hc2⟩
  · left
    have hm0 : 0 < μ / (n : ℝ) := by positivity
    have hα3 : α * (μ / (n : ℝ) + Lbar Lf) ≤ 1 := by
      rw [hc1, lt_div_iff₀ (by positivity)] at hα2; linarith
    rw [hc2]
    set m := μ / (n : ℝ)
    set l := Lbar Lf
    have hml : 0 < m + l := by linarith
    rw [← mul_div_assoc, div_le_iff₀ hml]
    nlinarith [sq_nonneg (m - l), mul_pos hm0 hL]
  · by_cases hνL : ν / (n : ℝ) ≤ Lbar Lf
    · left
      have hθ' : α * Lbar Lf ≤ θ := by
        rw [hc1, lt_div_iff₀ hL] at hα2; linarith
      rw [hc2]
      have h1 : α * ((1 - θ) * (ν / (n : ℝ))) ≤ α * ((1 - θ) * Lbar Lf) := by
        gcongr
        linarith [hθ.2]
      nlinarith [sq_nonneg (θ - 1 / 2), hθ.1, hθ.2, mul_le_mul_of_nonneg_left hθ' (by linarith [hθ.2] : (0:ℝ) ≤ 1 - θ)]
    · right
      intro x xs hx
      by_contra hne
      have hxs0 := dgd_Gbar_zero hx.1 hA
      have h1 := dgd_inner_scale f ν x xs (hν x xs hx)
      have h2 := dgd_Gbar_lip hA x xs
      have h3 := real_inner_le_norm (((1 / (n : ℝ)) • gradSum f x - (1 / (n : ℝ)) • gradSum f xs)) (x - xs)
      have h4 : ‖(1 / (n : ℝ)) • gradSum f x - (1 / (n : ℝ)) • gradSum f xs‖ * ‖x - xs‖ ≤
          Lbar Lf * ‖x - xs‖ * ‖x - xs‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      have hpos : 0 < ‖x - xs‖ ^ 2 := by
        have : x - xs ≠ 0 := sub_ne_zero.2 hne
        positivity
      have := mul_pos (by linarith [not_le.1 hνL] : 0 < ν / (n : ℝ) - Lbar Lf) hpos
      nlinarith

theorem dgd_center_sum {n p : ℕ} (hn : n ≠ 0) (y : Stack n p) :
    ∑ i, (y i - (1 / (n : ℝ)) • ∑ j, y j) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_one_div_cancel hn', one_smul, sub_self]

theorem dgd_centered {n p : ℕ} (hn : 0 < n) (h : Fin n → E p) :
    ∑ i, ‖h i - (1 / (n : ℝ)) • ∑ j, h j‖ ^ 2 ≤ ∑ i, ‖h i‖ ^ 2 := by
  obtain ⟨g, hg⟩ : ∃ g, g = (1 / (n : ℝ)) • ∑ j, h j := ⟨_, rfl⟩
  rw [← hg]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hS : ∑ j, h j = (n : ℝ) • g := by
    rw [hg, smul_smul, mul_one_div_cancel hn', one_smul]
  have h1 : ∀ i, ‖h i - g‖ ^ 2 = ‖h i‖ ^ 2 - 2 * ⟪h i, g⟫_ℝ + ‖g‖ ^ 2 := fun i => norm_sub_sq_real _ _
  simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h2 : ∑ i, ⟪h i, g⟫_ℝ = (n : ℝ) * ‖g‖ ^ 2 := by
    rw [← sum_inner, hS, real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [h2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : 0 ≤ (n : ℝ) * ‖g‖ ^ 2 := by positivity
  linarith

theorem dgd_cocoercive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} {G : E → E} {K : ℝ} (hK : 0 < K)
    (hup : ∀ x y, F y ≤ F x + ⟪G x, y - x⟫ + K / 2 * ‖y - x‖ ^ 2)
    (hlo : ∀ x y, F x + ⟪G x, y - x⟫ ≤ F y) (x y : E) :
    ‖G y - G x‖ ^ 2 ≤ 2 * K * (F y - F x - ⟪G x, y - x⟫) := by
  set v := G y - G x with hv
  have h1 := hlo x (y - (1 / K) • v)
  have h2 := hup y (y - (1 / K) • v)
  have e1 : y - (1 / K) • v - y = -((1 / K) • v) := by abel
  have e2 : y - (1 / K) • v - x = (y - x) - (1 / K) • v := by abel
  rw [e1] at h2
  rw [e2] at h1
  rw [inner_sub_right, real_inner_smul_right] at h1
  rw [inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / K)] at h2
  have h3 : ⟪G y, v⟫ - ⟪G x, v⟫ = ‖v‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have hK' : K ≠ 0 := hK.ne'
  have h4 : 1 / K * ⟪G y, v⟫ - 1 / K * ⟪G x, v⟫ = 1 / K * ‖v‖ ^ 2 := by
    rw [← mul_sub, h3]
  have h5 : K / 2 * (1 / K * ‖v‖) ^ 2 = 1 / (2 * K) * ‖v‖ ^ 2 := by
    field_simp
  have key : F x + ⟪G x, y - x⟫ - F y ≤ -(1 / (2 * K)) * ‖v‖ ^ 2 := by
    have h6 : 1 / K * ‖v‖ ^ 2 = 2 * (1 / (2 * K) * ‖v‖ ^ 2) := by field_simp
    nlinarith
  have h7 : 2 * K * (1 / (2 * K) * ‖v‖ ^ 2) = ‖v‖ ^ 2 := by field_simp
  nlinarith

theorem dgd_cocoercive_crit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} {G : E → E} {L : ℝ} (hL : 0 < L)
    (hup : ∀ x y, F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (hlo : ∀ x y, F x + ⟪G x, y - x⟫ ≤ F y) (xs : E) (hxs : G xs = 0) (x : E) :
    ‖G x‖ ^ 2 ≤ L * ⟪G x, x - xs⟫ := by
  have c1 := dgd_cocoercive hL hup hlo xs x
  have c2 := dgd_cocoercive hL hup hlo x xs
  rw [hxs] at c1 c2
  simp only [sub_zero, zero_sub, norm_neg, inner_zero_left, sub_zero] at c1 c2
  have e : ⟪G x, xs - x⟫ = -⟪G x, x - xs⟫ := by
    rw [← inner_neg_right]; congr 1; abel
  rw [e] at c2
  nlinarith

theorem dgd_cocoercive_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} {G : E → E} {K : ℝ} (hK : 0 < K)
    (hup : ∀ x y, F y ≤ F x + ⟪G x, y - x⟫ + K / 2 * ‖y - x‖ ^ 2)
    (hlo : ∀ x y, F x + ⟪G x, y - x⟫ ≤ F y) (x y : E) :
    ‖G x - G y‖ ^ 2 ≤ K * ⟪G x - G y, x - y⟫ := by
  have c1 := dgd_cocoercive hK hup hlo y x
  have c2 := dgd_cocoercive hK hup hlo x y
  rw [norm_sub_rev] at c2
  have e : ⟪G x, y - x⟫ = -⟪G x, x - y⟫ := by
    rw [← inner_neg_right]; congr 1; abel
  rw [inner_sub_left]
  rw [e] at c2
  nlinarith

theorem dgd_normsq {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} (hh : W.IsHermitian) (v : Fin n → ℝ) :
    ∑ i, ((W *ᵥ v) i) ^ 2 =
      ∑ j, hh.eigenvalues j ^ 2 * (∑ i, (hh.eigenvectorBasis j) i * v i) ^ 2 := by
  have := dgd_parseval2 hh (W *ᵥ v) (W *ᵥ v)
  calc ∑ i, ((W *ᵥ v) i) ^ 2 = ∑ i, (W *ᵥ v) i * (W *ᵥ v) i := by simp [sq]
    _ = _ := this.symm
    _ = _ := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dgd_spec_coeff hh v j]; ring

theorem dgd_top_eig {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} (hh : W.IsHermitian) (hn : 2 ≤ n) :
    ∃ j0 : Fin n, ∀ j, j ≠ j0 → hh.eigenvalues j ≤ lam2 W := by
  have h : lam2 W = hh.eigenvalues₀ ⟨1, by rw [Fintype.card_fin]; omega⟩ := by
    unfold lam2; rw [dif_pos ⟨hh, hn⟩]
  have hpos : 0 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  refine ⟨(dgdE n) ⟨0, hpos⟩, fun j hj => ?_⟩
  rw [h]
  show hh.eigenvalues₀ _ ≤ _
  refine hh.eigenvalues₀_antitone ?_
  rw [Fin.le_def]
  have hne : (dgdE n).symm j ≠ ⟨0, hpos⟩ := by
    intro heq
    apply hj
    rw [← heq]; simp
  have : ((dgdE n).symm j).val ≠ 0 := by
    intro h0; apply hne; exact Fin.ext h0
  show 1 ≤ ((dgdE n).symm j).val
  omega

theorem dgd_contract_mean {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} (hh : W.IsHermitian)
    (hn : 2 ≤ n) (hone : W *ᵥ (fun _ => (1:ℝ)) = fun _ => 1) (hb : beta W < 1)
    (v : Fin n → ℝ) (hv : ∑ i, v i = 0) :
    ∑ i, ((W *ᵥ v) i) ^ 2 ≤ beta W ^ 2 * ∑ i, v i ^ 2 := by
  obtain ⟨j0, hj0⟩ := dgd_top_eig hh hn
  have hβ : ∀ j, j ≠ j0 → |hh.eigenvalues j| ≤ beta W := by
    intro j hj
    have h1 := hj0 j hj
    have h2 := dgd_lamN_le hh hn j
    have h3 : lam2 W ≤ beta W := le_trans (le_abs_self _) (le_max_left _ _)
    have h4 : -(beta W) ≤ lamN W := by
      have : -|lamN W| ≤ lamN W := neg_abs_le _
      have h5 : |lamN W| ≤ beta W := le_max_right _ _
      linarith
    rw [abs_le]; constructor <;> linarith
  have hd0 : ∀ j, j ≠ j0 → ∑ i, (hh.eigenvectorBasis j) i * (fun _ => (1:ℝ)) i = 0 := by
    intro j hj
    have h := dgd_spec_coeff hh (fun _ => (1:ℝ)) j
    rw [hone] at h
    have hlt : hh.eigenvalues j < 1 := lt_of_le_of_lt (le_trans (le_abs_self _) (hβ j hj)) hb
    have : (1 - hh.eigenvalues j) * ∑ i, (hh.eigenvectorBasis j) i * (fun _ => (1:ℝ)) i = 0 := by
      linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact h1
  have hsum1 := dgd_parseval2 hh v (fun _ => (1:ℝ))
  have hsum2 := dgd_parseval2 hh (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
  rw [Finset.sum_eq_single j0 (fun j _ hj => by rw [hd0 j hj, mul_zero]) (by simp)] at hsum1 hsum2
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hd2 : (∑ i, (hh.eigenvectorBasis j0) i * (fun _ => (1:ℝ)) i) ≠ 0 := by
    intro h0
    rw [h0] at hsum2
    have h1 : (∑ i : Fin n, (1:ℝ) * 1) = n := by simp
    rw [h1] at hsum2
    linarith
  have hc0 : ∑ i, (hh.eigenvectorBasis j0) i * v i = 0 := by
    simp only [mul_one, hv] at hsum1
    have : (∑ i, (hh.eigenvectorBasis j0) i * v i) * (∑ i, (hh.eigenvectorBasis j0) i) = 0 := by
      simpa using hsum1
    rcases mul_eq_zero.1 this with h1 | h1
    · exact h1
    · exfalso; apply hd2; simpa using h1
  rw [dgd_normsq hh v]
  have hp := dgd_parseval2 hh v v
  have h3 : ∑ i, v i ^ 2 = ∑ j, (∑ i, (hh.eigenvectorBasis j) i * v i) ^ 2 := by
    rw [show ∑ i, v i ^ 2 = ∑ i, v i * v i by simp [sq], ← hp]
    simp [sq]
  rw [h3, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j = j0
  · subst hj; rw [hc0]; simp
  · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact sq_le_sq' (by linarith [abs_le.1 (hβ j hj)]) (by linarith [abs_le.1 (hβ j hj)])

theorem dgd_mix_contract_sq {n p : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} (hh : W.IsHermitian)
    (hn : 2 ≤ n) (hone : W *ᵥ (fun _ => (1:ℝ)) = fun _ => 1) (hb : beta W < 1)
    (y : Stack n p) (hy : ∑ i, y i = 0) : ‖mix W y‖ ^ 2 ≤ beta W ^ 2 * ‖y‖ ^ 2 := by
  rw [dgd_norm_sq_coord, dgd_norm_sq_coord, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  have hv : ∑ j, y j c = 0 := by
    have := congrArg (fun z : E p => z c) hy
    simpa using this
  have := dgd_contract_mean hh hn hone hb (fun j => y j c) hv
  simpa [dgd_mix_coord, Matrix.mulVec, dotProduct] using this

theorem dgd_mix_const {n p : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hds : W ∈ doublyStochastic ℝ (Fin n)) (v : E p) :
    mix W (WithLp.toLp 2 (fun _ : Fin n => v) : Stack n p) = WithLp.toLp 2 (fun _ : Fin n => v) := by
  obtain ⟨h0, hr, hc⟩ := dgd_ds_rows hds
  ext i c
  rw [dgd_mix_coord]
  show ∑ j, W i j * v c = v c
  rw [← Finset.sum_mul, hr i, one_mul]

theorem dgd_mix_dgdC {n p : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hds : W ∈ doublyStochastic ℝ (Fin n)) (v : E p) : mix W (dgdC v : Stack n p) = dgdC v :=
  dgd_mix_const hds v

theorem dgd_mix_sub {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (x y : Stack n p) :
    mix W (x - y) = mix W x - mix W y := by
  ext i c
  simp [dgd_mix_coord, mul_sub, Finset.sum_sub_distrib]

theorem dgd_mix_sum {n p : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hds : W ∈ doublyStochastic ℝ (Fin n)) (x : Stack n p) :
    ∑ i, (mix W x) i = ∑ i, x i := by
  obtain ⟨h0, hr, hc⟩ := dgd_ds_rows hds
  ext c
  simp only [WithLp.ofLp_sum, Finset.sum_apply, dgd_mix_coord]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul, hc j, one_mul]

theorem dgd_xbar_succ {n p : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hds : W ∈ doublyStochastic ℝ (Fin n)) (f : Fin n → E p → ℝ) (α : ℝ) (k : ℕ) :
    xbar (dgd W f α) (k + 1) = xbar (dgd W f α) k - α • gk f (dgd W f α) k := by
  unfold xbar gk
  rw [dgd_succ]
  have h : ∑ i, (mix W (dgd W f α k) - α • dgdH f (dgd W f α k)) i =
      ∑ i, dgd W f α k i - α • ∑ i, gradient (f i) (dgd W f α k i) := by
    rw [← dgd_mix_sum hds (dgd W f α k)]
    simp [Finset.sum_sub_distrib, Finset.smul_sum, dgdH]
  rw [h, smul_sub, smul_comm α]

theorem dgd_cons {n p : ℕ} {G : SimpleGraph (Fin n)} {W : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → E p → ℝ} {Lf : Fin n → ℝ} (hA : Assumption1 G W f Lf)
    {α : ℝ} (hα : 0 < α) (hα1 : α < (1 + lamN W) / Lh Lf) (k : ℕ) :
    ‖dgd W f α k - dgdC (xbar (dgd W f α) k)‖ ≤ α * D f Lf / (1 - beta W) := by
  have hn := hA.two_le
  have hβ1 := hA.beta_lt_one
  have hβ0 : 0 ≤ beta W := le_trans (abs_nonneg _) (le_max_left _ _)
  have hD0 : 0 ≤ D f Lf := Real.sqrt_nonneg _
  have hpos : 0 < 1 - beta W := by linarith
  have hh := dgd_herm hA.symm
  have hone : W *ᵥ (fun _ => (1:ℝ)) = fun _ => 1 := by
    obtain ⟨_, hr, _⟩ := dgd_ds_rows hA.doublyStochastic
    ext i; simpa [Matrix.mulVec, dotProduct] using hr i
  induction k with
  | zero =>
    have : dgd W f α 0 - dgdC (xbar (dgd W f α) 0) = 0 := by
      ext i c; simp [dgd_zero, xbar, dgdC]
    rw [this, norm_zero]; positivity
  | succ k ih =>
    obtain ⟨z, hz⟩ : ∃ z, z = dgd W f α k - dgdC (xbar (dgd W f α) k) := ⟨_, rfl⟩
    rw [← hz] at ih
    have hz0 : ∑ i, z i = 0 := by
      have := dgd_center_sum (p := p) (by omega : n ≠ 0) (dgd W f α k)
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hz]; rfl
    have hzs : dgd W f α (k + 1) - dgdC (xbar (dgd W f α) (k + 1)) =
        mix W z - α • (dgdH f (dgd W f α k) - dgdC (gk f (dgd W f α) k)) := by
      rw [dgd_succ, dgd_xbar_succ hA.doublyStochastic, dgd_C_sub_smul, hz, dgd_mix_sub,
        dgd_mix_dgdC hA.doublyStochastic]
      module
    have hmix : ‖mix W z‖ ≤ beta W * ‖z‖ := by
      have := dgd_mix_contract_sq hh hn hone hA.beta_lt_one z hz0
      refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
      rw [mul_pow]; exact this
    have hcent : ‖dgdH f (dgd W f α k) - dgdC (gk f (dgd W f α) k)‖ ≤ D f Lf := by
      refine le_trans ?_ (dgd_H_bound hA hα hα1 k)
      refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      have := dgd_centered (p := p) (by omega : 0 < n)
        (fun i => gradient (f i) (dgd W f α k i))
      simpa [dgdH, dgdC, gk] using this
    rw [hzs]
    calc ‖mix W z - α • (dgdH f (dgd W f α k) - dgdC (gk f (dgd W f α) k))‖
        ≤ ‖mix W z‖ + ‖α • (dgdH f (dgd W f α k) - dgdC (gk f (dgd W f α) k))‖ := norm_sub_le _ _
      _ ≤ beta W * (α * D f Lf / (1 - beta W)) + α * D f Lf := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα]
          have h1 : beta W * ‖z‖ ≤ beta W * (α * D f Lf / (1 - beta W)) :=
            mul_le_mul_of_nonneg_left ih hβ0
          have h2 : α * ‖dgdH f (dgd W f α k) - dgdC (gk f (dgd W f α) k)‖ ≤ α * D f Lf :=
            mul_le_mul_of_nonneg_left hcent hα.le
          linarith
      _ = α * D f Lf / (1 - beta W) := by field_simp; ring

theorem dgd_contract_A {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} {G : E → E} {L μ t : ℝ} (hμ : 0 < μ) (hμL : μ < L) (ht : 0 < t)
    (htL : t * (μ + L) ≤ 1)
    (hup : ∀ x y, F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (hlo : ∀ x y, F x + ⟪G x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ F y)
    (xs : E) (hxs : G xs = 0) (x : E) :
    ‖(x - xs) - t • G x‖ ^ 2 ≤ (1 - 2 * t * (μ * L / (μ + L))) * ‖x - xs‖ ^ 2 := by
  -- the shifted function φ z = F z - μ/2 ‖z‖², gradient G z - μ z
  have hK : 0 < L - μ := by linarith
  have hid : ∀ x y : E, ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y - x⟫ + ‖y - x‖ ^ 2 := by
    intro x y
    have := norm_add_sq_real x (y - x)
    rw [add_sub_cancel] at this
    exact this
  have hup' : ∀ x y : E, (fun z => F z - μ / 2 * ‖z‖ ^ 2) y ≤
      (fun z => F z - μ / 2 * ‖z‖ ^ 2) x + ⟪(fun z => G z - μ • z) x, y - x⟫
        + (L - μ) / 2 * ‖y - x‖ ^ 2 := by
    intro x y
    have h := hup x y
    have h2 := hid x y
    simp only [inner_sub_left, real_inner_smul_left]
    nlinarith
  have hlo' : ∀ x y : E, (fun z => F z - μ / 2 * ‖z‖ ^ 2) x +
      ⟪(fun z => G z - μ • z) x, y - x⟫ ≤ (fun z => F z - μ / 2 * ‖z‖ ^ 2) y := by
    intro x y
    have h := hlo x y
    have h2 := hid x y
    simp only [inner_sub_left, real_inner_smul_left]
    nlinarith
  have hp := dgd_cocoercive_pair hK hup' hlo' x xs
  have hw : (G x - μ • x) - (G xs - μ • xs) = G x - μ • (x - xs) := by
    rw [hxs]; simp only [smul_sub, zero_sub]; abel
  rw [hw] at hp
  have hexp : ‖(x - xs) - t • G x‖ ^ 2 =
      ‖x - xs‖ ^ 2 - 2 * t * ⟪G x, x - xs⟫ + t ^ 2 * ‖G x‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_comm]
    ring
  rw [hexp]
  rw [norm_sub_sq_real, inner_sub_left, real_inner_smul_left, real_inner_smul_right,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_self_eq_norm_sq] at hp
  set P := ⟪G x, x - xs⟫
  set Q := ‖G x‖ ^ 2
  set R := ‖x - xs‖ ^ 2
  have hR : 0 ≤ R := by positivity
  have hQ : 0 ≤ Q := by positivity
  have hm : 0 < μ + L := by linarith
  set c2 := μ * L / (μ + L) with hc2
  have hc2m : c2 * (μ + L) = μ * L := by rw [hc2]; field_simp
  have hineq : Q ≤ (μ + L) * P - μ * L * R := by nlinarith
  have hPc : c2 * R ≤ P := by
    have : (μ + L) * (c2 * R) ≤ (μ + L) * P := by nlinarith
    exact le_of_mul_le_mul_left this hm
  have hs : 0 ≤ t * (2 - t * (μ + L)) := mul_nonneg ht.le (by linarith)
  have hineq' : Q ≤ (μ + L) * P - c2 * (μ + L) * R := by rw [hc2m]; exact hineq
  have h1 := mul_le_mul_of_nonneg_left hineq' (sq_nonneg t)
  have h2 := mul_nonneg hs (sub_nonneg.2 hPc)
  nlinarith [h1, h2]

theorem dgd_contract_B {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} {G : E → E} {L ν t θ : ℝ} (hL : 0 < L) (ht : 0 < t) (hθ1 : θ ≤ 1)
    (htL : t * L ≤ θ) (hν : 0 < ν)
    (hup : ∀ x y, F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (hlo : ∀ x y, F x + ⟪G x, y - x⟫ ≤ F y) (xs : E) (hxs : G xs = 0) (x : E)
    (hrsc : ν * ‖x - xs‖ ^ 2 ≤ ⟪G x - G xs, x - xs⟫) :
    ‖(x - xs) - t • G x‖ ^ 2 ≤ (1 - t * (1 - θ) * ν) * ‖x - xs‖ ^ 2 := by
  have hc := dgd_cocoercive_crit hL hup hlo xs hxs x
  rw [hxs, sub_zero] at hrsc
  have hexp : ‖(x - xs) - t • G x‖ ^ 2 =
      ‖x - xs‖ ^ 2 - 2 * t * ⟪G x, x - xs⟫ + t ^ 2 * ‖G x‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_comm]
    ring
  rw [hexp]
  set P := ⟪G x, x - xs⟫
  set Q := ‖G x‖ ^ 2
  set R := ‖x - xs‖ ^ 2
  have hR : 0 ≤ R := by positivity
  have hP : ν * R ≤ P := hrsc
  have hP0 : 0 ≤ P := le_trans (by positivity) hP
  have h1 : t ^ 2 * Q ≤ t * θ * P := by
    calc t ^ 2 * Q ≤ t ^ 2 * (L * P) := by gcongr
      _ = t * (t * L) * P := by ring
      _ ≤ t * θ * P := by gcongr
  have h2 : (1 - t * (1 - θ) * ν) * R ≥ R - t * (2 - θ) * P := by
    nlinarith [mul_nonneg ht.le (mul_nonneg hR hν.le), mul_nonneg ht.le hP0,
      mul_nonneg ht.le (sub_nonneg.2 hP), sub_nonneg.2 hθ1]
  nlinarith

theorem dgd_fbar_conv {n p : ℕ} {G : SimpleGraph (Fin n)} {W : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → E p → ℝ} {Lf : Fin n → ℝ} (hA : Assumption1 G W f Lf) (x y : E p) :
    fbar f x + ⟪(1 / (n : ℝ)) • gradSum f x, y - x⟫ ≤ fbar f y := by
  have hi : ∀ i, f i x + ⟪gradient (f i) x, y - x⟫ ≤ f i y := fun i =>
    Gradient.convex_first_order (dgd_hasGrad hA i) (hA.convex i) x y
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  rw [Finset.sum_add_distrib, ← sum_inner] at hs
  have hn : (0:ℝ) ≤ 1 / (n : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hs hn
  unfold fbar
  rw [real_inner_smul_left]
  simp only [gradSum] at *
  linarith

theorem dgd_lower_sc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {μ : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hm : ∀ a b, μ * ‖a - b‖ ^ 2 ≤ ⟪G a - G b, a - b⟫) (x y : E) :
    F x + ⟪G x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ F y := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * ⟪G x, w⟫ - μ / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪G (x + t • w), w⟫ - ⟪G x, w⟫
      - μ / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := Gradient.hasDerivAt_line hF x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪G x, w⟫) ⟪G x, w⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪G x, w⟫
    have h3 : HasDerivAt (fun s : ℝ => μ / 2 * s ^ 2 * ‖w‖ ^ 2) (μ / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (μ / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hge : 0 ≤ ⟪G (x + c • w), w⟫ - ⟪G x, w⟫ - μ / 2 * (2 * c) * ‖w‖ ^ 2 := by
    have e1 : ⟪G (x + c • w), w⟫ - ⟪G x, w⟫ = ⟪G (x + c • w) - G x, w⟫ := by
      rw [inner_sub_left]
    have e3 : μ * ‖c • w‖ ^ 2 ≤ ⟪G (x + c • w) - G x, c • w⟫ := by
      have := hm (x + c • w) x
      rwa [add_sub_cancel_left] at this
    rw [norm_smul, real_inner_smul_right, Real.norm_eq_abs, abs_of_pos hc.1] at e3
    have h6 : μ * c * ‖w‖ ^ 2 ≤ ⟪G (x + c • w) - G x, w⟫ := by
      refine le_of_mul_le_mul_left ?_ hc.1
      nlinarith [e3]
    rw [e1]
    nlinarith
  rw [hcd] at hge
  have : g 0 ≤ g 1 := by
    have := hge; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

theorem dgd_contraction {n p : ℕ} {G : SimpleGraph (Fin n)} {W : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → E p → ℝ} {Lf : Fin n → ℝ} (hA : Assumption1 G W f Lf) {α : ℝ} (hα : 0 < α)
    {c1 c2 : ℝ} (hc : Lemma3Consts f Lf c1 c2) (hα2 : α < c1) {x xs : E p}
    (hx : IsProj (Xstar f) x xs) :
    ‖(x - xs) - α • ((1 / (n : ℝ)) • gradSum f x)‖ ^ 2 ≤ (1 - α * c2) * ‖x - xs‖ ^ 2 := by
  have hn : (0:ℝ) < n := by have := hA.two_le; exact_mod_cast (by omega : 0 < n)
  have hL := dgd_Lbar_pos hA
  have hxs0 := dgd_Gbar_zero hx.1 hA
  have hR : 0 ≤ ‖x - xs‖ ^ 2 := by positivity
  rcases hc with ⟨μ, ⟨hμ0, hμ⟩, hc1, hc2⟩ | ⟨ν, θ, ⟨hν0, hν⟩, hθ, hc1, hc2⟩
  · have hm0 : 0 < μ / (n : ℝ) := by positivity
    have hmon : ∀ a b : E p, μ / (n : ℝ) * ‖a - b‖ ^ 2 ≤
        ⟪(1 / (n : ℝ)) • gradSum f a - (1 / (n : ℝ)) • gradSum f b, a - b⟫_ℝ :=
      fun a b => dgd_inner_scale f μ a b (hμ a b)
    have hα3 : α * (μ / (n : ℝ) + Lbar Lf) < 1 := by
      rw [hc1, lt_div_iff₀ (by positivity)] at hα2; linarith
    by_cases hmL : μ / (n : ℝ) ≤ Lbar Lf
    · have hL' : Lbar Lf < 1 / α - μ / (n : ℝ) := by
        have : Lbar Lf + μ / (n : ℝ) < 1 / α := by
          rw [lt_div_iff₀ hα]; linarith
        linarith
      have hA' := dgd_contract_A (F := fbar f) (G := fun z => (1 / (n : ℝ)) • gradSum f z)
        (L := 1 / α - μ / (n : ℝ)) (μ := μ / (n : ℝ)) (t := α) hm0 (by linarith) hα
        (by have : α * (μ / (n : ℝ) + (1 / α - μ / (n : ℝ))) = 1 := by field_simp; ring
            linarith)
        (fun x y => by
          have := dgd_Gbar_up hA x y
          have h2 : Lbar Lf / 2 * ‖y - x‖ ^ 2 ≤ (1 / α - μ / (n : ℝ)) / 2 * ‖y - x‖ ^ 2 := by
            gcongr
          linarith)
        (fun x y => dgd_lower_sc (F := fbar f) (G := fun z => (1 / (n : ℝ)) • gradSum f z)
          (dgd_fbar_grad hA) hmon x y)
        xs hxs0 x
      refine le_trans hA' ?_
      refine mul_le_mul_of_nonneg_right ?_ hR
      have hc2le : c2 ≤ μ / (n : ℝ) * (1 / α - μ / (n : ℝ)) /
          (μ / (n : ℝ) + (1 / α - μ / (n : ℝ))) := by
        rw [hc2, div_le_div_iff₀ (by positivity) (by linarith)]
        nlinarith [mul_pos hm0 hm0]
      have hu : 0 ≤ μ / (n : ℝ) * (1 / α - μ / (n : ℝ)) /
          (μ / (n : ℝ) + (1 / α - μ / (n : ℝ))) := by
        apply div_nonneg
        · exact mul_nonneg hm0.le (by linarith)
        · linarith
      nlinarith
    · have hall : ∀ a b : E p, a = b := by
        intro a b
        have h1 := hmon a b
        have h2 := dgd_Gbar_lip hA a b
        have h3 := real_inner_le_norm (((1 / (n : ℝ)) • gradSum f a - (1 / (n : ℝ)) • gradSum f b)) (a - b)
        have h4 : ‖(1 / (n : ℝ)) • gradSum f a - (1 / (n : ℝ)) • gradSum f b‖ * ‖a - b‖ ≤
            Lbar Lf * ‖a - b‖ * ‖a - b‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        have h5 : (μ / (n : ℝ) - Lbar Lf) * ‖a - b‖ ^ 2 ≤ 0 := by nlinarith
        have h6 : ‖a - b‖ ^ 2 ≤ 0 := by
          by_contra hcon
          have := mul_pos (by linarith : 0 < μ / (n : ℝ) - Lbar Lf) (not_le.1 hcon)
          linarith
        have : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
        exact sub_eq_zero.1 (norm_eq_zero.1 this)
      have hxe : x = xs := hall x xs
      subst hxe
      rw [hxs0]; simp
  · have hν1 : 0 < ν / (n : ℝ) := by positivity
    have hθ' : α * Lbar Lf ≤ θ := by
      rw [hc1, lt_div_iff₀ hL] at hα2; linarith
    have := dgd_contract_B (F := fbar f) (G := fun z => (1 / (n : ℝ)) • gradSum f z)
      (L := Lbar Lf) (ν := ν / (n : ℝ)) (t := α) (θ := θ) hL hα hθ.2 hθ' hν1
      (fun x y => dgd_Gbar_up hA x y) (fun x y => dgd_fbar_conv hA x y) xs hxs0 x
      (by have := dgd_inner_scale f ν x xs (hν x xs hx)
          simpa [hxs0] using this)
    rw [hc2]
    calc _ ≤ _ := this
      _ = _ := by ring

theorem dgd_mean_err {n p : ℕ} {G : SimpleGraph (Fin n)} {W : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → E p → ℝ} {Lf : Fin n → ℝ} (hA : Assumption1 G W f Lf) (y : Stack n p) (m : E p) :
    ‖(1 / (n : ℝ)) • ∑ i, gradient (f i) (y i) - (1 / (n : ℝ)) • ∑ i, gradient (f i) m‖ ≤
      Lh Lf * ‖y - dgdC m‖ := by
  have hn : (0:ℝ) < n := by have := hA.two_le; exact_mod_cast (by omega : 0 < n)
  have hn' : (0:ℝ) ≤ 1 / (n : ℝ) := by positivity
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hn', ← Finset.sum_sub_distrib]
  have hi : ∀ i, ‖gradient (f i) (y i) - gradient (f i) m‖ ≤ Lh Lf * ‖y - dgdC m‖ := by
    intro i
    refine le_trans (hA.lipschitz i _ _) ?_
    have h1 : ‖y i - m‖ ≤ ‖y - dgdC m‖ := by
      have := PiLp.norm_apply_le (y - dgdC m) i
      simpa [dgdC] using this
    exact mul_le_mul (dgd_Lf_le_Lh Lf i) h1 (norm_nonneg _)
      (le_trans (hA.Lf_pos i).le (dgd_Lf_le_Lh Lf i))
  have h2 : ∑ i, ‖gradient (f i) (y i) - gradient (f i) m‖ ≤ ∑ i : Fin n, Lh Lf * ‖y - dgdC m‖ :=
    Finset.sum_le_sum fun i _ => hi i
  have h3 : ∑ i : Fin n, Lh Lf * ‖y - dgdC m‖ = (n : ℝ) * (Lh Lf * ‖y - dgdC m‖) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h4 := mul_le_mul_of_nonneg_left (norm_sum_le Finset.univ
    (fun i => gradient (f i) (y i) - gradient (f i) m)) hn'
  have h5 := mul_le_mul_of_nonneg_left h2 hn'
  rw [h3] at h5
  have h6 : 1 / (n : ℝ) * ((n : ℝ) * (Lh Lf * ‖y - dgdC m‖)) = Lh Lf * ‖y - dgdC m‖ := by
    field_simp
  linarith

theorem dgd_rec (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k) (a b : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (hb : 0 ≤ b) (h : ∀ k, r (k + 1) ^ 2 ≤ a ^ 2 * r k ^ 2 + b ^ 2) :
    ∀ k, r k ≤ a ^ k * r 0 + b / Real.sqrt (1 - a ^ 2) := by
  have hpos : 0 < 1 - a ^ 2 := by nlinarith
  have hsq : Real.sqrt (1 - a ^ 2) ^ 2 = 1 - a ^ 2 := Real.sq_sqrt hpos.le
  have hsp : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.2 hpos
  set B := b ^ 2 / (1 - a ^ 2) with hB
  have hinv : ∀ k, r k ^ 2 ≤ (a ^ k * r 0) ^ 2 + B := by
    intro k
    induction k with
    | zero => simp; nlinarith [sq_nonneg b, div_nonneg (sq_nonneg b) hpos.le]
    | succ k ih =>
      have h1 := h k
      have h2 : a ^ 2 * r k ^ 2 ≤ a ^ 2 * ((a ^ k * r 0) ^ 2 + B) :=
        mul_le_mul_of_nonneg_left ih (sq_nonneg a)
      have h3 : a ^ 2 * B + b ^ 2 = B := by rw [hB]; field_simp; ring
      calc r (k + 1) ^ 2 ≤ a ^ 2 * r k ^ 2 + b ^ 2 := h1
        _ ≤ a ^ 2 * ((a ^ k * r 0) ^ 2 + B) + b ^ 2 := by linarith
        _ = (a ^ (k + 1) * r 0) ^ 2 + B := by linear_combination h3
  intro k
  have hv : (b / Real.sqrt (1 - a ^ 2)) ^ 2 = B := by
    rw [div_pow, hsq]
  have hu0 : 0 ≤ a ^ k * r 0 := mul_nonneg (pow_nonneg ha k) (hr 0)
  have hv0 : 0 ≤ b / Real.sqrt (1 - a ^ 2) := by positivity
  refine (sq_le_sq₀ (hr k) (by positivity)).1 ?_
  nlinarith [hinv k, hv, mul_nonneg hu0 hv0]

theorem dgd_young (A B s R R' α δ q : ℝ) (hα : 0 < α) (hδ : 0 < δ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hBs : B ≤ s) (hAq : A ^ 2 ≤ q * R ^ 2) (hR0 : 0 ≤ R') (hR' : R' ≤ A + B) :
    R' ^ 2 ≤ (1 + α * δ) * q * R ^ 2 + (1 + 1 / (α * δ)) * s ^ 2 := by
  have hε : 0 < α * δ := mul_pos hα hδ
  set ε := α * δ with hεdef
  have h1 : R' ^ 2 ≤ (A + B) ^ 2 := by
    exact pow_le_pow_left₀ hR0 hR' 2
  have h2 : 2 * A * B ≤ ε * A ^ 2 + B ^ 2 / ε := by
    have : 0 ≤ (ε * A - B) ^ 2 := sq_nonneg _
    have h3 : 2 * ε * A * B ≤ ε ^ 2 * A ^ 2 + B ^ 2 := by nlinarith
    rw [← sub_nonneg]
    have : ε * A ^ 2 + B ^ 2 / ε - 2 * A * B = (ε ^ 2 * A ^ 2 + B ^ 2 - 2 * ε * A * B) / ε := by
      field_simp
    rw [this]
    exact div_nonneg (by linarith) hε.le
  have h4 : B ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hB hBs 2
  have h5 : B ^ 2 / ε ≤ s ^ 2 / ε := div_le_div_of_nonneg_right h4 hε.le
  have h6 : (1 + ε) * A ^ 2 ≤ (1 + ε) * (q * R ^ 2) :=
    mul_le_mul_of_nonneg_left hAq (by linarith)
  have h7 : (A + B) ^ 2 = A ^ 2 + 2 * A * B + B ^ 2 := by ring
  have h8 : (1 + 1 / ε) * s ^ 2 = s ^ 2 + s ^ 2 / ε := by ring
  nlinarith

theorem dgd_main {n p : ℕ} (G : SimpleGraph (Fin n)) (W : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ) (hA : Assumption1 G W f Lf)
    (α : ℝ) (hα : 0 < α) (hα1 : α < (1 + lamN W) / Lh Lf)
    (c1 c2 : ℝ) (hc : Lemma3Consts f Lf c1 c2) (hα2 : α < c1) (hc2 : 0 < c2)
    (xs : ℕ → E p) (hxs : ∀ k, IsProj (Xstar f) (xbar (dgd W f α) k) (xs k)) :
    ∀ (k : ℕ) (i : Fin n), ‖dgd W f α k i - xs k‖ ≤
      c3 α c2 ^ k * ‖xs 0‖ +
        c4 α c2 (Lh Lf) (D f Lf) (beta W) / Real.sqrt (1 - c3 α c2 ^ 2) +
          α * D f Lf / (1 - beta W) := by
  intro k i
  have hn := hA.two_le
  have hβ1 := hA.beta_lt_one
  have hβ0 : 0 ≤ beta W := le_trans (abs_nonneg _) (le_max_left _ _)
  have hD0 : 0 ≤ D f Lf := Real.sqrt_nonneg _
  have hpos : 0 < 1 - beta W := by linarith
  have hLh := dgd_Lh_pos hA
  have hρ0 : 0 ≤ α * D f Lf / (1 - beta W) := div_nonneg (mul_nonneg hα.le hD0) hpos.le
  have hcons := dgd_cons hA hα hα1
  have hzi : ‖dgd W f α k i - xbar (dgd W f α) k‖ ≤ α * D f Lf / (1 - beta W) := by
    have := PiLp.norm_apply_le (dgd W f α k - dgdC (xbar (dgd W f α) k)) i
    have h2 : ‖dgd W f α k i - xbar (dgd W f α) k‖ ≤
        ‖dgd W f α k - dgdC (xbar (dgd W f α) k)‖ := by simpa [dgdC] using this
    exact le_trans h2 (hcons k)
  have hsplit : ‖dgd W f α k i - xs k‖ ≤
      ‖dgd W f α k i - xbar (dgd W f α) k‖ + ‖xbar (dgd W f α) k - xs k‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hc3nn : 0 ≤ c3 α c2 ^ k * ‖xs 0‖ := mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) k) (norm_nonneg _)
  have hc4nn : 0 ≤ c4 α c2 (Lh Lf) (D f Lf) (beta W) / Real.sqrt (1 - c3 α c2 ^ 2) :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rcases dgd_c2_small hA hα hc hα2 with hsmall | htriv
  · -- main case
    have hαc0 : 0 < α * c2 := mul_pos hα hc2
    have hq : 0 < 1 - α * c2 := by linarith
    obtain ⟨δ, hδdef⟩ : ∃ δ, δ = deltaStar α c2 := ⟨_, rfl⟩
    have hδ : δ = c2 / (2 * (1 - α * c2)) := by rw [hδdef]; rfl
    have hδpos : 0 < δ := by rw [hδ]; positivity
    obtain ⟨a, ha⟩ : ∃ a, a = c3 α c2 := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = c4 α c2 (Lh Lf) (D f Lf) (beta W) := ⟨_, rfl⟩
    have ha0 : 0 ≤ a := by rw [ha]; exact Real.sqrt_nonneg _
    have ha2 : a ^ 2 = 1 - α * c2 / 2 := by
      rw [ha]; unfold c3; exact Real.sq_sqrt (by linarith)
    have ha1 : a < 1 := by
      by_contra hcon
      have : 1 ≤ a := not_lt.1 hcon
      nlinarith
    have hb0 : 0 ≤ b := by rw [hb]; exact Real.sqrt_nonneg _
    have hb2 : b ^ 2 = α ^ 3 * (α + δ⁻¹) * Lh Lf ^ 2 * D f Lf ^ 2 / (1 - beta W) ^ 2 := by
      rw [hb]; unfold c4
      rw [Real.sq_sqrt]
      · unfold c4sq; rw [← hδdef]
      · unfold c4sq; rw [← hδdef]; positivity
    -- one step
    have hstep : ∀ k, ‖xbar (dgd W f α) (k + 1) - xs (k + 1)‖ ^ 2 ≤
        a ^ 2 * ‖xbar (dgd W f α) k - xs k‖ ^ 2 + b ^ 2 := by
      intro k
      have hproj : ‖xbar (dgd W f α) (k + 1) - xs (k + 1)‖ ≤
          ‖xbar (dgd W f α) (k + 1) - xs k‖ := (hxs (k + 1)).2 (xs k) (hxs k).1
      obtain ⟨gb, hgb⟩ : ∃ gb, gb = (1 / (n : ℝ)) • gradSum f (xbar (dgd W f α) k) := ⟨_, rfl⟩
      have hdec : xbar (dgd W f α) (k + 1) - xs k =
          ((xbar (dgd W f α) k - xs k) - α • gb) + α • (gb - gk f (dgd W f α) k) := by
        rw [dgd_xbar_succ hA.doublyStochastic]; module
      have hA1 := dgd_contraction hA hα hc hα2 (hxs k)
      rw [← hgb] at hA1
      have hB1 : ‖gb - gk f (dgd W f α) k‖ ≤ Lh Lf * (α * D f Lf / (1 - beta W)) := by
        rw [norm_sub_rev]
        have := dgd_mean_err hA (dgd W f α k) (xbar (dgd W f α) k)
        have h2 : ‖gk f (dgd W f α) k - gb‖ ≤ Lh Lf * ‖dgd W f α k - dgdC (xbar (dgd W f α) k)‖ := by
          rw [hgb]; exact this
        exact le_trans h2 (mul_le_mul_of_nonneg_left (hcons k) hLh.le)
      have hY := dgd_young
        ‖(xbar (dgd W f α) k - xs k) - α • gb‖ (α * ‖gb - gk f (dgd W f α) k‖)
        (α * (Lh Lf * (α * D f Lf / (1 - beta W)))) ‖xbar (dgd W f α) k - xs k‖
        ‖xbar (dgd W f α) (k + 1) - xs (k + 1)‖ α δ (1 - α * c2) hα hδpos (norm_nonneg _)
        (by positivity) (mul_le_mul_of_nonneg_left hB1 hα.le) hA1 (norm_nonneg _)
        (by
          refine le_trans hproj ?_
          rw [hdec]
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα])
      refine le_trans hY (le_of_eq ?_)
      have e1 : (1 + α * δ) * (1 - α * c2) = a ^ 2 := by
        rw [ha2, hδ]; field_simp; ring
      have e2 : (1 + 1 / (α * δ)) * (α * (Lh Lf * (α * D f Lf / (1 - beta W)))) ^ 2 = b ^ 2 := by
        rw [hb2]
        have : (1 - beta W) ≠ 0 := hpos.ne'
        have : δ ≠ 0 := hδpos.ne'
        have : α ≠ 0 := hα.ne'
        field_simp
      rw [← e1, ← e2]
    have hrec := dgd_rec (fun k => ‖xbar (dgd W f α) k - xs k‖) (fun k => norm_nonneg _) a b ha0 ha1 hb0 hstep k
    have hx0 : xbar (dgd W f α) 0 = 0 := by simp [xbar, dgd_zero]
    simp only [hx0, zero_sub, norm_neg] at hrec
    rw [← ha, ← hb]
    linarith
  · have := htriv _ _ (hxs k)
    have h0 : ‖xbar (dgd W f α) k - xs k‖ = 0 := by rw [this, sub_self, norm_zero]
    linarith

open YuanDGD.Linear in
theorem solution {n p : ℕ} (G : SimpleGraph (Fin n)) (W : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ) (hA : Assumption1 G W f Lf)
    (hX : (Xstar f).Nonempty) (α : ℝ) (hα : 0 < α) (hα1 : α < (1 + lamN W) / Lh Lf)
    (c1 c2 : ℝ) (hc : Lemma3Consts f Lf c1 c2) (hα2 : α < c1) (hc2 : 0 < c2)
    (xs : ℕ → E p) (hxs : ∀ k, IsProj (Xstar f) (xbar (dgd W f α) k) (xs k)) :
    ∀ (k : ℕ) (i : Fin n), ‖dgd W f α k i - xs k‖ ≤
      c3 α c2 ^ k * ‖xs 0‖ +
        c4 α c2 (Lh Lf) (D f Lf) (beta W) / Real.sqrt (1 - c3 α c2 ^ 2) +
          α * D f Lf / (1 - beta W) := by
  exact dgd_main G W f Lf hA α hα hα1 c1 c2 hc hα2 hc2 xs hxs

end
