-- Prove2me | solution 1 for WildeQIT.EADamping.isAchievableEARate_le_channelMutualInfo
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:15:56.404425+00:00
-- url     : https://prove2.me/submissions/a9ba2bd3-5883-47f3-a39d-4d18227e4c5b

import Mathlib
import Definitions.Def_DattaDiscord_mutualInfo
import Definitions.Def_WildeQIT_EADamping_channelMutualInfo
import Definitions.Def_WildeQIT_EADamping_IsAchievableEARate

set_option autoImplicit false

/-! Subadditivity of von Neumann entropy, `S(AB) ≤ S(A) + S(B)` (so `I(A:B) ≥ 0`), proved with
eigenbases only: Schur concavity of `negMulLog` under unitary conjugation (Jensen) + classical
Gibbs inequality on the product eigenbasis of `ρ_A ⊗ ρ_B`. No matrix logarithm needed. -/

namespace SubaddAux
open Matrix
open scoped ComplexOrder Kronecker

lemma trace_cfc_herm {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc]
  first
    | rw [Unitary.coe_star_mul_self]
    | rw [Unitary.star_mul_self]
    | rw [Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2]
  rw [Matrix.one_mul, Matrix.trace_diagonal]
  rfl

lemma vn_eq {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    QAlgorithms.vnEntropy s = (∑ i, Real.negMulLog (hs.eigenvalues i)) / Real.log 2 := by
  rw [QAlgorithms.vnEntropy, trace_cfc_herm hs, Complex.re_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Complex.ofReal_re, Real.negMulLog, Real.logb]
  ring

lemma trace_eig {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    s.trace.re = ∑ i, hs.eigenvalues i := by
  have hsa : IsSelfAdjoint s := hs
  have h1 : cfc (fun x : ℝ => x) s = s := cfc_id' ℝ s hsa
  conv_lhs => rw [← h1]
  rw [trace_cfc_herm hs, Complex.re_sum]
  simp only [Complex.ofReal_re]

/-- spectral decomposition `s = U D Uᴴ` -/
lemma spec {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    (hs.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => ((hs.eigenvalues i : ℝ) : ℂ)) *
      star (hs.eigenvectorUnitary : Matrix n n ℂ) = s := by
  have hsa : IsSelfAdjoint s := hs
  have h := cfc_id' ℝ s hsa
  rw [hs.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply] at h
  exact h

lemma unit_mul_star {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU

lemma unit_star_mul {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU

lemma conj_diag {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    star (hs.eigenvectorUnitary : Matrix n n ℂ) * s * (hs.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (fun i => ((hs.eigenvalues i : ℝ) : ℂ)) := by
  have hU := unit_star_mul hs.eigenvectorUnitary.2
  calc _ = star (hs.eigenvectorUnitary : Matrix n n ℂ) * ((hs.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun i => ((hs.eigenvalues i : ℝ) : ℂ)) * star (hs.eigenvectorUnitary : Matrix n n ℂ)) *
        (hs.eigenvectorUnitary : Matrix n n ℂ) := by rw [spec hs]
    _ = _ := by
        simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
        rw [Matrix.mul_assoc, hU, Matrix.mul_one]

lemma re_mul_star (z : ℂ) : (z * star z).re = Complex.normSq z := by
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

lemma re_star_mul (z : ℂ) : (star z * z).re = Complex.normSq z := by
  rw [mul_comm, re_mul_star]

lemma row_sum {n : Type*} [Fintype n] [DecidableEq n] {V : Matrix n n ℂ}
    (hV : V ∈ unitaryGroup n ℂ) (j : n) : ∑ i, Complex.normSq (V j i) = 1 := by
  have h := congrArg Complex.re (congrFun (congrFun (unit_mul_star hV) j) j)
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Complex.re_sum] at h
  simpa only [Matrix.star_apply, re_mul_star, Complex.one_re] using h

lemma col_sum {n : Type*} [Fintype n] [DecidableEq n] {V : Matrix n n ℂ}
    (hV : V ∈ unitaryGroup n ℂ) (i : n) : ∑ j, Complex.normSq (V j i) = 1 := by
  have h := congrArg Complex.re (congrFun (congrFun (unit_star_mul hV) i) i)
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Complex.re_sum] at h
  simpa only [Matrix.star_apply, re_star_mul, Complex.one_re] using h

/-- diagonal of a unitary conjugate in terms of eigenvalues -/
lemma diag_conj {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (W : Matrix n n ℂ) (j : n) :
    ((star W * ρ * W) j j).re = ∑ i, hρ.eigenvalues i *
      Complex.normSq ((star W * (hρ.eigenvectorUnitary : Matrix n n ℂ)) j i) := by
  set U := (hρ.eigenvectorUnitary : Matrix n n ℂ)
  have e : star W * ρ * W = (star W * U) * diagonal (fun i => ((hρ.eigenvalues i : ℝ) : ℂ)) *
      star (star W * U) := by
    rw [star_mul, star_star]
    calc star W * ρ * W = star W * (U * diagonal (fun i => ((hρ.eigenvalues i : ℝ) : ℂ)) * star U) * W := by
          rw [spec hρ]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mul_diagonal, Matrix.star_apply]
  have : (star W * U) j i * ((hρ.eigenvalues i : ℝ) : ℂ) * star ((star W * U) j i) =
      ((hρ.eigenvalues i : ℝ) : ℂ) * ((star W * U) j i * star ((star W * U) j i)) := by ring
  rw [this, Complex.re_ofReal_mul, re_mul_star]

/-- Schur concavity: entropy (in nats) of the eigenvalues ≤ entropy of any unitary diagonal -/
lemma eig_le_diag {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (W : Matrix n n ℂ) (hW : W ∈ unitaryGroup n ℂ) :
    ∑ i, Real.negMulLog (hρ.1.eigenvalues i) ≤
      ∑ j, Real.negMulLog ((star W * ρ * W) j j).re := by
  set U := (hρ.1.eigenvectorUnitary : Matrix n n ℂ)
  have hV : star W * U ∈ unitaryGroup n ℂ :=
    Submonoid.mul_mem _ (Unitary.star_mem hW) hρ.1.eigenvectorUnitary.2
  set w : n → n → ℝ := fun j i => Complex.normSq ((star W * U) j i)
  have hw0 : ∀ j i, 0 ≤ w j i := fun j i => Complex.normSq_nonneg _
  calc ∑ i, Real.negMulLog (hρ.1.eigenvalues i)
      = ∑ i, (∑ j, w j i) * Real.negMulLog (hρ.1.eigenvalues i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [show (∑ j, w j i) = 1 from col_sum hV i, one_mul]
    _ = ∑ j, ∑ i, w j i * Real.negMulLog (hρ.1.eigenvalues i) := by
        simp only [Finset.sum_mul]
        exact Finset.sum_comm
    _ ≤ ∑ j, Real.negMulLog (∑ i, w j i * hρ.1.eigenvalues i) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ) (w := w j)
          (p := hρ.1.eigenvalues) (fun i _ => hw0 j i) (row_sum hV j)
          (fun i _ => Set.mem_Ici.mpr (hρ.eigenvalues_nonneg i))
        simpa only [smul_eq_mul] using this
    _ = ∑ j, Real.negMulLog ((star W * ρ * W) j j).re := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [diag_conj hρ.1 W j]
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring

lemma diag_nonneg {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (W : Matrix n n ℂ) (j : n) : 0 ≤ ((star W * ρ * W) j j).re := by
  rw [diag_conj hρ.1 W j]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hρ.eigenvalues_nonneg i) (Complex.normSq_nonneg _))

/-- partial trace over `B` of a product-unitary conjugate -/
lemma tr_right_conj {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (X : Matrix (a × b) (a × b) ℂ) (P : Matrix a a ℂ) (Q : Matrix b b ℂ) (hQ : Q * star Q = 1)
    (k : a) :
    ∑ l, (star (P ⊗ₖ Q) * X * (P ⊗ₖ Q)) (k, l) (k, l) = (star P * QAlgorithms.traceRight X * P) k k := by
  have hQ' : ∀ y x : b, ∑ l, Q y l * star (Q x l) = if y = x then 1 else 0 := fun y x => by
    have := congrFun (congrFun hQ y) x
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa only [Matrix.star_apply] using this
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.kroneckerMap_apply, QAlgorithms.traceRight,
    Matrix.of_apply, Fintype.sum_prod_type, star_mul', Finset.sum_mul, Finset.mul_sum]
  -- LHS: Σ l y1 y2 x1 x2 (sP x1 * sQ x2 l * X) * (P y1 * Q y2 l); RHS: Σ y1 x1 h, sP x1 * X(x1,h)(y1,h) * P y1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y1 _ => ?_)
  rw [Finset.sum_comm]
  -- Σ y2 Σ l Σ x1 Σ x2 ... -> move l innermost
  calc _ = ∑ y2 : b, ∑ x1 : a, ∑ x2 : b, star (P x1 k) * X (x1, x2) (y1, y2) * P y1 k *
        (∑ l, Q y2 l * star (Q x2 l)) := by
          refine Finset.sum_congr rfl (fun y2 _ => ?_)
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun x1 _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun x2 _ => ?_)
          refine Finset.sum_congr rfl (fun l _ => ?_)
          ring
    _ = _ := by
          simp only [hQ', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
            Finset.mem_univ, if_true]
          rw [Finset.sum_comm]

/-- partial trace over `A` of a product-unitary conjugate -/
lemma tr_left_conj {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (X : Matrix (a × b) (a × b) ℂ) (P : Matrix a a ℂ) (Q : Matrix b b ℂ) (hP : P * star P = 1)
    (l : b) :
    ∑ k, (star (P ⊗ₖ Q) * X * (P ⊗ₖ Q)) (k, l) (k, l) = (star Q * QAlgorithms.traceLeft X * Q) l l := by
  have hP' : ∀ y x : a, ∑ k, P y k * star (P x k) = if y = x then 1 else 0 := fun y x => by
    have := congrFun (congrFun hP y) x
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa only [Matrix.star_apply] using this
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.kroneckerMap_apply, QAlgorithms.traceLeft,
    Matrix.of_apply, Fintype.sum_prod_type, star_mul', Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ y1 : a, ∑ y2 : b, ∑ x2 : b, ∑ x1 : a, star (Q x2 l) * X (x1, x2) (y1, y2) * Q y2 l *
        (∑ k, P y1 k * star (P x1 k)) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          all_goals refine Finset.sum_congr rfl (fun y1 _ => ?_)
          all_goals rw [Finset.sum_comm]
          all_goals refine Finset.sum_congr rfl (fun y2 _ => ?_)
          all_goals rw [Finset.sum_comm]
          all_goals symm
          all_goals rw [Finset.sum_comm]
          all_goals refine Finset.sum_congr rfl (fun x1 _ => ?_)
          all_goals rw [Finset.sum_comm]
          all_goals refine Finset.sum_congr rfl (fun k _ => ?_)
          all_goals refine Finset.sum_congr rfl (fun x2 _ => ?_)
          all_goals ring
    _ = _ := by
          simp only [hP', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          rw [Finset.sum_comm]
          all_goals refine Finset.sum_congr rfl (fun y2 _ => ?_)
          all_goals rw [Finset.sum_comm]

lemma herm_tr_right {a b : Type*} [Fintype b] {M : Matrix (a × b) (a × b) ℂ} (h : M.IsHermitian) :
    (QAlgorithms.traceRight M).IsHermitian := by
  refine Matrix.IsHermitian.ext (fun i j => ?_)
  simp only [QAlgorithms.traceRight, Matrix.of_apply, star_sum]
  exact Finset.sum_congr rfl (fun k _ => h.apply (i, k) (j, k))

lemma herm_tr_left {a b : Type*} [Fintype a] {M : Matrix (a × b) (a × b) ℂ} (h : M.IsHermitian) :
    (QAlgorithms.traceLeft M).IsHermitian := by
  refine Matrix.IsHermitian.ext (fun i j => ?_)
  simp only [QAlgorithms.traceLeft, Matrix.of_apply, star_sum]
  exact Finset.sum_congr rfl (fun k _ => h.apply (k, i) (k, j))

lemma trace_tr_right {a b : Type*} [Fintype a] [Fintype b] (M : Matrix (a × b) (a × b) ℂ) :
    (QAlgorithms.traceRight M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, QAlgorithms.traceRight, Matrix.of_apply, Fintype.sum_prod_type]

/-- pointwise Gibbs inequality -/
lemma gibbs {t x y : ℝ} (ht : 0 ≤ t) (htx : t ≤ x) (hty : t ≤ y) :
    Real.negMulLog t ≤ -(t * Real.log x) - t * Real.log y + x * y - t := by
  rcases ht.eq_or_lt with h | h
  · subst h
    rw [Real.negMulLog_zero]
    nlinarith [mul_nonneg htx hty]
  · have hx : 0 < x := by linarith
    have hy : 0 < y := by linarith
    have hl := Real.log_le_sub_one_of_pos (show 0 < x * y / t by positivity)
    rw [Real.log_div (by positivity) h.ne', Real.log_mul hx.ne' hy.ne'] at hl
    have hm : t * (Real.log x + Real.log y - Real.log t) ≤ t * (x * y / t - 1) :=
      mul_le_mul_of_nonneg_left hl h.le
    have e : t * (x * y / t - 1) = x * y - t := by field_simp
    rw [Real.negMulLog]
    nlinarith [hm, e]

/-- **Subadditivity** `S(AB) ≤ S(A) + S(B)` of von Neumann entropy. -/
theorem subadd {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    QAlgorithms.vnEntropy ρ ≤ QAlgorithms.vnEntropy (QAlgorithms.traceRight ρ) +
      QAlgorithms.vnEntropy (QAlgorithms.traceLeft ρ) := by
  have hA : (QAlgorithms.traceRight ρ).IsHermitian := herm_tr_right hρ.1
  have hB : (QAlgorithms.traceLeft ρ).IsHermitian := herm_tr_left hρ.1
  set P := (hA.eigenvectorUnitary : Matrix A A ℂ) with hP
  set Q := (hB.eigenvectorUnitary : Matrix B B ℂ) with hQ
  have hPu : P ∈ unitaryGroup A ℂ := hA.eigenvectorUnitary.2
  have hQu : Q ∈ unitaryGroup B ℂ := hB.eigenvectorUnitary.2
  have hW : P ⊗ₖ Q ∈ unitaryGroup (A × B) ℂ := Matrix.kronecker_mem_unitary hPu hQu
  set t : A × B → ℝ := fun x => ((star (P ⊗ₖ Q) * ρ * (P ⊗ₖ Q)) x x).re with ht_def
  have ht0 : ∀ x, 0 ≤ t x := fun x => diag_nonneg hρ _ x
  have hrow : ∀ k, ∑ l, t (k, l) = hA.eigenvalues k := by
    intro k
    have h := congrArg Complex.re (tr_right_conj ρ P Q (unit_mul_star hQu) k)
    rw [Complex.re_sum, conj_diag hA, Matrix.diagonal_apply_eq, Complex.ofReal_re] at h
    exact h
  have hcol : ∀ l, ∑ k, t (k, l) = hB.eigenvalues l := by
    intro l
    have h := congrArg Complex.re (tr_left_conj ρ P Q (unit_mul_star hPu) l)
    rw [Complex.re_sum, conj_diag hB, Matrix.diagonal_apply_eq, Complex.ofReal_re] at h
    exact h
  have hS : ∑ k, hA.eigenvalues k = 1 := by
    rw [← trace_eig hA, trace_tr_right, htr, Complex.one_re]
  have hSB : ∑ l, hB.eigenvalues l = 1 := by
    rw [← hS]
    calc ∑ l, hB.eigenvalues l = ∑ l, ∑ k, t (k, l) := Finset.sum_congr rfl (fun l _ => (hcol l).symm)
      _ = ∑ k, ∑ l, t (k, l) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun k _ => hrow k)
  have h1 := eig_le_diag hρ (P ⊗ₖ Q) hW
  have h2 : ∑ x, Real.negMulLog (t x) ≤ ∑ k, Real.negMulLog (hA.eigenvalues k) +
      ∑ l, Real.negMulLog (hB.eigenvalues l) := by
    have hle : ∀ x : A × B, Real.negMulLog (t x) ≤ -(t x * Real.log (hA.eigenvalues x.1)) -
        t x * Real.log (hB.eigenvalues x.2) + hA.eigenvalues x.1 * hB.eigenvalues x.2 - t x := fun x =>
      gibbs (ht0 x)
        (by rw [← hrow x.1]; exact Finset.single_le_sum (f := fun l => t (x.1, l))
              (fun l _ => ht0 (x.1, l)) (Finset.mem_univ x.2))
        (by rw [← hcol x.2]; exact Finset.single_le_sum (f := fun k => t (k, x.2))
              (fun k _ => ht0 (k, x.2)) (Finset.mem_univ x.1))
    refine (Finset.sum_le_sum (fun x _ => hle x)).trans (le_of_eq ?_)
    have e1 : ∑ x : A × B, t x * Real.log (hA.eigenvalues x.1) =
        ∑ k, hA.eigenvalues k * Real.log (hA.eigenvalues k) := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl (fun k _ => by
        show ∑ l, t (k, l) * Real.log (hA.eigenvalues k) = _
        rw [← Finset.sum_mul, hrow k])
    have e2 : ∑ x : A × B, t x * Real.log (hB.eigenvalues x.2) =
        ∑ l, hB.eigenvalues l * Real.log (hB.eigenvalues l) := by
      rw [Fintype.sum_prod_type_right]
      exact Finset.sum_congr rfl (fun l _ => by
        show ∑ k, t (k, l) * Real.log (hB.eigenvalues l) = _
        rw [← Finset.sum_mul, hcol l])
    have e3 : ∑ x : A × B, hA.eigenvalues x.1 * hB.eigenvalues x.2 = 1 := by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, hSB, mul_one, hS]
    have e4 : ∑ x : A × B, t x = 1 := by
      rw [Fintype.sum_prod_type]
      simp only [hrow, hS]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, e1, e2, e3, e4]
    simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
    ring
  rw [vn_eq hρ.1, vn_eq hA, vn_eq hB, ← add_div]
  exact (div_le_div_iff_of_pos_right (Real.log_pos one_lt_two)).mpr (h1.trans h2)

/-- `I(A:B) ≥ 0`. -/
theorem mutualInfo_nonneg {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    0 ≤ DattaDiscord.mutualInfo ρ := by
  have := subadd ρ hρ htr
  rw [DattaDiscord.mutualInfo]
  linarith


open Polynomial in
/-- generic: Hermitian `A` whose charpoly splits as `∏ (X - C (d i))` (real `d`, any index type). -/
lemma sum_eig_of_charpoly {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (d : ι → ℝ)
    (h : A.charpoly = ∏ i, (X - C ((d i : ℝ) : ℂ))) (f : ℝ → ℝ) :
    ∑ i, f (hA.eigenvalues i) = ∑ i, f (d i) := by
  have h1 := hA.roots_charpoly_eq_eigenvalues
  have h2 : A.charpoly.roots = Multiset.map (fun i => ((d i : ℝ) : ℂ)) Finset.univ.val := by
    rw [h, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have h3 : (A.charpoly.roots.map (fun z => f z.re)).sum = ∑ i, f (hA.eigenvalues i) := by
    rw [h1, Multiset.map_map, Finset.sum_eq_multiset_sum]
    congr 1
  have h4 : (A.charpoly.roots.map (fun z => f z.re)).sum = ∑ i, f (d i) := by
    rw [h2, Multiset.map_map, Finset.sum_eq_multiset_sum]
    congr 1
  rw [← h3, h4]

open Polynomial in
lemma vn_of_charpoly {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (d : ι → ℝ)
    (h : A.charpoly = ∏ i, (X - C ((d i : ℝ) : ℂ))) :
    QAlgorithms.vnEntropy A = (∑ i, Real.negMulLog (d i)) / Real.log 2 := by
  rw [vn_eq hA, sum_eig_of_charpoly hA d h]

lemma vn_charpoly_eq {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A.charpoly = B.charpoly) :
    QAlgorithms.vnEntropy A = QAlgorithms.vnEntropy B := by
  rw [vn_eq hB, vn_of_charpoly hA hB.eigenvalues (h.trans hB.charpoly_eq)]

/-- entropy is invariant under relabelling the basis -/
lemma vn_reindex {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    QAlgorithms.vnEntropy (Matrix.reindex e e A) = QAlgorithms.vnEntropy A := by
  have hB : (Matrix.reindex e e A).IsHermitian := hA.submatrix e.symm
  exact vn_charpoly_eq hB hA (Matrix.charpoly_reindex e A)

/-- entropy is invariant under unitary conjugation -/
lemma vn_unit_conj {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    QAlgorithms.vnEntropy (U * A * star U) = QAlgorithms.vnEntropy A := by
  have hB : (U * A * star U).IsHermitian := by
    rw [Matrix.star_eq_conjTranspose]; unfold Matrix.IsHermitian
    simp [Matrix.conjTranspose_mul, hA.eq, Matrix.mul_assoc]
  refine vn_charpoly_eq hB hA ?_
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.one_mul]

lemma herm_kron {a b : Type*} {A : Matrix a a ℂ} {B : Matrix b b ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_kronecker, hA.eq, hB.eq]

open Polynomial in
lemma charpoly_kron {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : Matrix a a ℂ} {B : Matrix b b ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A ⊗ₖ B).charpoly =
      ∏ p : a × b, (X - C (((hA.eigenvalues p.1 * hB.eigenvalues p.2 : ℝ)) : ℂ)) := by
  set U := (hA.eigenvectorUnitary : Matrix a a ℂ)
  set V := (hB.eigenvectorUnitary : Matrix b b ℂ)
  have e : A ⊗ₖ B = (U ⊗ₖ V) * (diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) ⊗ₖ
      diagonal (fun j => ((hB.eigenvalues j : ℝ) : ℂ))) * star (U ⊗ₖ V) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
      spec hA, spec hB]
  have hUV : star (U ⊗ₖ V) * (U ⊗ₖ V) = 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
      unit_star_mul hA.eigenvectorUnitary.2, unit_star_mul hB.eigenvectorUnitary.2,
      Matrix.one_kronecker_one]
  rw [e, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUV, Matrix.one_mul,
    Matrix.diagonal_kronecker_diagonal, Matrix.charpoly_diagonal]
  simp

/-- additivity of entropy on product states -/
theorem vn_kron {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : Matrix a a ℂ} {B : Matrix b b ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (htA : A.trace = 1) (htB : B.trace = 1) :
    QAlgorithms.vnEntropy (A ⊗ₖ B) = QAlgorithms.vnEntropy A + QAlgorithms.vnEntropy B := by
  rw [vn_of_charpoly (herm_kron hA hB) _ (charpoly_kron hA hB), vn_eq hA, vn_eq hB, ← add_div]
  congr 1
  have sA : ∑ i, hA.eigenvalues i = 1 := by rw [← trace_eig hA, htA]; simp
  have sB : ∑ j, hB.eigenvalues j = 1 := by rw [← trace_eig hB, htB]; simp
  rw [Fintype.sum_prod_type]
  simp only [Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, sA, sB,
    one_mul]


lemma trace_tr_left {a b : Type*} [Fintype a] [Fintype b] (M : Matrix (a × b) (a × b) ℂ) :
    (QAlgorithms.traceLeft M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, QAlgorithms.traceLeft, Matrix.of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma psd_tr_left {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {M : Matrix (a × b) (a × b) ℂ} (h : M.PosSemidef) : (QAlgorithms.traceLeft M).PosSemidef := by
  have e : QAlgorithms.traceLeft M = ∑ x : a,
      (Matrix.of fun (j : b) (p : a × b) => if p = (x, j) then (1 : ℂ) else 0) * M *
        (Matrix.of fun (j : b) (p : a × b) => if p = (x, j) then (1 : ℂ) else 0)ᴴ := by
    ext i j
    simp [QAlgorithms.traceLeft, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e]
  exact Matrix.posSemidef_sum _ (fun x _ => h.mul_mul_conjTranspose_same _)

lemma psd_tr_right {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {M : Matrix (a × b) (a × b) ℂ} (h : M.PosSemidef) : (QAlgorithms.traceRight M).PosSemidef := by
  have e : QAlgorithms.traceRight M = ∑ x : b,
      (Matrix.of fun (j : a) (p : a × b) => if p = (j, x) then (1 : ℂ) else 0) * M *
        (Matrix.of fun (j : a) (p : a × b) => if p = (j, x) then (1 : ℂ) else 0)ᴴ := by
    ext i j
    simp [QAlgorithms.traceRight, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e]
  exact Matrix.posSemidef_sum _ (fun x _ => h.mul_mul_conjTranspose_same _)

/-- regrouping `M (B T) ≃ (M T) B` -/
def regroup (M B T : Type*) : M × (B × T) ≃ (M × T) × B :=
  ((Equiv.refl M).prodCongr (Equiv.prodComm B T)).trans (Equiv.prodAssoc M T B).symm

lemma tr_left_regroup {M B T : Type*} [Fintype M] [Fintype T] [DecidableEq M] [DecidableEq B]
    [DecidableEq T] (ρ : Matrix (M × (B × T)) (M × (B × T)) ℂ) :
    QAlgorithms.traceLeft (Matrix.reindex (regroup M B T) (regroup M B T) ρ) =
      QAlgorithms.traceRight (QAlgorithms.traceLeft ρ) := by
  ext i j
  simp [QAlgorithms.traceLeft, QAlgorithms.traceRight, regroup, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- D3a (abstract): if `ρ_{MT} = ρ_M ⊗ ρ_T` then `I(M; B T) ≤ I(M T; B)`. -/
theorem mi_le_regroup {M B T : Type*} [Fintype M] [Fintype B] [Fintype T] [DecidableEq M]
    [DecidableEq B] [DecidableEq T] (ρ : Matrix (M × (B × T)) (M × (B × T)) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hprod : QAlgorithms.traceRight (Matrix.reindex (regroup M B T) (regroup M B T) ρ) =
      QAlgorithms.traceRight ρ ⊗ₖ QAlgorithms.traceLeft (QAlgorithms.traceLeft ρ)) :
    DattaDiscord.mutualInfo ρ ≤
      DattaDiscord.mutualInfo (Matrix.reindex (regroup M B T) (regroup M B T) ρ) := by
  unfold DattaDiscord.mutualInfo
  have hBT := psd_tr_left hρ
  have htBT : (QAlgorithms.traceLeft ρ).trace = 1 := by rw [trace_tr_left, htr]
  have htM : (QAlgorithms.traceRight ρ).trace = 1 := by rw [trace_tr_right, htr]
  have htT : (QAlgorithms.traceLeft (QAlgorithms.traceLeft ρ)).trace = 1 := by
    rw [trace_tr_left, htBT]
  rw [hprod, vn_kron (herm_tr_right hρ.1) (herm_tr_left hBT.1) htM htT, tr_left_regroup,
    vn_reindex _ hρ.1]
  have h3 := subadd (QAlgorithms.traceLeft ρ) hBT htBT
  linarith

end SubaddAux

open WildeQIT WildeQIT.EADamping
open scoped Kronecker

namespace EAConv
open Matrix

noncomputable def outState {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {n k : ℕ} (c : EACode a b n k) (N : QChannel a b) (m : Fin k) :
    Matrix ((Fin n → b) × Fin c.dB) ((Fin n → b) × Fin c.dB) ℂ :=
  leftApply (powKraus N n) (leftApply (c.enc m).K (QAlgorithms.pureDensity c.Ψ))

noncomputable def cqState {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {n k : ℕ} (c : EACode a b n k) (N : QChannel a b) :
    Matrix (Fin k × ((Fin n → b) × Fin c.dB)) (Fin k × ((Fin n → b) × Fin c.dB)) ℂ :=
  ∑ m, ((1 : ℂ) / k) • (Matrix.single m m (1 : ℂ) ⊗ₖ outState c N m)

lemma tl_sum {α β ι : Type*} [Fintype α] [Fintype ι] (Y : ι → Matrix (α × β) (α × β) ℂ) :
    QAlgorithms.traceLeft (∑ i, Y i) = ∑ i, QAlgorithms.traceLeft (Y i) := by
  ext r r'
  simp only [QAlgorithms.traceLeft, Matrix.of_apply, Matrix.sum_apply]
  exact Finset.sum_comm

lemma tl_cyc {a b r : Type*} [Fintype a] [Fintype b] [Fintype r] [DecidableEq r]
    (A : Matrix b a ℂ) (Y : Matrix (a × r) (b × r) ℂ) :
    QAlgorithms.traceLeft ((A ⊗ₖ (1 : Matrix r r ℂ)) * Y) =
      QAlgorithms.traceLeft (Y * (A ⊗ₖ (1 : Matrix r r ℂ))) := by
  ext s s'
  simp [QAlgorithms.traceLeft, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

lemma tl_leftApply {ι a b r : Type} [Fintype ι] [Fintype a] [Fintype b] [Fintype r]
    [DecidableEq a] [DecidableEq r] (K : ι → Matrix b a ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    (X : Matrix (a × r) (a × r) ℂ) :
    QAlgorithms.traceLeft (leftApply K X) = QAlgorithms.traceLeft X := by
  unfold leftApply
  rw [tl_sum]
  have h1 : ∀ i, QAlgorithms.traceLeft ((K i ⊗ₖ (1 : Matrix r r ℂ)) * X * (K i ⊗ₖ (1 : Matrix r r ℂ))ᴴ)
      = QAlgorithms.traceLeft (X * (((K i)ᴴ * K i) ⊗ₖ (1 : Matrix r r ℂ))) := by
    intro i
    rw [Matrix.mul_assoc, tl_cyc, Matrix.mul_assoc, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  simp_rw [h1, ← tl_sum, ← Matrix.mul_sum]
  have h2 : ∑ i, (((K i)ᴴ * K i) ⊗ₖ (1 : Matrix r r ℂ)) = 1 := by
    rw [← Matrix.one_kronecker_one, ← hK]
    ext p q
    simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]
  rw [h2, Matrix.mul_one]

lemma powKraus_complete {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    (N : QChannel a b) (n : ℕ) :
    ∑ i, (powKraus N n i)ᴴ * powKraus N n i = 1 := by
  ext x x'
  have hc : ∀ j, ∑ l, ∑ c, star (N.K l c (x j)) * N.K l c (x' j) = if x j = x' j then 1 else 0 := by
    intro j
    have := congrFun (congrFun N.complete (x j)) (x' j)
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using this
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, powKraus, Matrix.of_apply,
    Matrix.one_apply, star_prod, ← Finset.prod_mul_distrib]
  have e1 : ∀ i : Fin n → N.ι, ∑ y : Fin n → b, ∏ j, star (N.K (i j) (y j) (x j)) * N.K (i j) (y j) (x' j)
      = ∏ j, ∑ c, star (N.K (i j) c (x j)) * N.K (i j) c (x' j) := fun i =>
    (Fintype.prod_sum (fun j c => star (N.K (i j) c (x j)) * N.K (i j) c (x' j))).symm
  simp_rw [e1]
  rw [← Fintype.prod_sum (fun j l => ∑ c, star (N.K l c (x j)) * N.K l c (x' j))]
  simp_rw [hc]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma trace_pure {ι : Type*} [Fintype ι] (Ψ : EuclideanSpace ℂ ι) (h : ‖Ψ‖ = 1) :
    (QAlgorithms.pureDensity Ψ).trace = 1 := by
  have h2 := EuclideanSpace.norm_sq_eq Ψ
  rw [h, one_pow] at h2
  simp only [Matrix.trace, Matrix.diag, QAlgorithms.pureDensity, Matrix.of_apply, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  exact_mod_cast h2.symm

lemma outState_tl {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {n k : ℕ} (c : EACode a b n k) (N : QChannel a b) (m : Fin k) :
    QAlgorithms.traceLeft (outState c N m) = QAlgorithms.traceLeft (QAlgorithms.pureDensity c.Ψ) := by
  unfold outState
  rw [tl_leftApply _ (powKraus_complete N n), tl_leftApply _ (c.enc m).complete]

lemma cq_prod {k : ℕ} (hk : 0 < k) {B T : Type*} [Fintype B] [Fintype T] [DecidableEq B]
    [DecidableEq T] (ρ : Fin k → Matrix (B × T) (B × T) ℂ) (σ : Matrix T T ℂ)
    (hσ : ∀ m, QAlgorithms.traceLeft (ρ m) = σ) (htσ : σ.trace = 1) :
    QAlgorithms.traceRight (Matrix.reindex (SubaddAux.regroup (Fin k) B T) (SubaddAux.regroup (Fin k) B T)
        (∑ m, ((1 : ℂ) / k) • (Matrix.single m m (1 : ℂ) ⊗ₖ ρ m))) =
      QAlgorithms.traceRight (∑ m, ((1 : ℂ) / k) • (Matrix.single m m (1 : ℂ) ⊗ₖ ρ m)) ⊗ₖ
        QAlgorithms.traceLeft (QAlgorithms.traceLeft
          (∑ m, ((1 : ℂ) / k) • (Matrix.single m m (1 : ℂ) ⊗ₖ ρ m))) := by
  set cq := ∑ m, ((1 : ℂ) / k) • (Matrix.single m m (1 : ℂ) ⊗ₖ ρ m) with hcqdef
  have hcq : ∀ m p m' p', cq (m, p) (m', p') = if m = m' then (1 / k : ℂ) * ρ m p p' else 0 := by
    intro m p m' p'
    rw [hcqdef]
    simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.single_apply]
    split_ifs with hmm
    · simp_all
    · exact Finset.sum_eq_zero (fun x _ => if_neg (fun hx => hmm (hx.1.symm.trans hx.2)))
  have e1 : ∀ m t t', ∑ β, ρ m (β, t) (β, t') = σ t t' := fun m t t' => by
    have := congrFun (congrFun (hσ m) t) t'
    simpa [QAlgorithms.traceLeft] using this
  have e2 : ∀ m, ∑ β, ∑ t, ρ m (β, t) (β, t) = 1 := fun m => by
    rw [Finset.sum_comm]; simp only [e1]; simpa [Matrix.trace] using htσ
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hR : ∀ m m', QAlgorithms.traceRight cq m m' = if m = m' then (1 / k : ℂ) else 0 := by
    intro m m'
    simp only [QAlgorithms.traceRight, Matrix.of_apply]
    by_cases h : m = m'
    · subst h; simp only [hcq, if_true, Fintype.sum_prod_type, ← Finset.mul_sum, e2, mul_one]
    · simp [hcq, h]
  have hLL : ∀ t t', QAlgorithms.traceLeft (QAlgorithms.traceLeft cq) t t' = σ t t' := by
    intro t t'
    simp only [QAlgorithms.traceLeft, Matrix.of_apply, hcq, if_true]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, e1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hRG : ∀ m t m' t', QAlgorithms.traceRight (Matrix.reindex (SubaddAux.regroup (Fin k) B T)
      (SubaddAux.regroup (Fin k) B T) cq) (m, t) (m', t') = if m = m' then (1 / k : ℂ) * σ t t' else 0 := by
    intro m t m' t'
    simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    simp only [SubaddAux.regroup, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.prodAssoc_apply,
      Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.refl_symm, Equiv.prodComm_symm,
      Equiv.refl_apply, Equiv.prodComm_apply, Prod.map, Prod.swap, hcq]
    by_cases h : m = m'
    · subst h; simp only [if_true, ← Finset.mul_sum, e1]
    · simp [h]
  ext ⟨m, t⟩ ⟨m', t'⟩
  rw [hRG, Matrix.kroneckerMap_apply, hR, hLL]
  split_ifs <;> simp

/-- D3a hypothesis for the code state: `ω_{M T_B} = ω_M ⊗ ω_{T_B}` (encoders act on `T_A` only). -/
theorem cqState_prod {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {n k : ℕ} (hk : 0 < k) (c : EACode a b n k) (N : QChannel a b) :
    QAlgorithms.traceRight (Matrix.reindex (SubaddAux.regroup (Fin k) (Fin n → b) (Fin c.dB))
        (SubaddAux.regroup (Fin k) (Fin n → b) (Fin c.dB)) (cqState c N)) =
      QAlgorithms.traceRight (cqState c N) ⊗ₖ
        QAlgorithms.traceLeft (QAlgorithms.traceLeft (cqState c N)) :=
  cq_prod hk (outState c N) _ (outState_tl c N) (by rw [SubaddAux.trace_tr_left, trace_pure _ c.norm_Ψ])

open scoped ComplexOrder in
lemma psd_pure {ι : Type*} [Fintype ι] (Ψ : EuclideanSpace ℂ ι) :
    (QAlgorithms.pureDensity Ψ).PosSemidef := by
  have e : QAlgorithms.pureDensity Ψ =
      (Matrix.of fun i (_ : Unit) => Ψ i) * (Matrix.of fun i (_ : Unit) => Ψ i)ᴴ := by
    ext i j
    simp [QAlgorithms.pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e]; exact Matrix.posSemidef_self_mul_conjTranspose _

open scoped ComplexOrder in
lemma psd_leftApply {ι a b r : Type} [Fintype ι] [Fintype a] [Fintype b] [Fintype r] [DecidableEq r]
    (K : ι → Matrix b a ℂ) {X : Matrix (a × r) (a × r) ℂ} (hX : X.PosSemidef) :
    (leftApply K X).PosSemidef := by
  unfold leftApply
  exact Matrix.posSemidef_sum _ (fun i _ => hX.mul_mul_conjTranspose_same _)

open scoped ComplexOrder in
lemma psd_single_kron {k : ℕ} {B : Type*} [Fintype B] [DecidableEq B] (m : Fin k)
    {ρ : Matrix B B ℂ} (hρ : ρ.PosSemidef) :
    (Matrix.single m m (1 : ℂ) ⊗ₖ ρ).PosSemidef := by
  have e : Matrix.single m m (1 : ℂ) ⊗ₖ ρ =
      (Matrix.of fun (p : Fin k × B) (b : B) => if p = (m, b) then (1 : ℂ) else 0) * ρ *
        (Matrix.of fun (p : Fin k × B) (b : B) => if p = (m, b) then (1 : ℂ) else 0)ᴴ := by
    ext ⟨m1, b1⟩ ⟨m2, b2⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.single_apply, Matrix.mul_apply, Matrix.of_apply,
      Matrix.conjTranspose_apply, Prod.mk.injEq]
    by_cases h1 : m1 = m <;> by_cases h2 : m2 = m <;> simp [h1, h2] <;> intros <;> simp_all
  rw [e]; exact hρ.mul_mul_conjTranspose_same _

open scoped ComplexOrder in
theorem cqState_psd {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {n k : ℕ} (c : EACode a b n k) (N : QChannel a b) : (cqState c N).PosSemidef := by
  unfold cqState
  have hk : (0 : ℂ) ≤ 1 / (k : ℂ) := by
    rw [show (1 : ℂ) / k = ((1 / k : ℝ) : ℂ) by push_cast; ring]
    exact Complex.zero_le_real.mpr (by positivity)
  refine Matrix.posSemidef_sum _ (fun m _ => (psd_single_kron m ?_).smul hk)
  exact psd_leftApply _ (psd_leftApply _ (psd_pure _))

theorem cqState_trace {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {n k : ℕ} (hk : 0 < k) (c : EACode a b n k) (N : QChannel a b) : (cqState c N).trace = 1 := by
  unfold cqState
  have ho : ∀ m, (outState c N m).trace = 1 := fun m => by
    rw [← SubaddAux.trace_tr_left, outState_tl, SubaddAux.trace_tr_left, trace_pure _ c.norm_Ψ]
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_kronecker, ho, Matrix.trace_single_eq_same,
    mul_one, smul_eq_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- D3a for the code state: `I(M; Bⁿ T_B)_ω ≤ I(M T_B; Bⁿ)_ω`. -/
theorem d3a_cq {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {n k : ℕ} (hk : 0 < k) (c : EACode a b n k) (N : QChannel a b) :
    DattaDiscord.mutualInfo (cqState c N) ≤
      DattaDiscord.mutualInfo (Matrix.reindex (SubaddAux.regroup (Fin k) (Fin n → b) (Fin c.dB))
        (SubaddAux.regroup (Fin k) (Fin n → b) (Fin c.dB)) (cqState c N)) :=
  SubaddAux.mi_le_regroup _ (cqState_psd c N) (cqState_trace hk c N) (cqState_prod hk c N)

end EAConv

/-! ## D3b (generic): `I(Z;B)` of `(id ⊗ N)(σ)` is at most `I(N)` (purify, drop the purifier by SSA). -/
namespace DG
open Matrix SubaddAux WildeQIT WildeQIT.EADamping
open scoped Kronecker ComplexOrder

lemma mi_reindex {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    (e1 : A ≃ A') (e2 : B ≃ B') {M : Matrix (A × B) (A × B) ℂ} (hM : M.IsHermitian) :
    DattaDiscord.mutualInfo (reindex (e1.prodCongr e2) (e1.prodCongr e2) M) =
      DattaDiscord.mutualInfo M := by
  have h1 : QAlgorithms.traceRight (reindex (e1.prodCongr e2) (e1.prodCongr e2) M) =
      reindex e1 e1 (QAlgorithms.traceRight M) := by
    ext i j
    simp only [QAlgorithms.traceRight, reindex_apply, submatrix_apply, Matrix.of_apply,
      Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map]
    exact Fintype.sum_equiv e2.symm _ _ (fun _ => rfl)
  have h2 : QAlgorithms.traceLeft (reindex (e1.prodCongr e2) (e1.prodCongr e2) M) =
      reindex e2 e2 (QAlgorithms.traceLeft M) := by
    ext i j
    simp only [QAlgorithms.traceLeft, reindex_apply, submatrix_apply, Matrix.of_apply,
      Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map]
    exact Fintype.sum_equiv e1.symm _ _ (fun _ => rfl)
  unfold DattaDiscord.mutualInfo
  rw [h1, h2, vn_reindex _ (herm_tr_right hM), vn_reindex _ (herm_tr_left hM), vn_reindex _ hM]

lemma mi_swap {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {M : Matrix (A × B) (A × B) ℂ} (hM : M.IsHermitian) :
    DattaDiscord.mutualInfo (reindex (Equiv.prodComm A B) (Equiv.prodComm A B) M) =
      DattaDiscord.mutualInfo M := by
  have h1 : QAlgorithms.traceRight (reindex (Equiv.prodComm A B) (Equiv.prodComm A B) M) =
      QAlgorithms.traceLeft M := by
    ext i j; simp [QAlgorithms.traceRight, QAlgorithms.traceLeft, reindex_apply]
  have h2 : QAlgorithms.traceLeft (reindex (Equiv.prodComm A B) (Equiv.prodComm A B) M) =
      QAlgorithms.traceRight M := by
    ext i j; simp [QAlgorithms.traceRight, QAlgorithms.traceLeft, reindex_apply]
  unfold DattaDiscord.mutualInfo
  rw [h1, h2, vn_reindex _ hM]; ring

lemma psd_idT {r a b : Type} [Fintype r] [DecidableEq r] [Fintype a] [Fintype b] [DecidableEq a]
    (N : QChannel a b) {X : Matrix (r × a) (r × a) ℂ} (hX : X.PosSemidef) :
    (idTensorApply N X).PosSemidef := by
  unfold idTensorApply
  exact Matrix.posSemidef_sum _ (fun i _ => hX.mul_mul_conjTranspose_same _)

/-- A channel on the last factor commutes with the partial trace over the first factor. -/
lemma idT_trR {R z a b : Type} [Fintype R] [DecidableEq R] [Fintype z] [DecidableEq z]
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (N : QChannel a b)
    (X : Matrix ((R × z) × a) ((R × z) × a) ℂ) :
    QAlgorithms.traceLeft (reindex (Equiv.prodAssoc R z b) (Equiv.prodAssoc R z b)
        (idTensorApply N X)) =
      idTensorApply N (QAlgorithms.traceLeft
        (reindex (Equiv.prodAssoc R z a) (Equiv.prodAssoc R z a) X)) := by
  ext ⟨z1, b1⟩ ⟨z2, b2⟩
  simp only [idTensorApply, QAlgorithms.traceLeft, reindex_apply, submatrix_apply, Matrix.of_apply,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Equiv.prodAssoc_symm_apply, Matrix.one_apply, Prod.mk.injEq]
  simp only [ite_mul, one_mul, zero_mul, apply_ite (star : ℂ → ℂ), star_zero, mul_ite, mul_zero,
    ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a2 _
  rw [Finset.sum_comm]

/-- A relabelling of the reference commutes with a channel on the last factor. -/
lemma idT_reindex {r r' a b : Type} [Fintype r] [DecidableEq r] [Fintype r'] [DecidableEq r']
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (N : QChannel a b) (e : r ≃ r')
    (X : Matrix (r × a) (r × a) ℂ) :
    idTensorApply N (reindex (e.prodCongr (Equiv.refl a)) (e.prodCongr (Equiv.refl a)) X) =
      reindex (e.prodCongr (Equiv.refl b)) (e.prodCongr (Equiv.refl b)) (idTensorApply N X) := by
  ext ⟨r1, b1⟩ ⟨r2, b2⟩
  simp only [idTensorApply, reindex_apply, submatrix_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map, Equiv.refl_symm, Equiv.refl_apply,
    Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, star_zero, star_one,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero,
    Finset.sum_ite_irrel]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [Equiv.apply_eq_iff_eq]

lemma norm_of_trace {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι)
    (h : (QAlgorithms.pureDensity v).trace = 1) : ‖v‖ = 1 := by
  have e : (QAlgorithms.pureDensity v).trace = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Matrix.trace, Matrix.diag, QAlgorithms.pureDensity, Matrix.of_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e] at h
  have h2 : ‖v‖ ^ 2 = 1 := by exact_mod_cast h
  have := norm_nonneg v
  nlinarith

/-- **D3b (generic)**. Strong subadditivity (`hssa`, in mutual-information form) and the
existence of purifications (`hpur`) give `I(Z;B)_{(id⊗N)σ} ≤ I(N)` for every state `σ` on `Z × A′`. -/
theorem mi_le_channelMI
    (hpur : ∀ {S : Type} [Fintype S] [DecidableEq S] {ρ : Matrix S S ℂ}, ρ.PosSemidef →
      ∃ ψ : EuclideanSpace ℂ (S × S), QAlgorithms.traceLeft (QAlgorithms.pureDensity ψ) = ρ)
    (hssa : ∀ {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
      [Fintype C] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
      (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ), ρ.PosSemidef →
      DattaDiscord.mutualInfo (QAlgorithms.traceRight
        (reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm ρ)) ≤
        DattaDiscord.mutualInfo ρ)
    (hbdd : ∀ {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
      (N : QChannel a b), BddAbove (Set.range fun φ : WildeQIT.Degradable.PureInput a =>
        DattaDiscord.mutualInfo (idTensorApply N (QAlgorithms.pureDensity φ.ψ))))
    {z a b : Type} [Fintype z] [DecidableEq z] [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) (σ : Matrix (z × a) (z × a) ℂ) (hσ : σ.PosSemidef)
    (htr : σ.trace = 1) :
    DattaDiscord.mutualInfo (idTensorApply N σ) ≤ channelMutualInfo N := by
  have hza : Nonempty (z × a) := by
    by_contra h; rw [not_nonempty_iff] at h; simp [Matrix.trace] at htr
  have hz : Nonempty z := ⟨hza.some.1⟩
  have ha : Nonempty a := ⟨hza.some.2⟩
  have hb : Nonempty b := by
    by_contra h; rw [not_nonempty_iff] at h
    have h1 := N.complete
    have h0 : ∀ i, N.K i = 0 := fun i => Subsingleton.elim _ _
    simp [h0] at h1
  obtain ⟨ψ, hψ⟩ := hpur hσ
  -- the purified input on `((z × a) × z) × a`, with `(z × a) = z × a`
  set X' : Matrix (((z × a) × z) × a) (((z × a) × z) × a) ℂ :=
    reindex (Equiv.prodAssoc (z × a) z a).symm (Equiv.prodAssoc (z × a) z a).symm (QAlgorithms.pureDensity ψ)
    with hX'
  have hX'psd : X'.PosSemidef := by
    rw [hX', reindex_apply]; exact (posSemidef_submatrix_equiv _).mpr (EAConv.psd_pure ψ)
  have hσX : QAlgorithms.traceLeft (reindex (Equiv.prodAssoc (z × a) z a) (Equiv.prodAssoc (z × a) z a) X') = σ := by
    rw [hX', ← hψ]; congr 1
  set Y := idTensorApply N X' with hY
  have hYpsd : Y.PosSemidef := psd_idT N hX'psd
  -- SSA drops the purifier
  have hSSA : DattaDiscord.mutualInfo (idTensorApply N σ) ≤ DattaDiscord.mutualInfo Y := by
    set ρ := reindex ((Equiv.refl b).prodCongr (Equiv.prodComm (z × a) z))
      ((Equiv.refl b).prodCongr (Equiv.prodComm (z × a) z))
      (reindex (Equiv.prodComm ((z × a) × z) b) (Equiv.prodComm ((z × a) × z) b) Y) with hρ
    have hρpsd : ρ.PosSemidef := by
      rw [hρ, reindex_apply, reindex_apply]
      exact (posSemidef_submatrix_equiv _).mpr ((posSemidef_submatrix_equiv _).mpr hYpsd)
    have h1 := hssa ρ hρpsd
    have hL : QAlgorithms.traceRight (reindex (Equiv.prodAssoc b z (z × a)).symm (Equiv.prodAssoc b z (z × a)).symm ρ) =
        reindex (Equiv.prodComm z b) (Equiv.prodComm z b)
          (QAlgorithms.traceLeft (reindex (Equiv.prodAssoc (z × a) z b) (Equiv.prodAssoc (z × a) z b) Y)) := by
      ext i j; simp [hρ, QAlgorithms.traceRight, QAlgorithms.traceLeft, reindex_apply]
    have hTherm : (QAlgorithms.traceLeft (reindex (Equiv.prodAssoc (z × a) z b) (Equiv.prodAssoc (z × a) z b) Y)).IsHermitian :=
      herm_tr_left (hYpsd.1.submatrix _)
    rw [hL, mi_swap hTherm, hY, idT_trR, hσX] at h1
    have hR : DattaDiscord.mutualInfo ρ = DattaDiscord.mutualInfo Y := by
      rw [hρ, mi_reindex (Equiv.refl b) (Equiv.prodComm (z × a) z)
        (by rw [reindex_apply]; exact hYpsd.1.submatrix _), mi_swap hYpsd.1]
    rw [hR] at h1
    exact h1
  -- relabel the reference `(z × a) × z` as `Fin m`
  set e := Fintype.equivFin ((z × a) × z)
  set ψ'' : EuclideanSpace ℂ (Fin (Fintype.card ((z × a) × z)) × a) :=
    WithLp.toLp 2 (fun p => ψ ((e.symm p.1).1, ((e.symm p.1).2, p.2))) with hψ''
  have hpure : QAlgorithms.pureDensity ψ'' =
      reindex (e.prodCongr (Equiv.refl a)) (e.prodCongr (Equiv.refl a)) X' := by
    ext i j; simp [hψ'', hX', QAlgorithms.pureDensity, reindex_apply]
  have hn : ‖ψ''‖ = 1 := by
    apply norm_of_trace
    have htψ : (QAlgorithms.pureDensity ψ).trace = 1 := by rw [← trace_tr_left, hψ, htr]
    have hT : ∀ {m n : Type} [Fintype m] [Fintype n] (f : m ≃ n) (M : Matrix m m ℂ),
        (reindex f f M).trace = M.trace := by
      intro m n _ _ f M
      simp only [Matrix.trace, Matrix.diag, reindex_apply, submatrix_apply]
      exact Fintype.sum_equiv f.symm _ _ (fun _ => rfl)
    rw [hpure, hT, hX', hT, htψ]
  have hle := le_ciSup (hbdd N) ⟨_, ψ'', hn⟩
  have hmi : DattaDiscord.mutualInfo (idTensorApply N (QAlgorithms.pureDensity ψ'')) =
      DattaDiscord.mutualInfo Y := by
    rw [hpure, idT_reindex, mi_reindex _ _ hYpsd.1]
  unfold channelMutualInfo
  rw [hmi] at hle
  linarith

end DG

/-! ## D3b (code-specific): the code state is `(id ⊗ N^{⊗n})(σ)` after regrouping. -/
namespace DG2
open Matrix SubaddAux WildeQIT WildeQIT.EADamping
open scoped Kronecker ComplexOrder

/-- `N^{⊗n}` as a channel. -/
noncomputable def powCh {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b)
    (n : ℕ) : QChannel (Fin n → a) (Fin n → b) where
  ι := Fin n → N.ι
  K := powKraus N n
  complete := EAConv.powKraus_complete N n

lemma conj_kron {M A B : Type*} [Fintype M] [DecidableEq M] [Fintype A] [Fintype B]
    (S : Matrix M M ℂ) (Q : Matrix B A ℂ) (X : Matrix A A ℂ) :
    ((1 : Matrix M M ℂ) ⊗ₖ Q) * (S ⊗ₖ X) * ((1 : Matrix M M ℂ) ⊗ₖ Q)ᴴ = S ⊗ₖ (Q * X * Qᴴ) := by
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

lemma kron_sum {M A ι : Type*} [Fintype ι] (S : Matrix M M ℂ) (f : ι → Matrix A A ℂ) :
    S ⊗ₖ (∑ i, f i) = ∑ i, S ⊗ₖ f i := by
  ext p q
  simp [Matrix.sum_apply, kroneckerMap_apply, Finset.mul_sum]

lemma kron_leftApply {ι M a b r : Type} [Fintype ι] [Fintype M] [DecidableEq M] [Fintype a]
    [Fintype b] [Fintype r] [DecidableEq r] (S : Matrix M M ℂ) (K : ι → Matrix b a ℂ)
    (X : Matrix (a × r) (a × r) ℂ) :
    S ⊗ₖ leftApply K X = ∑ i, ((1 : Matrix M M ℂ) ⊗ₖ (K i ⊗ₖ (1 : Matrix r r ℂ))) * (S ⊗ₖ X) *
      ((1 : Matrix M M ℂ) ⊗ₖ (K i ⊗ₖ (1 : Matrix r r ℂ)))ᴴ := by
  unfold leftApply
  rw [kron_sum]
  simp_rw [conj_kron]

lemma reindex_sum' {α β ι : Type*} [Fintype ι] (e : α ≃ β) (f : ι → Matrix α α ℂ) :
    reindex e e (∑ i, f i) = ∑ i, reindex e e (f i) := by
  ext p q; simp [Matrix.sum_apply]

lemma reindex_smul' {α β : Type*} (e : α ≃ β) (c : ℂ) (X : Matrix α α ℂ) :
    reindex e e (c • X) = c • reindex e e X := by
  ext p q; simp

lemma reg_kron {M A B T : Type*} [Fintype M] [DecidableEq M] [Fintype A] [Fintype B] [Fintype T]
    [DecidableEq T] (K : Matrix B A ℂ) :
    reindex (regroup M B T) (regroup M A T) ((1 : Matrix M M ℂ) ⊗ₖ (K ⊗ₖ (1 : Matrix T T ℂ))) =
      (1 : Matrix (M × T) (M × T) ℂ) ⊗ₖ K := by
  ext ⟨⟨m, t⟩, y⟩ ⟨⟨m', t'⟩, x⟩
  simp only [reindex_apply, submatrix_apply, kroneckerMap_apply, one_apply, regroup,
    Equiv.symm_trans_apply, Equiv.prodAssoc_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Equiv.refl_symm, Equiv.prodComm_symm, Prod.map, Equiv.refl_apply, Equiv.prodComm_apply,
    Prod.swap_prod_mk, Equiv.symm_symm, Prod.mk.injEq]
  by_cases h1 : m = m' <;> by_cases h2 : t = t' <;> simp [h1, h2]

lemma reg_conj {M A B T : Type*} [Fintype M] [DecidableEq M] [Fintype A] [Fintype B] [Fintype T]
    [DecidableEq T] (K : Matrix B A ℂ) (Y : Matrix (M × (A × T)) (M × (A × T)) ℂ) :
    reindex (regroup M B T) (regroup M B T)
      (((1 : Matrix M M ℂ) ⊗ₖ (K ⊗ₖ (1 : Matrix T T ℂ))) * Y *
        ((1 : Matrix M M ℂ) ⊗ₖ (K ⊗ₖ (1 : Matrix T T ℂ)))ᴴ) =
      ((1 : Matrix (M × T) (M × T) ℂ) ⊗ₖ K) * reindex (regroup M A T) (regroup M A T) Y *
        ((1 : Matrix (M × T) (M × T) ℂ) ⊗ₖ K)ᴴ := by
  rw [← reg_kron (M := M) (T := T) K, conjTranspose_reindex]
  simp only [reindex_apply, submatrix_mul_equiv]

lemma trace_reindex' {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (X : Matrix α α ℂ) :
    (reindex e e X).trace = X.trace := by
  unfold Matrix.trace
  simp only [reindex_apply, submatrix_apply, diag_apply]
  exact Equiv.sum_comp e.symm (fun i => X i i)

/-- Alice-side input state of the code: `σ_{(M T_B) A'ⁿ}`. -/
noncomputable def sigC {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {n k : ℕ} (c : EACode a b n k) :
    Matrix ((Fin k × Fin c.dB) × (Fin n → a)) ((Fin k × Fin c.dB) × (Fin n → a)) ℂ :=
  reindex (regroup (Fin k) (Fin n → a) (Fin c.dB)) (regroup (Fin k) (Fin n → a) (Fin c.dB))
    (∑ m, ((1 : ℂ) / k) • (Matrix.single m m (1 : ℂ) ⊗ₖ
      leftApply (c.enc m).K (QAlgorithms.pureDensity c.Ψ)))

theorem cq_ident {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {n k : ℕ} (c : EACode a b n k) (N : QChannel a b) :
    reindex (regroup (Fin k) (Fin n → b) (Fin c.dB)) (regroup (Fin k) (Fin n → b) (Fin c.dB))
      (EAConv.cqState c N) = idTensorApply (powCh N n) (sigC c) := by
  unfold EAConv.cqState EAConv.outState sigC idTensorApply
  simp only [kron_leftApply _ (powKraus N n), Finset.smul_sum, reindex_sum', reindex_smul',
    reg_conj, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [Finset.sum_comm]
  rfl

theorem sigC_psd {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {n k : ℕ} (c : EACode a b n k) : (sigC c).PosSemidef := by
  unfold sigC
  rw [reindex_apply]
  refine (posSemidef_submatrix_equiv _).mpr ?_
  have hk : (0 : ℂ) ≤ 1 / (k : ℂ) := by
    rw [show (1 : ℂ) / k = ((1 / k : ℝ) : ℂ) by push_cast; ring]
    exact Complex.zero_le_real.mpr (by positivity)
  refine Matrix.posSemidef_sum _ (fun m _ => (EAConv.psd_single_kron m ?_).smul hk)
  exact EAConv.psd_leftApply _ (EAConv.psd_pure _)

theorem sigC_trace {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {n k : ℕ} (hk : 0 < k) (c : EACode a b n k) : (sigC c).trace = 1 := by
  unfold sigC
  have ho : ∀ m, (leftApply (c.enc m).K (QAlgorithms.pureDensity c.Ψ)).trace = 1 := fun m => by
    rw [← SubaddAux.trace_tr_left, EAConv.tl_leftApply _ (c.enc m).complete,
      SubaddAux.trace_tr_left, EAConv.trace_pure _ c.norm_Ψ]
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [trace_reindex']
  simp only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_kronecker, ho,
    Matrix.trace_single_eq_same, mul_one, smul_eq_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

end DG2

/-! ## D3 assembly and D3c tools. -/
namespace DG3
open Matrix SubaddAux WildeQIT WildeQIT.EADamping
open scoped Kronecker ComplexOrder

/-- D3 from D3a (`d3a_cq`), the identification `cq_ident`, the generic D3b and n-fold D3c. -/
theorem d3_assembled {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (hgen : ∀ {z a' b' : Type} [Fintype z] [DecidableEq z] [Fintype a'] [Fintype b']
      [DecidableEq a'] [DecidableEq b'] (M : QChannel a' b') (σ : Matrix (z × a') (z × a') ℂ),
      σ.PosSemidef → σ.trace = 1 →
      DattaDiscord.mutualInfo (idTensorApply M σ) ≤ channelMutualInfo M)
    (N : QChannel a b) (hD3c : ∀ n : ℕ, channelMutualInfo (DG2.powCh N n) ≤ n * channelMutualInfo N)
    {n k : ℕ} (hk : 0 < k) (c : EACode a b n k) :
    DattaDiscord.mutualInfo (EAConv.cqState c N) ≤ n * channelMutualInfo N := by
  have h1 := EAConv.d3a_cq hk c N
  rw [DG2.cq_ident] at h1
  have h2 := hgen (DG2.powCh N n) (DG2.sigC c) (DG2.sigC_psd c) (DG2.sigC_trace hk c)
  have h3 := hD3c n
  linarith

lemma trR_trR_assoc {R B1 B2 : Type*} [Fintype B1] [Fintype B2]
    (ω : Matrix (R × (B1 × B2)) (R × (B1 × B2)) ℂ) :
    QAlgorithms.traceRight (QAlgorithms.traceRight
      (reindex (Equiv.prodAssoc R B1 B2).symm (Equiv.prodAssoc R B1 B2).symm ω)) =
      QAlgorithms.traceRight ω := by
  ext i j
  simp [QAlgorithms.traceRight, Fintype.sum_prod_type]

lemma trL_trR_assoc {R B1 B2 : Type*} [Fintype R] [Fintype B2]
    (ω : Matrix (R × (B1 × B2)) (R × (B1 × B2)) ℂ) :
    QAlgorithms.traceLeft (QAlgorithms.traceRight
      (reindex (Equiv.prodAssoc R B1 B2).symm (Equiv.prodAssoc R B1 B2).symm ω)) =
      QAlgorithms.traceRight (QAlgorithms.traceLeft ω) := by
  ext i j
  simp [QAlgorithms.traceRight, QAlgorithms.traceLeft, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma trL_assoc {R B1 B2 : Type*} [Fintype R] [Fintype B1]
    (ω : Matrix (R × (B1 × B2)) (R × (B1 × B2)) ℂ) :
    QAlgorithms.traceLeft
      (reindex (Equiv.prodAssoc R B1 B2).symm (Equiv.prodAssoc R B1 B2).symm ω) =
      QAlgorithms.traceLeft (QAlgorithms.traceLeft ω) := by
  ext i j
  simp [QAlgorithms.traceLeft, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- E1 (chain rule + subadditivity): `I(R;B₁B₂) ≤ I(R;B₁) + I(RB₁;B₂)`. -/
theorem mi_chain {R B1 B2 : Type} [Fintype R] [DecidableEq R] [Fintype B1] [DecidableEq B1]
    [Fintype B2] [DecidableEq B2] (ω : Matrix (R × (B1 × B2)) (R × (B1 × B2)) ℂ)
    (hω : ω.PosSemidef) (htr : ω.trace = 1) :
    DattaDiscord.mutualInfo ω ≤
      DattaDiscord.mutualInfo (QAlgorithms.traceRight
        (reindex (Equiv.prodAssoc R B1 B2).symm (Equiv.prodAssoc R B1 B2).symm ω)) +
      DattaDiscord.mutualInfo
        (reindex (Equiv.prodAssoc R B1 B2).symm (Equiv.prodAssoc R B1 B2).symm ω) := by
  unfold DattaDiscord.mutualInfo
  rw [trR_trR_assoc, trL_trR_assoc, trL_assoc, vn_reindex _ hω.1]
  have hB := psd_tr_left hω
  have htB : (QAlgorithms.traceLeft ω).trace = 1 := by rw [trace_tr_left, htr]
  have h := subadd (QAlgorithms.traceLeft ω) hB htB
  linarith

end DG3

/-! ## D3c: `I(N^{⊗n}) ≤ n · I(N)` (state form by induction, chain rule + one-channel bound). -/
namespace DG4
open Matrix SubaddAux WildeQIT WildeQIT.EADamping
open scoped Kronecker ComplexOrder

/-- `(Fin (n+1) → β) ≃ β × (Fin n → β)`, head and tail. -/
def eS (n : ℕ) (β : Type) : (Fin (n + 1) → β) ≃ β × (Fin n → β) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp

lemma tr_right_sum {α β ι : Type*} [Fintype β] [Fintype ι] (Y : ι → Matrix (α × β) (α × β) ℂ) :
    QAlgorithms.traceRight (∑ i, Y i) = ∑ i, QAlgorithms.traceRight (Y i) := by
  ext x x'
  simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.sum_apply]
  exact Finset.sum_comm

lemma tr_right_cyc {a b r : Type*} [Fintype a] [Fintype b] [Fintype r] [DecidableEq r]
    (A : Matrix b a ℂ) (Y : Matrix (r × a) (r × b) ℂ) :
    QAlgorithms.traceRight (((1 : Matrix r r ℂ) ⊗ₖ A) * Y) =
      QAlgorithms.traceRight (Y * ((1 : Matrix r r ℂ) ⊗ₖ A)) := by
  ext s s'
  simp [QAlgorithms.traceRight, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

lemma compl_one {z a b ι : Type} [Fintype z] [DecidableEq z] [Fintype a] [DecidableEq a]
    [Fintype b] [Fintype ι] (K : ι → Matrix b a ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1) :
    ∑ i, ((1 : Matrix z z ℂ) ⊗ₖ K i)ᴴ * ((1 : Matrix z z ℂ) ⊗ₖ K i) = 1 := by
  have hk : ∀ i, ((1 : Matrix z z ℂ) ⊗ₖ K i)ᴴ * ((1 : Matrix z z ℂ) ⊗ₖ K i) =
      (1 : Matrix z z ℂ) ⊗ₖ ((K i)ᴴ * K i) := by
    intro i
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul]
  simp_rw [hk]
  have : ∑ i, (1 : Matrix z z ℂ) ⊗ₖ ((K i)ᴴ * K i) =
      (1 : Matrix z z ℂ) ⊗ₖ (∑ i, (K i)ᴴ * K i) := by
    ext p q
    simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]
  rw [this, hK, Matrix.one_kronecker_one]

lemma tr_right_idTensor {r a b : Type} [Fintype r] [DecidableEq r] [Fintype a] [Fintype b]
    [DecidableEq a] (N : QChannel a b) (X : Matrix (r × a) (r × a) ℂ) :
    QAlgorithms.traceRight (idTensorApply N X) = QAlgorithms.traceRight X := by
  have hk : ∀ i, ((1 : Matrix r r ℂ) ⊗ₖ N.K i)ᴴ * ((1 : Matrix r r ℂ) ⊗ₖ N.K i) =
      (1 : Matrix r r ℂ) ⊗ₖ ((N.K i)ᴴ * N.K i) := by
    intro i
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul]
  have hs : ∑ i, (1 : Matrix r r ℂ) ⊗ₖ ((N.K i)ᴴ * N.K i) = 1 := by
    have : ∑ i, (1 : Matrix r r ℂ) ⊗ₖ ((N.K i)ᴴ * N.K i) =
        (1 : Matrix r r ℂ) ⊗ₖ (∑ i, (N.K i)ᴴ * N.K i) := by
      ext p q
      simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]
    rw [this, N.complete, Matrix.one_kronecker_one]
  unfold idTensorApply
  rw [tr_right_sum]
  have e : ∀ i, QAlgorithms.traceRight (((1 : Matrix r r ℂ) ⊗ₖ N.K i) * X *
      ((1 : Matrix r r ℂ) ⊗ₖ N.K i)ᴴ)
      = QAlgorithms.traceRight (X * ((1 : Matrix r r ℂ) ⊗ₖ ((N.K i)ᴴ * N.K i))) := by
    intro i
    rw [Matrix.mul_assoc, tr_right_cyc, Matrix.mul_assoc, hk]
  simp_rw [e, ← tr_right_sum, ← Matrix.mul_sum, hs, Matrix.mul_one]

lemma trace_idT {r a b : Type} [Fintype r] [DecidableEq r] [Fintype a] [Fintype b]
    [DecidableEq a] (N : QChannel a b) (X : Matrix (r × a) (r × a) ℂ) :
    (idTensorApply N X).trace = X.trace := by
  rw [← SubaddAux.trace_tr_right, tr_right_idTensor, SubaddAux.trace_tr_right]

lemma tr_right_kron_conj {p q r : Type} [Fintype q] [Fintype r] [DecidableEq r]
    (A : Matrix p q ℂ) (X : Matrix (q × r) (q × r) ℂ) :
    QAlgorithms.traceRight ((A ⊗ₖ (1 : Matrix r r ℂ)) * X * (A ⊗ₖ (1 : Matrix r r ℂ))ᴴ) =
      A * QAlgorithms.traceRight X * Aᴴ := by
  ext i j
  simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, star_zero,
    apply_ite (star : ℂ → ℂ), Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const_zero]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x' _ => ?_)
  rw [Finset.sum_comm]

lemma reindex_conj {m m' n n' : Type} [Fintype n] [Fintype n'] (f : m ≃ m') (g : n ≃ n')
    (A : Matrix m n ℂ) (X : Matrix n n ℂ) :
    reindex f f (A * X * Aᴴ) = reindex f g A * reindex g g X * (reindex f g A)ᴴ := by
  rw [conjTranspose_reindex]
  simp only [reindex_apply, submatrix_mul_equiv]

/-- Splitting the first copy off `N^{⊗(n+1)}` at the Kraus level. -/
lemma kr_split {z a b : Type} [Fintype z] [DecidableEq z] [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) (n : ℕ) (i : Fin (n + 1) → N.ι) :
    reindex (Equiv.prodAssoc z b (Fin n → b)).symm (Equiv.prodAssoc z a (Fin n → a)).symm
      (reindex ((Equiv.refl z).prodCongr (eS n b)) ((Equiv.refl z).prodCongr (eS n a))
        ((1 : Matrix z z ℂ) ⊗ₖ powKraus N (n + 1) i)) =
      ((1 : Matrix (z × b) (z × b) ℂ) ⊗ₖ powKraus N n (Fin.tail i)) *
        (((1 : Matrix z z ℂ) ⊗ₖ N.K (i 0)) ⊗ₖ (1 : Matrix (Fin n → a) (Fin n → a) ℂ)) := by
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  ext ⟨⟨z1, b1⟩, t1⟩ ⟨⟨z2, a2⟩, u2⟩
  simp [eS, reindex_apply, kroneckerMap_apply, powKraus, Fin.prod_univ_succ, Fin.tail,
    Matrix.one_apply]

lemma idT_powCh {z a b : Type} [Fintype z] [DecidableEq z] [Fintype a] [Fintype b]
    [DecidableEq a] (N : QChannel a b) (n : ℕ) (X : Matrix (z × (Fin n → a)) (z × (Fin n → a)) ℂ) :
    idTensorApply (DG2.powCh N n) X = ∑ i : Fin n → N.ι,
      ((1 : Matrix z z ℂ) ⊗ₖ powKraus N n i) * X * ((1 : Matrix z z ℂ) ⊗ₖ powKraus N n i)ᴴ := rfl

/-- **F1**: `(id ⊗ N^{⊗(n+1)})σ` = tail channels applied after the head channel. -/
theorem pow_split {z a b : Type} [Fintype z] [DecidableEq z] [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (N : QChannel a b) (n : ℕ)
    (σ : Matrix (z × (Fin (n + 1) → a)) (z × (Fin (n + 1) → a)) ℂ) :
    reindex (Equiv.prodAssoc z b (Fin n → b)).symm (Equiv.prodAssoc z b (Fin n → b)).symm
      (reindex ((Equiv.refl z).prodCongr (eS n b)) ((Equiv.refl z).prodCongr (eS n b))
        (idTensorApply (DG2.powCh N (n + 1)) σ)) =
      idTensorApply (DG2.powCh N n)
        (leftApply (fun l => (1 : Matrix z z ℂ) ⊗ₖ N.K l)
          (reindex (Equiv.prodAssoc z a (Fin n → a)).symm (Equiv.prodAssoc z a (Fin n → a)).symm
            (reindex ((Equiv.refl z).prodCongr (eS n a)) ((Equiv.refl z).prodCongr (eS n a)) σ))) := by
  rw [idT_powCh, idT_powCh]
  unfold leftApply
  simp only [DG2.reindex_sum', reindex_conj ((Equiv.refl z).prodCongr (eS n b))
    ((Equiv.refl z).prodCongr (eS n a)),
    reindex_conj (Equiv.prodAssoc z b (Fin n → b)).symm (Equiv.prodAssoc z a (Fin n → a)).symm,
    kr_split]
  conv_lhs => rw [← (eS n N.ι).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun t _ => ?_))
  simp only [eS, Equiv.coe_fn_symm_mk, Fin.cons_zero, Fin.tail_cons, conjTranspose_mul,
    Matrix.mul_assoc]

/-- `S(ρ) ≤ log₂ d` (copied from PureAux). -/
theorem vn_le_log_card {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    QAlgorithms.vnEntropy ρ ≤ Real.log (Fintype.card n) / Real.log 2 := by
  have hsum : ∑ i, hρ.1.eigenvalues i = 1 := by rw [← trace_eig hρ.1, htr]; simp
  have hc : (0 : ℝ) < Fintype.card n := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h | h
    · exfalso; rw [Fintype.card_eq_zero_iff] at h; haveI := h; simp at hsum
    · exact_mod_cast h
  have hc' := hc.ne'
  rw [vn_eq hρ.1]
  refine div_le_div_of_nonneg_right ?_ (Real.log_nonneg one_le_two)
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := fun _ => (1 : ℝ) / Fintype.card n) (p := hρ.1.eigenvalues) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
    (fun i _ => Set.mem_Ici.mpr (hρ.eigenvalues_nonneg i))
  simp only [smul_eq_mul, ← Finset.mul_sum, hsum, mul_one] at hJ
  have h2 : Real.negMulLog (1 / (Fintype.card n : ℝ)) =
      1 / Fintype.card n * Real.log (Fintype.card n) := by
    simp [Real.negMulLog, Real.log_inv]
  rw [h2] at hJ
  exact le_of_mul_le_mul_left hJ (by positivity)

/-- `n = 0`: a channel into a one-point system carries no information. -/
theorem base_case {z a b : Type} [Fintype z] [DecidableEq z] [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (N : QChannel a b)
    (σ : Matrix (z × (Fin 0 → a)) (z × (Fin 0 → a)) ℂ) (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    DattaDiscord.mutualInfo (idTensorApply (DG2.powCh N 0) σ) ≤ 0 := by
  set ω := idTensorApply (DG2.powCh N 0) σ with hωdef
  have hω : ω.PosSemidef := DG.psd_idT _ hσ
  have htω : ω.trace = 1 := by rw [hωdef, trace_idT, htr]
  have hR : QAlgorithms.traceRight ω =
      reindex (Equiv.prodUnique z (Fin 0 → b)) (Equiv.prodUnique z (Fin 0 → b)) ω := by
    ext i j
    simp [QAlgorithms.traceRight, reindex_apply]
  have hB := vn_le_log_card (psd_tr_left hω) (by rw [trace_tr_left, htω])
  simp only [Fintype.card_unique, Nat.cast_one, Real.log_one, zero_div] at hB
  unfold DattaDiscord.mutualInfo
  rw [hR, vn_reindex _ hω.1]
  linarith

/-- Inductive step. -/
theorem step
    (hgen : ∀ {z a' b' : Type} [Fintype z] [DecidableEq z] [Fintype a'] [Fintype b']
      [DecidableEq a'] [DecidableEq b'] (M : QChannel a' b') (σ : Matrix (z × a') (z × a') ℂ),
      σ.PosSemidef → σ.trace = 1 →
      DattaDiscord.mutualInfo (idTensorApply M σ) ≤ channelMutualInfo M)
    {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (N : QChannel a b)
    (n : ℕ)
    (IH : ∀ {z : Type} [Fintype z] [DecidableEq z] (σ : Matrix (z × (Fin n → a)) (z × (Fin n → a)) ℂ),
      σ.PosSemidef → σ.trace = 1 →
      DattaDiscord.mutualInfo (idTensorApply (DG2.powCh N n) σ) ≤ n * channelMutualInfo N)
    {z : Type} [Fintype z] [DecidableEq z]
    (σ : Matrix (z × (Fin (n + 1) → a)) (z × (Fin (n + 1) → a)) ℂ)
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    DattaDiscord.mutualInfo (idTensorApply (DG2.powCh N (n + 1)) σ) ≤
      ((n + 1 : ℕ) : ℝ) * channelMutualInfo N := by
  set ω := idTensorApply (DG2.powCh N (n + 1)) σ with hωdef
  have hω : ω.PosSemidef := DG.psd_idT _ hσ
  have htω : ω.trace = 1 := by rw [hωdef, trace_idT, htr]
  set W := reindex ((Equiv.refl z).prodCongr (eS n b)) ((Equiv.refl z).prodCongr (eS n b)) ω
    with hWdef
  have hW : W.PosSemidef := by
    rw [hWdef, reindex_apply]; exact (posSemidef_submatrix_equiv _).mpr hω
  have htW : W.trace = 1 := by rw [hWdef, DG2.trace_reindex', htω]
  have e1 : DattaDiscord.mutualInfo ω = DattaDiscord.mutualInfo W :=
    (DG.mi_reindex (Equiv.refl z) (eS n b) hω.1).symm
  have hc := DG3.mi_chain W hW htW
  set σ'' := reindex (Equiv.prodAssoc z a (Fin n → a)).symm (Equiv.prodAssoc z a (Fin n → a)).symm
      (reindex ((Equiv.refl z).prodCongr (eS n a)) ((Equiv.refl z).prodCongr (eS n a)) σ)
    with hσ''
  have hps'' : σ''.PosSemidef := by
    rw [hσ'', reindex_apply, reindex_apply]
    exact (posSemidef_submatrix_equiv _).mpr ((posSemidef_submatrix_equiv _).mpr hσ)
  have htr'' : σ''.trace = 1 := by rw [hσ'', DG2.trace_reindex', DG2.trace_reindex', htr]
  set H := leftApply (fun l => (1 : Matrix z z ℂ) ⊗ₖ N.K l) σ'' with hHdef
  have hH : H.PosSemidef := EAConv.psd_leftApply _ hps''
  have htH : H.trace = 1 := by
    rw [hHdef, ← trace_tr_left, EAConv.tl_leftApply _ (compl_one (z := z) N.K N.complete), trace_tr_left,
      htr'']
  have key : reindex (Equiv.prodAssoc z b (Fin n → b)).symm (Equiv.prodAssoc z b (Fin n → b)).symm W =
      idTensorApply (DG2.powCh N n) H := pow_split N n σ
  rw [key] at hc
  have h2 := IH H hH htH
  have hm : QAlgorithms.traceRight (idTensorApply (DG2.powCh N n) H) =
      idTensorApply N (QAlgorithms.traceRight σ'') := by
    rw [tr_right_idTensor, hHdef]
    unfold leftApply idTensorApply
    rw [tr_right_sum]
    simp only [tr_right_kron_conj]
  rw [hm] at hc
  have h1 := hgen N (QAlgorithms.traceRight σ'') (psd_tr_right hps'')
    (by rw [SubaddAux.trace_tr_right, htr''])
  rw [e1]
  push_cast
  linarith

/-- State form of D3c. -/
theorem state_bound
    (hgen : ∀ {z a' b' : Type} [Fintype z] [DecidableEq z] [Fintype a'] [Fintype b']
      [DecidableEq a'] [DecidableEq b'] (M : QChannel a' b') (σ : Matrix (z × a') (z × a') ℂ),
      σ.PosSemidef → σ.trace = 1 →
      DattaDiscord.mutualInfo (idTensorApply M σ) ≤ channelMutualInfo M)
    {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (N : QChannel a b) :
    ∀ (n : ℕ) {z : Type} [Fintype z] [DecidableEq z]
      (σ : Matrix (z × (Fin n → a)) (z × (Fin n → a)) ℂ), σ.PosSemidef → σ.trace = 1 →
      DattaDiscord.mutualInfo (idTensorApply (DG2.powCh N n) σ) ≤ n * channelMutualInfo N := by
  intro n
  induction n with
  | zero =>
    intro z _ _ σ hσ htr
    simpa using base_case N σ hσ htr
  | succ n ih =>
    intro z _ _ σ hσ htr
    exact step hgen N n (fun σ hσ htr => ih σ hσ htr) σ hσ htr

/-- **D3c**: `I(N^{⊗n}) ≤ n · I(N)`. -/
theorem d3c
    (hgen : ∀ {z a' b' : Type} [Fintype z] [DecidableEq z] [Fintype a'] [Fintype b']
      [DecidableEq a'] [DecidableEq b'] (M : QChannel a' b') (σ : Matrix (z × a') (z × a') ℂ),
      σ.PosSemidef → σ.trace = 1 →
      DattaDiscord.mutualInfo (idTensorApply M σ) ≤ channelMutualInfo M)
    {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (N : QChannel a b)
    (n : ℕ) : channelMutualInfo (DG2.powCh N n) ≤ n * channelMutualInfo N := by
  have hC : 0 ≤ channelMutualInfo N := by
    unfold channelMutualInfo
    refine Real.iSup_nonneg (fun φ => mutualInfo_nonneg _ (DG.psd_idT _ (EAConv.psd_pure _)) ?_)
    rw [trace_idT, EAConv.trace_pure _ φ.norm_eq_one]
  unfold channelMutualInfo
  refine Real.iSup_le (fun φ => ?_) (mul_nonneg (Nat.cast_nonneg n) hC)
  exact state_bound hgen N n _ (EAConv.psd_pure _) (EAConv.trace_pure _ φ.norm_eq_one)

end DG4


set_option autoImplicit false

/-! SSA library, step 1: operator Jensen inequality for isometries (Hansen-Pedersen) for the
operator-concave logarithm, `Vᴴ log(A) V ≤ log(Vᴴ A V)` for `A > 0`, `VᴴV = 1`.
Route to SSA (Petz): relative modular operator on Hilbert-Schmidt space + this inequality. -/

namespace SSALib
open Matrix
open scoped ComplexOrder

lemma exists_poly (s : Finset ℝ) (f : ℝ → ℝ) : ∃ p : Polynomial ℝ, ∀ x ∈ s, p.eval x = f x := by
  refine ⟨Lagrange.interpolate s id f, fun x hx => ?_⟩
  have := Lagrange.eval_interpolate_at_node (s := s) (v := id) f (Set.injOn_id _) hx
  simpa using this

lemma cfc_eq_aeval {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (p : Polynomial ℝ) (f : ℝ → ℝ) (hs : ∀ x ∈ spectrum ℝ A, p.eval x = f x) :
    cfc f A = Polynomial.aeval A p := by
  rw [← cfc_polynomial p A hA.isSelfAdjoint]
  exact cfc_congr (fun x hx => (hs x hx).symm)

/-- Functional calculus respects intertwiners: `A V = V B` implies `f(A) V = V f(B)`. -/
lemma cfc_intertwine {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (V : Matrix m n ℂ) (h : A * V = V * B) (f : ℝ → ℝ) :
    cfc f A * V = V * cfc f B := by
  have fA : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  have fB : (spectrum ℝ B).Finite := Matrix.finite_real_spectrum
  obtain ⟨p, hp⟩ := exists_poly (fA.toFinset ∪ fB.toFinset) f
  rw [cfc_eq_aeval A hA p f (fun x hx => hp x (by simp [hx])),
    cfc_eq_aeval B hB p f (fun x hx => hp x (by simp [hx]))]
  have hpow : ∀ k : ℕ, A ^ k * V = V * B ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.smul_mul, Matrix.mul_smul, hpow]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- Hansen-Pedersen-Jensen for an isometry and the operator-concave `log`. -/
theorem jensen_log_iso {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (hA : A.PosDef) (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) :
    (cfc Real.log (Vᴴ * A * V) - Vᴴ * cfc Real.log A * V).PosSemidef := by
  have hVinj : Function.Injective V.mulVec := fun x y hxy => by
    have := congrArg (Vᴴ.mulVec) hxy
    simpa [Matrix.mulVec_mulVec, hV] using this
  set W : Matrix m m ℂ := (2 : ℂ) • (V * Vᴴ) - 1 with hWdef
  have hPP : V * Vᴴ * (V * Vᴴ) = V * Vᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul]
  have hWh : Wᴴ = W := by
    simp [hWdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul]
  have hWW : W * W = 1 := by
    rw [hWdef]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hPP]
    module
  have hWV : W * V = V := by
    rw [hWdef, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, hV, Matrix.mul_one, Matrix.one_mul,
      two_smul]
    abel
  have hVW : Vᴴ * W = Vᴴ := by
    have := congrArg Matrix.conjTranspose hWV
    rwa [Matrix.conjTranspose_mul, hWh] at this
  have hWinj : Function.Injective W.mulVec := fun x y hxy => by
    have := congrArg W.mulVec hxy
    simpa [Matrix.mulVec_mulVec, hWW] using this
  have hA2 : (Wᴴ * A * W).PosDef := hA.conjTranspose_mul_mul_same hWinj
  have hB : (Vᴴ * A * V).PosDef := hA.conjTranspose_mul_mul_same hVinj
  have hlogA2 : cfc Real.log (Wᴴ * A * W) = W * cfc Real.log A * W := by
    have hi := cfc_intertwine (Wᴴ * A * W) A hA2.isHermitian hA.isHermitian W
      (by rw [hWh, Matrix.mul_assoc, hWW, Matrix.mul_one]) Real.log
    calc cfc Real.log (Wᴴ * A * W) = cfc Real.log (Wᴴ * A * W) * (W * W) := by
          rw [hWW, Matrix.mul_one]
      _ = W * cfc Real.log A * W := by rw [← Matrix.mul_assoc, hi]
  have hconc := CFC.concaveOn_log.2 (x := A) (y := Wᴴ * A * W) hA.isStrictlyPositive
    hA2.isStrictlyPositive (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simp only [CFC.log] at hconc
  set A' : Matrix m m ℂ := (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • (Wᴴ * A * W) with hA'def
  have hA'V : A' * V = V * (Vᴴ * A * V) := by
    rw [hA'def, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hWh, Matrix.mul_assoc,
      Matrix.mul_assoc W, hWV, hWdef]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Complex.coe_smul, ← Complex.coe_smul]
    module
  have hA'h : A'.IsHermitian := by
    rw [hA'def]
    unfold Matrix.IsHermitian
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hA.isHermitian.eq,
      hA2.isHermitian.eq, star_trivial]
  have hi2 := cfc_intertwine A' (Vᴴ * A * V) hA'h hB.isHermitian V hA'V Real.log
  have key : Vᴴ * cfc Real.log A' * V = cfc Real.log (Vᴴ * A * V) := by
    rw [Matrix.mul_assoc, hi2, ← Matrix.mul_assoc, hV, Matrix.one_mul]
  have hleft : Vᴴ * ((1 / 2 : ℝ) • cfc Real.log A + (1 / 2 : ℝ) • cfc Real.log (Wᴴ * A * W)) * V =
      Vᴴ * cfc Real.log A * V := by
    rw [hlogA2]
    have e : Vᴴ * (W * cfc Real.log A * W) * V = Vᴴ * cfc Real.log A * V := by
      simp only [← Matrix.mul_assoc]
      rw [hVW]
      simp only [Matrix.mul_assoc]
      rw [hWV]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
      e, ← add_smul]
    norm_num
  have hps : (cfc Real.log A' - ((1 / 2 : ℝ) • cfc Real.log A +
      (1 / 2 : ℝ) • cfc Real.log (Wᴴ * A * W))).PosSemidef := by
    exact Matrix.le_iff.mp hconc
  have h3 := hps.conjTranspose_mul_mul_same V
  rw [Matrix.mul_sub, Matrix.sub_mul, key, hleft] at h3
  exact h3

/-! ## S2: logarithm of a Kronecker product -/

lemma aeval_diag {n : Type} [Fintype n] [DecidableEq n] (d : n → ℝ) (p : Polynomial ℝ) :
    Polynomial.aeval (Matrix.diagonal (fun i => (d i : ℂ))) p =
      Matrix.diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ)) := by
  ext i j
  rw [Polynomial.aeval_eq_sum_range, Matrix.sum_apply, Matrix.diagonal_apply]
  simp only [Polynomial.eval_eq_sum_range, Matrix.smul_apply, Matrix.diagonal_pow, Matrix.diagonal_apply,
    Pi.pow_apply]
  by_cases h : i = j
  · subst h
    simp only [if_true, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Complex.real_smul]
  · simp [h]

lemma herm_diag {n : Type} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma cfc_diag {n : Type} [Fintype n] [DecidableEq n] (d : n → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  have fD : (spectrum ℝ (Matrix.diagonal (fun i => (d i : ℂ)))).Finite := Matrix.finite_real_spectrum
  obtain ⟨p, hp⟩ := exists_poly (fD.toFinset ∪ Finset.univ.image d) f
  rw [cfc_eq_aeval _ (herm_diag d) p f (fun x hx => hp x (by simp [hx])), aeval_diag]
  congr 1; funext i; rw [hp (d i) (by simp)]

open scoped Kronecker in
lemma log_kron_diag {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (d : m → ℝ) (e : n → ℝ) (hd : ∀ i, 0 < d i) (he : ∀ j, 0 < e j) :
    cfc Real.log (Matrix.diagonal (fun i => (d i : ℂ)) ⊗ₖ Matrix.diagonal (fun j => (e j : ℂ))) =
      cfc Real.log (Matrix.diagonal (fun i => (d i : ℂ))) ⊗ₖ (1 : Matrix n n ℂ) +
        (1 : Matrix m m ℂ) ⊗ₖ cfc Real.log (Matrix.diagonal (fun j => (e j : ℂ))) := by
  rw [Matrix.diagonal_kronecker_diagonal]
  have h : (fun mn : m × n => (d mn.1 : ℂ) * (e mn.2 : ℂ)) = fun mn => ((d mn.1 * e mn.2 : ℝ) : ℂ) := by
    funext mn; push_cast; ring
  rw [h, cfc_diag, cfc_diag, cfc_diag, ← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal,
    ← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_add]
  congr 1; funext mn
  rw [Real.log_mul (hd mn.1).ne' (he mn.2).ne']
  push_cast; ring

lemma eig_intertwine {n : Type} [Fintype n] [DecidableEq n] {σ : Matrix n n ℂ} (hσ : σ.IsHermitian) :
    σ * (hσ.eigenvectorUnitary : Matrix n n ℂ) =
      (hσ.eigenvectorUnitary : Matrix n n ℂ) * Matrix.diagonal (fun i => ((hσ.eigenvalues i : ℝ) : ℂ)) := by
  have hs := congrArg (· * (hσ.eigenvectorUnitary : Matrix n n ℂ)) hσ.spectral_theorem
  beta_reduce at hs
  rw [hs, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]
  rfl

lemma unit_mul_star' {n : Type} [Fintype n] [DecidableEq n] {σ : Matrix n n ℂ} (hσ : σ.IsHermitian) :
    (hσ.eigenvectorUnitary : Matrix n n ℂ) * (hσ.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 :=
  Unitary.coe_mul_star_self _

open scoped Kronecker in
/-- `log(σ ⊗ τ) = log σ ⊗ 1 + 1 ⊗ log τ` for positive definite `σ, τ`. -/
theorem log_kron {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {σ : Matrix m m ℂ} {τ : Matrix n n ℂ} (hσ : σ.PosDef) (hτ : τ.PosDef) :
    cfc Real.log (σ ⊗ₖ τ) = cfc Real.log σ ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ cfc Real.log τ := by
  set U : Matrix m m ℂ := (hσ.isHermitian.eigenvectorUnitary : Matrix m m ℂ) with hU
  set W : Matrix n n ℂ := (hτ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) with hW
  set Dσ := Matrix.diagonal (fun i => ((hσ.isHermitian.eigenvalues i : ℝ) : ℂ))
  set Dτ := Matrix.diagonal (fun j => ((hτ.isHermitian.eigenvalues j : ℝ) : ℂ))
  have e1 : σ * U = U * Dσ := eig_intertwine hσ.isHermitian
  have e2 : τ * W = W * Dτ := eig_intertwine hτ.isHermitian
  have l1 := cfc_intertwine σ Dσ hσ.isHermitian (herm_diag _) U e1 Real.log
  have l2 := cfc_intertwine τ Dτ hτ.isHermitian (herm_diag _) W e2 Real.log
  have hX : (σ ⊗ₖ τ).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hσ.isHermitian.eq, hτ.isHermitian.eq]
  have hDD : (Dσ ⊗ₖ Dτ).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, (herm_diag _).eq, (herm_diag _).eq]
  have eX : σ ⊗ₖ τ * (U ⊗ₖ W) = (U ⊗ₖ W) * (Dσ ⊗ₖ Dτ) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, e1, e2]
  have lX := cfc_intertwine _ _ hX hDD (U ⊗ₖ W) eX Real.log
  rw [log_kron_diag _ _ hσ.eigenvalues_pos hτ.eigenvalues_pos] at lX
  have hZ : (U ⊗ₖ W) * (U ⊗ₖ W)ᴴ = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU, hW, unit_mul_star',
      unit_mul_star', Matrix.one_kronecker_one]
  have hL : (cfc Real.log σ ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ cfc Real.log τ) * (U ⊗ₖ W) =
      (U ⊗ₖ W) * (cfc Real.log Dσ ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ cfc Real.log Dτ) := by
    rw [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, l1, l2]
    simp only [Matrix.one_mul, Matrix.mul_one]
  calc cfc Real.log (σ ⊗ₖ τ) = cfc Real.log (σ ⊗ₖ τ) * ((U ⊗ₖ W) * (U ⊗ₖ W)ᴴ) := by
        rw [hZ, Matrix.mul_one]
    _ = (cfc Real.log σ ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ cfc Real.log τ) *
          ((U ⊗ₖ W) * (U ⊗ₖ W)ᴴ) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, lX, hL]
    _ = _ := by rw [hZ, Matrix.mul_one]

section Index
open scoped Kronecker
variable {X C : Type} [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

/-- Partial trace over the second factor. -/
def ptrC (M : Matrix (X × C) (X × C) ℂ) : Matrix X X ℂ := fun x y => ∑ c, M (x, c) (y, c)

/-- Row-major vectorisation. -/
def vecM {I : Type} (Y : Matrix I I ℂ) : I × I → ℂ := fun p => Y p.1 p.2

/-- The Petz isometry `vec Y ↦ vec ((Y ⊗ 1) T)`. -/
def Vmat (T : Matrix (X × C) (X × C) ℂ) : Matrix ((X × C) × (X × C)) (X × X) ℂ :=
  fun p a => if p.1.1 = a.1 then T (a.2, p.1.2) p.2 else 0

lemma kron_mulVec_vec {I : Type} [Fintype I] [DecidableEq I] (A B Y : Matrix I I ℂ) :
    (A ⊗ₖ Bᵀ) *ᵥ vecM Y = vecM (A * Y * B) := by
  funext p
  simp only [mulVec, dotProduct, vecM, kroneckerMap_apply, transpose_apply, mul_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

lemma dot_vec {I : Type} [Fintype I] [DecidableEq I] (Y Z : Matrix I I ℂ) :
    star (vecM Y) ⬝ᵥ vecM Z = trace (Yᴴ * Z) := by
  simp only [dotProduct, vecM, trace, diag, mul_apply, conjTranspose_apply, Pi.star_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

lemma qf_kron {I : Type} [Fintype I] [DecidableEq I] (A B Y : Matrix I I ℂ) :
    star (vecM Y) ⬝ᵥ ((A ⊗ₖ Bᵀ) *ᵥ vecM Y) = trace (Yᴴ * A * Y * B) := by
  rw [kron_mulVec_vec, dot_vec]; simp only [Matrix.mul_assoc]

lemma V_sandwich (T : Matrix (X × C) (X × C) ℂ)
    (M : Matrix ((X × C) × (X × C)) ((X × C) × (X × C)) ℂ) (a b : X × X) :
    ((Vmat T)ᴴ * M * Vmat T) a b =
      ∑ c', ∑ q', ∑ c, ∑ q, star (T (a.2, c) q) * M ((a.1, c), q) ((b.1, c'), q') * T (b.2, c') q' := by
  simp only [mul_apply, conjTranspose_apply, Vmat, Fintype.sum_prod_type, apply_ite star, star_zero,
    ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  skip

lemma VtV (T : Matrix (X × C) (X × C) ℂ) (h : ptrC (T * Tᴴ) = 1) : (Vmat T)ᴴ * Vmat T = 1 := by
  ext a b
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  have h2 := congrFun (congrFun h b2) a2
  simp only [ptrC, mul_apply, conjTranspose_apply] at h2
  simp only [mul_apply, conjTranspose_apply, Vmat, Fintype.sum_prod_type, apply_ite star, star_zero,
    ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h3 : ∑ x, ∑ x_1, ∑ x_2, star (T (a2, x) (x_1, x_2)) * T (b2, x) (x_1, x_2) = (1 : Matrix X X ℂ) b2 a2 := by
    rw [← h2]; simp only [Fintype.sum_prod_type, mul_comm]
  rw [h3]
  by_cases h1 : b1 = a1
  · subst h1
    by_cases h4 : b2 = a2
    · subst h4; simp
    · simp [one_apply, h4, Ne.symm h4]
  · simp [one_apply, h1, Ne.symm h1]

lemma VtDV (T Q : Matrix (X × C) (X × C) ℂ) (σ : Matrix (X × C) (X × C) ℂ) (P : Matrix X X ℂ)
    (h : T * Q * Tᴴ = P ⊗ₖ (1 : Matrix C C ℂ)) :
    (Vmat T)ᴴ * (σ ⊗ₖ Qᵀ) * Vmat T = ptrC σ ⊗ₖ Pᵀ := by
  ext a b
  rw [V_sandwich]
  simp only [kroneckerMap_apply, transpose_apply, ptrC]
  have h2 : ∀ c c', ∑ q', ∑ q, star (T (a.2, c) q) * Q q' q * T (b.2, c') q' =
      P b.2 a.2 * (1 : Matrix C C ℂ) c' c := by
    intro c c'
    have := congrFun (congrFun h (b.2, c')) (a.2, c)
    simp only [mul_apply, conjTranspose_apply, kroneckerMap_apply] at this
    rw [← this, Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q' _ => by ring
  calc ∑ c', ∑ q', ∑ c, ∑ q, star (T (a.2, c) q) * (σ (a.1, c) (b.1, c') * Q q' q) * T (b.2, c') q'
      = ∑ c', ∑ c, σ (a.1, c) (b.1, c') * (∑ q', ∑ q, star (T (a.2, c) q) * Q q' q * T (b.2, c') q') := by
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => by ring
    _ = (∑ c, σ (a.1, c) (b.1, c)) * P b.2 a.2 := by
        simp only [h2, one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
          Finset.mem_univ, if_true, Finset.sum_mul]

lemma V_vec (T : Matrix (X × C) (X × C) ℂ) (P : Matrix X X ℂ) :
    Vmat T *ᵥ vecM P = vecM ((P ⊗ₖ (1 : Matrix C C ℂ)) * T) := by
  funext p
  obtain ⟨⟨x, c⟩, q⟩ := p
  simp only [mulVec, dotProduct, vecM, Vmat, mul_apply, kroneckerMap_apply, one_apply,
    Fintype.sum_prod_type, ite_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  refine Finset.sum_congr rfl fun z _ => by ring

lemma ptr_sandwich (A B : Matrix X X ℂ) (M : Matrix (X × C) (X × C) ℂ) :
    ptrC ((A ⊗ₖ (1 : Matrix C C ℂ)) * M * (B ⊗ₖ (1 : Matrix C C ℂ))) = A * ptrC M * B := by
  ext x y
  simp only [ptrC, mul_apply, kroneckerMap_apply, one_apply, Fintype.sum_prod_type, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_comm]

end Index

section Petz
open scoped Kronecker

lemma cfc_unitary_diag {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (U : Matrix n n ℂ) (hU : U * Uᴴ = 1) (d : n → ℝ)
    (h : A * U = U * Matrix.diagonal (fun i => (d i : ℂ))) (f : ℝ → ℝ) :
    cfc f A = U * Matrix.diagonal (fun i => (f (d i) : ℂ)) * Uᴴ := by
  have l := cfc_intertwine A _ hA (herm_diag d) U h f
  rw [cfc_diag] at l
  calc cfc f A = cfc f A * (U * Uᴴ) := by rw [hU, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, l]

lemma cfc_eig {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ :=
  cfc_unitary_diag A hA _ (unit_mul_star' hA) (fun i => hA.eigenvalues i) (eig_intertwine hA) f

lemma cfc_mul_cfc {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (f g : ℝ → ℝ) : cfc f A * cfc g A = cfc (fun x => f x * g x) A := by
  have hUU' : (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  rw [cfc_eig A hA f, cfc_eig A hA g, cfc_eig A hA (fun x => f x * g x)]
  calc _ = (hA.eigenvectorUnitary : Matrix n n ℂ) * Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) *
        ((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix n n ℂ)) *
        Matrix.diagonal (fun i => (g (hA.eigenvalues i) : ℂ)) * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
          simp only [Matrix.mul_assoc]
    _ = _ := by
          rw [hUU', Matrix.mul_one, Matrix.mul_assoc _ (Matrix.diagonal _) (Matrix.diagonal _),
            Matrix.diagonal_mul_diagonal]
          simp only [Complex.ofReal_mul]

lemma cfc_congr_pos {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.PosDef)
    (f g : ℝ → ℝ) (h : ∀ x, 0 < x → f x = g x) : cfc f A = cfc g A := by
  rw [cfc_eig A hA.isHermitian f, cfc_eig A hA.isHermitian g]
  have : (fun i => (f (hA.isHermitian.eigenvalues i) : ℂ)) = fun i => (g (hA.isHermitian.eigenvalues i) : ℂ) :=
    funext fun i => by rw [h _ (hA.eigenvalues_pos i)]
  rw [this]

lemma cfc_const_one' {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    cfc (fun _ : ℝ => (1 : ℝ)) A = 1 := by
  rw [cfc_eig A hA]
  simp only [Complex.ofReal_one]
  rw [Matrix.diagonal_one, Matrix.mul_one]
  exact unit_mul_star' hA

lemma herm_cfc {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A)ᴴ = cfc f A := by
  rw [cfc_eig A hA f]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose,
    (herm_diag (fun i => f (hA.eigenvalues i))).eq, Matrix.mul_assoc]

lemma cfc_cfc {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    cfc g (cfc f A) = cfc (fun x => g (f x)) A := by
  have hUU' : (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have e : cfc f A * (hA.eigenvectorUnitary : Matrix n n ℂ) =
      (hA.eigenvectorUnitary : Matrix n n ℂ) * Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) := by
    rw [cfc_eig A hA f, Matrix.mul_assoc, hUU', Matrix.mul_one]
  rw [cfc_unitary_diag (cfc f A) (herm_cfc A hA f) _ (unit_mul_star' hA) (fun i => f (hA.eigenvalues i)) e g,
    cfc_eig A hA (fun x => g (f x))]

lemma cfc_transpose {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (f : ℝ → ℝ) : cfc f Aᵀ = (cfc f A)ᵀ := by
  have e := eig_intertwine hA
  have hUU : (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 :=
    unit_mul_star' hA
  have hUU' : (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set D := Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) with hD
  have hAeq : A = U * D * Uᴴ := by
    calc A = A * (U * Uᴴ) := by rw [hUU, Matrix.mul_one]
      _ = U * D * Uᴴ := by rw [← Matrix.mul_assoc, e]
  have hWh : ((Uᴴ)ᵀ)ᴴ = Uᵀ := by ext i j; simp
  have hWW : (Uᴴ)ᵀ * ((Uᴴ)ᵀ)ᴴ = 1 := by rw [hWh, ← Matrix.transpose_mul, hUU, Matrix.transpose_one]
  have hUW : Uᵀ * (Uᴴ)ᵀ = 1 := by rw [← Matrix.transpose_mul, hUU', Matrix.transpose_one]
  have hDT : Dᵀ = D := by rw [hD, Matrix.diagonal_transpose]
  have eT : Aᵀ * (Uᴴ)ᵀ = (Uᴴ)ᵀ * D := by
    rw [hAeq, Matrix.transpose_mul, Matrix.transpose_mul, hDT, Matrix.mul_assoc, Matrix.mul_assoc, hUW,
      Matrix.mul_one]
  rw [cfc_unitary_diag Aᵀ hA.transpose (Uᴴ)ᵀ hWW (fun i => hA.eigenvalues i) eT f,
    cfc_eig A hA f, ← hUdef, hWh, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose]
  simp only [Matrix.mul_assoc]

open scoped Matrix.Norms.L2Operator MatrixOrder in
lemma posDef_cfc_inv {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosDef) :
    (cfc (fun x : ℝ => x⁻¹) A).PosDef := by
  have hsp : ∀ x ∈ spectrum ℝ A, 0 < x := fun x hx => hA.isStrictlyPositive.spectrum_pos hx
  apply Matrix.IsStrictlyPositive.posDef
  rw [cfc_isStrictlyPositive_iff (fun x : ℝ => x⁻¹) A (continuousOn_inv₀.mono fun x hx => (hsp x hx).ne')]
  intro x hx; exact inv_pos.2 (hsp x hx)

lemma qf_kron' {I : Type} [Fintype I] [DecidableEq I] (A B Y : Matrix I I ℂ) :
    star (vecM Y) ⬝ᵥ ((A ⊗ₖ B) *ᵥ vecM Y) = trace (Yᴴ * A * Y * Bᵀ) := by
  simpa using qf_kron A Bᵀ Y

lemma qf_sandwich {m n : Type} [Fintype m] [Fintype n] (V : Matrix m n ℂ) (L : Matrix m m ℂ) (v : n → ℂ) :
    star v ⬝ᵥ ((Vᴴ * L * V) *ᵥ v) = star (V *ᵥ v) ⬝ᵥ (L *ᵥ (V *ᵥ v)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

lemma tr_sym {I : Type} [Fintype I] (S L : Matrix I I ℂ) : trace (S * L * S) = trace (S * S * L) := by
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- `⟨ρ^{1/2}, log(σ ⊗ (ρ⁻¹)ᵀ) ρ^{1/2}⟩ = Tr ρ log σ - Tr ρ log ρ`. -/
lemma qf_rel {I : Type} [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ) (hA : A.PosDef) (hB : B.PosDef) :
    star (vecM (cfc Real.sqrt A)) ⬝ᵥ
        (cfc Real.log (B ⊗ₖ (cfc (fun x : ℝ => x⁻¹) A)ᵀ) *ᵥ vecM (cfc Real.sqrt A)) =
      trace (A * cfc Real.log B) - trace (A * cfc Real.log A) := by
  have hQ := posDef_cfc_inv hA
  have hlogQ : cfc Real.log (cfc (fun x : ℝ => x⁻¹) A) = -cfc Real.log A := by
    rw [cfc_cfc A hA.isHermitian, cfc_eig A hA.isHermitian, cfc_eig A hA.isHermitian Real.log]
    have : (Matrix.diagonal fun i => ((Real.log (hA.isHermitian.eigenvalues i)⁻¹ : ℝ) : ℂ)) =
        -(Matrix.diagonal fun i => ((Real.log (hA.isHermitian.eigenvalues i) : ℝ) : ℂ)) := by
      ext i j; rw [Matrix.neg_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
      split_ifs <;> simp [Real.log_inv]
    rw [this, Matrix.mul_neg, Matrix.neg_mul]
  have hS : (cfc Real.sqrt A)ᴴ = cfc Real.sqrt A := herm_cfc A hA.isHermitian _
  have hSS : cfc Real.sqrt A * cfc Real.sqrt A = A := by
    rw [cfc_mul_cfc A hA.isHermitian, cfc_congr_pos A hA _ (fun x => x)
      (fun x hx => Real.mul_self_sqrt hx.le), cfc_id' ℝ A hA.isHermitian.isSelfAdjoint]
  rw [log_kron hB hQ.transpose, cfc_transpose _ (herm_cfc A hA.isHermitian _), add_mulVec, dotProduct_add,
    qf_kron', qf_kron', Matrix.transpose_one, Matrix.transpose_transpose, hlogQ, hS, Matrix.mul_one,
    Matrix.mul_one, tr_sym, hSS, Matrix.mul_neg, Matrix.trace_neg, sub_eq_add_neg]

/-- Column embeddings `x ↦ (x, c)`. -/
def Ec {X C : Type} [DecidableEq X] [DecidableEq C] (c : C) : Matrix (X × C) X ℂ :=
  fun p x => if p = (x, c) then 1 else 0

lemma ptrC_eq_sum {X C : Type} [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    (M : Matrix (X × C) (X × C) ℂ) : ptrC M = ∑ c, (Matrix.conjTranspose (Ec (X := X) c) : Matrix X (X × C) ℂ) * M * (Ec (X := X) c : Matrix (X × C) X ℂ) := by
  ext x y
  simp [ptrC, Ec, Matrix.sum_apply, mul_apply, conjTranspose_apply]

lemma Ec_inj {X C : Type} [Fintype X] [DecidableEq X] [DecidableEq C] (c : C) :
    Function.Injective (Ec (X := X) c).mulVec := by
  intro v w h
  funext x
  have := congrFun h (x, c)
  simpa [mulVec, dotProduct, Ec] using this

lemma ptrC_posDef {X C : Type} [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C] [Nonempty C]
    {M : Matrix (X × C) (X × C) ℂ} (hM : M.PosDef) : (ptrC M).PosDef := by
  obtain ⟨c0⟩ := ‹Nonempty C›
  rw [ptrC_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ c0)]
  exact (hM.conjTranspose_mul_mul_same (Ec_inj c0)).add_posSemidef
    (posSemidef_sum _ fun c _ => hM.posSemidef.conjTranspose_mul_mul_same (Ec (X := X) c))

/-- **Petz monotonicity** of relative entropy under the partial trace (S3 of the SSA plan):
`Tr ρ log σ - Tr ρ log ρ ≤ Tr ρ_X log σ_X - Tr ρ_X log ρ_X`, i.e. `D(ρ_X‖σ_X) ≤ D(ρ‖σ)`. -/
theorem petz_mono {X C : Type} [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C] [Nonempty C]
    (ρ σ : Matrix (X × C) (X × C) ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    trace (ρ * cfc Real.log σ) - trace (ρ * cfc Real.log ρ) ≤
      trace (ptrC ρ * cfc Real.log (ptrC σ)) - trace (ptrC ρ * cfc Real.log (ptrC ρ)) := by
  have hρX := ptrC_posDef hρ
  have hσX := ptrC_posDef hσ
  set ρX := ptrC ρ with hρXdef
  set S := cfc Real.sqrt ρ with hSdef
  set Q := cfc (fun x : ℝ => x⁻¹) ρ with hQdef
  set P := cfc Real.sqrt ρX with hPdef
  set R := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) ρX with hRdef
  set Pinv := cfc (fun x : ℝ => x⁻¹) ρX with hPinvdef
  have hSh : Sᴴ = S := herm_cfc ρ hρ.isHermitian _
  have hRh : Rᴴ = R := herm_cfc ρX hρX.isHermitian _
  have hSS : S * S = ρ := by
    rw [hSdef, cfc_mul_cfc ρ hρ.isHermitian, cfc_congr_pos ρ hρ _ (fun x => x)
      (fun x hx => Real.mul_self_sqrt hx.le), cfc_id' ℝ ρ hρ.isHermitian.isSelfAdjoint]
  have hSQS : S * Q * S = 1 := by
    rw [hSdef, hQdef, cfc_mul_cfc ρ hρ.isHermitian, cfc_mul_cfc ρ hρ.isHermitian,
      cfc_congr_pos ρ hρ _ (fun _ => 1) (fun x hx => by
        rw [mul_comm, ← mul_assoc, Real.mul_self_sqrt hx.le, mul_inv_cancel₀ hx.ne']),
      cfc_const_one' ρ hρ.isHermitian]
  have hRρR : R * ρX * R = 1 := by
    calc R * ρX * R = R * cfc (fun x : ℝ => x) ρX * R := by rw [cfc_id' ℝ ρX hρX.isHermitian.isSelfAdjoint]
      _ = 1 := by
        rw [hRdef, cfc_mul_cfc ρX hρX.isHermitian, cfc_mul_cfc ρX hρX.isHermitian,
          cfc_congr_pos ρX hρX _ (fun _ => 1) (fun x hx => by
            rw [mul_comm, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hx.le, inv_mul_cancel₀ hx.ne']),
          cfc_const_one' ρX hρX.isHermitian]
  have hRR : R * R = Pinv := by
    rw [hRdef, hPinvdef, cfc_mul_cfc ρX hρX.isHermitian]
    exact cfc_congr_pos ρX hρX _ _ (fun x hx => by rw [← mul_inv, Real.mul_self_sqrt hx.le])
  have hPR : P * R = 1 := by
    rw [hPdef, hRdef, cfc_mul_cfc ρX hρX.isHermitian,
      cfc_congr_pos ρX hρX _ (fun _ => 1) (fun x hx => mul_inv_cancel₀ (Real.sqrt_pos.2 hx).ne'),
      cfc_const_one' ρX hρX.isHermitian]
  set T : Matrix (X × C) (X × C) ℂ := (R ⊗ₖ (1 : Matrix C C ℂ)) * S with hTdef
  have hTh : Tᴴ = S * (R ⊗ₖ (1 : Matrix C C ℂ)) := by
    rw [hTdef, conjTranspose_mul, conjTranspose_kronecker, hRh, conjTranspose_one, hSh]
  have hTT : T * Tᴴ = (R ⊗ₖ (1 : Matrix C C ℂ)) * ρ * (R ⊗ₖ (1 : Matrix C C ℂ)) := by
    rw [hTh, hTdef, ← hSS]; simp only [Matrix.mul_assoc]
  have hTQT : T * Q * Tᴴ = Pinv ⊗ₖ (1 : Matrix C C ℂ) := by
    calc T * Q * Tᴴ = (R ⊗ₖ (1 : Matrix C C ℂ)) * (S * Q * S) * (R ⊗ₖ (1 : Matrix C C ℂ)) := by
          rw [hTh, hTdef]; simp only [Matrix.mul_assoc]
      _ = Pinv ⊗ₖ (1 : Matrix C C ℂ) := by
          rw [hSQS, Matrix.mul_one, ← Matrix.mul_kronecker_mul, hRR, Matrix.mul_one]
  have hV : (Vmat T)ᴴ * Vmat T = 1 := VtV T (by rw [hTT, ptr_sandwich, hRρR])
  have hVD := VtDV T Q σ Pinv hTQT
  have hVv : Vmat T *ᵥ vecM P = vecM S := by
    rw [V_vec, hTdef, ← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, hPR, Matrix.mul_one,
      Matrix.one_kronecker_one, Matrix.one_mul]
  have hΔ : (σ ⊗ₖ Qᵀ).PosDef := hσ.kronecker (posDef_cfc_inv hρ).transpose
  have J := jensen_log_iso (σ ⊗ₖ Qᵀ) hΔ (Vmat T) hV
  rw [hVD] at J
  have key := J.dotProduct_mulVec_nonneg (vecM P)
  rw [sub_mulVec, dotProduct_sub, qf_sandwich, hVv] at key
  have q1 := qf_rel ρ σ hρ hσ
  have q2 := qf_rel ρX (ptrC σ) hρX hσX
  rw [← hSdef, ← hQdef] at q1
  rw [← hPdef, ← hPinvdef] at q2
  rw [q1, q2] at key
  exact sub_nonneg.1 key

end Petz


/-! ## S4: strong subadditivity for positive definite `ρ` on `A × (B × C)` (natural-log trace form). -/
section SSA4
open scoped Kronecker

lemma posDef_reindex {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) {M : Matrix m m ℂ} (hM : M.PosDef) : (reindex e e M).PosDef := by
  have h1 : (reindex e e M).PosSemidef := by
    rw [reindex_apply]; exact (posSemidef_submatrix_equiv e.symm).mpr hM.posSemidef
  refine h1.posDef_iff_isUnit.mpr ?_
  rw [Matrix.isUnit_iff_isUnit_det, det_reindex_self]
  exact isUnit_iff_ne_zero.mpr hM.det_pos.ne'

lemma reindex_symm_reindex {m n : Type} (e : m ≃ n) (M : Matrix m m ℂ) :
    reindex e.symm e.symm (reindex e e M) = M := by
  ext i j; simp [reindex_apply]

lemma cfc_reindex {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (M : Matrix m m ℂ) (hM : M.IsHermitian) (f : ℝ → ℝ) :
    cfc f (reindex e e M) = reindex e e (cfc f M) := by
  set V : Matrix n m ℂ := (1 : Matrix m m ℂ).submatrix e.symm id with hVdef
  have hA : (reindex e e M).IsHermitian := by rw [reindex_apply]; exact hM.submatrix e.symm
  have hV : reindex e e M * V = V * M := by
    ext i j
    simp only [hVdef, reindex_apply, Matrix.mul_apply, Matrix.one_apply, submatrix_apply, id, mul_ite, mul_one,
      mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact (Fintype.sum_equiv e.symm _ (fun k => if k = j then M (e.symm i) k else 0) (fun _ => rfl)).trans
      (by simp)
  have h := cfc_intertwine _ _ hA hM V hV f
  have hVV : V * Vᴴ = 1 := by
    ext i j; simp [hVdef, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply]
  calc cfc f (reindex e e M) = cfc f (reindex e e M) * V * Vᴴ := by
        rw [Matrix.mul_assoc, hVV, Matrix.mul_one]
    _ = V * cfc f M * Vᴴ := by rw [h]
    _ = reindex e e (cfc f M) := by
        ext i j; simp [hVdef, reindex_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply]

lemma tr_reindex {m n : Type} [Fintype m] [Fintype n] (e : m ≃ n) (P : Matrix n n ℂ) (N : Matrix m m ℂ) :
    trace (P * reindex e e N) = trace (reindex e.symm e.symm P * N) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, reindex_apply, submatrix_apply, Equiv.symm_symm]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← e.sum_comp]
  simp

/-- Partial trace over the first factor. -/
def ptrA {X C : Type} [Fintype X] (M : Matrix (X × C) (X × C) ℂ) : Matrix C C ℂ :=
  fun c d => ∑ x, M (x, c) (x, d)

lemma ptrA_eq {X C : Type} [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    (M : Matrix (X × C) (X × C) ℂ) :
    ptrA M = ptrC (reindex (Equiv.prodComm X C) (Equiv.prodComm X C) M) := by
  ext c d; simp [ptrA, ptrC, reindex_apply]

lemma ptrA_posDef {X C : Type} [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C] [Nonempty X]
    {M : Matrix (X × C) (X × C) ℂ} (hM : M.PosDef) : (ptrA M).PosDef := by
  rw [ptrA_eq]; exact ptrC_posDef (posDef_reindex _ hM)

lemma tr_kron_one {X C : Type} [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    (M : Matrix (X × C) (X × C) ℂ) (L : Matrix X X ℂ) :
    trace (M * (L ⊗ₖ (1 : Matrix C C ℂ))) = trace (ptrC M * L) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply, ptrC,
    Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_comm)

lemma tr_one_kron {X C : Type} [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    (M : Matrix (X × C) (X × C) ℂ) (L : Matrix C C ℂ) :
    trace (M * ((1 : Matrix X X ℂ) ⊗ₖ L)) = trace (ptrA M * L) := by
  have hk : ((1 : Matrix X X ℂ) ⊗ₖ L) =
      reindex (Equiv.prodComm C X) (Equiv.prodComm C X) (L ⊗ₖ (1 : Matrix X X ℂ)) := by
    ext ⟨x, c⟩ ⟨x', c'⟩; simp [reindex_apply, kroneckerMap_apply, mul_comm]
  rw [hk, tr_reindex, tr_kron_one, ptrA_eq, Equiv.prodComm_symm]

lemma ptrC_reindex_kron {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (P : Matrix A A ℂ) (K : Matrix (B × C) (B × C) ℂ) :
    ptrC (reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm (P ⊗ₖ K)) = P ⊗ₖ ptrC K := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [ptrC, reindex_apply, kroneckerMap_apply, Finset.mul_sum]

lemma ptrC_ptrC_assoc {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    ptrC (ptrC (reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm ρ)) = ptrC ρ := by
  ext a a'
  simp [ptrC, reindex_apply, Fintype.sum_prod_type]

lemma ptrA_ptrC_assoc {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    ptrA (ptrC (reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm ρ)) = ptrC (ptrA ρ) := by
  ext b b'
  simp only [ptrA, ptrC, reindex_apply, submatrix_apply, Equiv.symm_symm, Equiv.prodAssoc_apply]
  exact Finset.sum_comm

/-- **Strong subadditivity** (S4, positive definite case), natural-log trace form:
`Tr ρ_BC log ρ_BC - Tr ρ log ρ ≤ Tr ρ_B log ρ_B - Tr ρ_AB log ρ_AB`, i.e. `S(ABC) + S(B) ≤ S(AB) + S(BC)`. -/
theorem ssa_pd {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
    (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hρ : ρ.PosDef) :
    trace (ptrA ρ * cfc Real.log (ptrA ρ)) - trace (ρ * cfc Real.log ρ) ≤
      trace (ptrC (ptrA ρ) * cfc Real.log (ptrC (ptrA ρ))) -
        trace (ptrC (reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm ρ) *
          cfc Real.log (ptrC (reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm ρ))) := by
  have hρ' := posDef_reindex (Equiv.prodAssoc A B C).symm hρ
  have hρA : (ptrC ρ).PosDef := ptrC_posDef hρ
  have hρBC : (ptrA ρ).PosDef := ptrA_posDef hρ
  have hρB : (ptrC (ptrA ρ)).PosDef := ptrC_posDef hρBC
  have hK := hρA.kronecker hρBC
  have hσ := posDef_reindex (Equiv.prodAssoc A B C).symm hK
  have hP := petz_mono _ _ hρ' hσ
  rw [ptrC_reindex_kron, cfc_reindex _ _ hK.isHermitian, log_kron hρA hρBC, tr_reindex,
    reindex_symm_reindex, cfc_reindex _ _ hρ.isHermitian, tr_reindex, reindex_symm_reindex,
    log_kron hρA hρB, Matrix.mul_add, Matrix.mul_add, trace_add, trace_add, tr_kron_one, tr_one_kron,
    tr_kron_one, tr_one_kron, ptrC_ptrC_assoc, ptrA_ptrC_assoc] at hP
  have h := add_le_add_right hP (-trace (ptrC ρ * cfc Real.log (ptrC ρ)))
  convert h using 1 <;> ring

end SSA4


/-! ## S5: strong subadditivity for positive semidefinite `ρ` (limit `ρ + t•1`, `t → 0⁺`). -/
section SSA5

/-- `Tr(ρ ln ρ)` via the continuous function `x ln x` (`= -S(ρ) ln 2`). -/
noncomputable def Hn {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) : ℝ :=
  (cfc (fun x : ℝ => x * Real.log x) M).trace.re

lemma Hn_pd {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (hM : M.PosDef) :
    Hn M = (trace (M * cfc Real.log M)).re := by
  have h := cfc_mul (id : ℝ → ℝ) Real.log M continuousOn_id
    (Matrix.finite_real_spectrum.continuousOn Real.log)
  rw [cfc_id ℝ M hM.isHermitian.isSelfAdjoint] at h
  unfold Hn
  rw [← h]
  rfl

lemma herm_ptrC {X C : Type} [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    {M : Matrix (X × C) (X × C) ℂ} (h : M.IsHermitian) : (ptrC M).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, ptrC, star_sum]
  exact Finset.sum_congr rfl (fun c _ => h.apply _ _)

lemma herm_ptrA {X C : Type} [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    {M : Matrix (X × C) (X × C) ℂ} (h : M.IsHermitian) : (ptrA M).IsHermitian := by
  rw [ptrA_eq]; exact herm_ptrC (by rw [reindex_apply]; exact h.submatrix _)

lemma cont_ptrC {Y X C : Type} [TopologicalSpace Y] [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    {f : Y → Matrix (X × C) (X × C) ℂ} (hf : Continuous f) : Continuous fun y => ptrC (f y) :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_finset_sum _ fun c _ => hf.matrix_elem _ _

lemma cont_ptrA {Y X C : Type} [TopologicalSpace Y] [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    {f : Y → Matrix (X × C) (X × C) ℂ} (hf : Continuous f) : Continuous fun y => ptrA (f y) :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_finset_sum _ fun c _ => hf.matrix_elem _ _

open scoped Matrix.Norms.L2Operator in
lemma cont_Hn {Y n : Type} [TopologicalSpace Y] [Fintype n] [DecidableEq n]
    {f : Y → Matrix n n ℂ} (hf : Continuous f) (hh : ∀ y, (f y).IsHermitian) :
    Continuous fun y => Hn (f y) := by
  unfold Hn
  have h1 : Continuous fun y => cfc (fun x : ℝ => x * Real.log x) (f y) :=
    Continuous.cfc_of_mem_nhdsSet (𝕜 := ℝ) (s := Set.univ) _ Filter.univ_mem hf
      (fun y => (hh y).isSelfAdjoint) Real.continuous_mul_log.continuousOn
  exact Complex.continuous_re.comp h1.matrix_trace

/-- **Strong subadditivity** (S5, positive semidefinite case), `Hn = Tr(· ln ·)`:
`Tr ρ_AB ln ρ_AB + Tr ρ_BC ln ρ_BC ≤ Tr ρ ln ρ + Tr ρ_B ln ρ_B`, i.e. `S(ABC) + S(B) ≤ S(AB) + S(BC)`. -/
theorem ssa_psd {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
    (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hρ : ρ.PosSemidef) :
    Hn (ptrC (reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm ρ)) + Hn (ptrA ρ) ≤
      Hn ρ + Hn (ptrC (ptrA ρ)) := by
  let e := (Equiv.prodAssoc A B C).symm
  let P : ℝ → Matrix (A × (B × C)) (A × (B × C)) ℂ := fun t => ρ + (t : ℂ) • (1 : Matrix _ _ ℂ)
  have hPc : Continuous P := continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have hPh : ∀ t, (P t).IsHermitian := fun t => by
    unfold IsHermitian
    simp only [P, conjTranspose_add, conjTranspose_smul, conjTranspose_one, hρ.1.eq, Complex.star_def,
      Complex.conj_ofReal]
  let g : ℝ → ℝ := fun t => Hn (P t) + Hn (ptrC (ptrA (P t))) - Hn (ptrC (reindex e e (P t))) - Hn (ptrA (P t))
  have hg : Continuous g := by
    refine (((cont_Hn hPc hPh).add (cont_Hn (cont_ptrC (cont_ptrA hPc))
      (fun t => herm_ptrC (herm_ptrA (hPh t))))).sub (cont_Hn (cont_ptrC (hPc.matrix_reindex e e))
      (fun t => herm_ptrC (by rw [reindex_apply]; exact (hPh t).submatrix _)))).sub
      (cont_Hn (cont_ptrA hPc) (fun t => herm_ptrA (hPh t)))
  have hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ g t := by
    intro t ht
    have hpd : (P t).PosDef := Matrix.PosDef.posSemidef_add hρ (Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr ht))
    have h := ssa_pd (P t) hpd
    have hre := (Complex.le_def.mp h).1
    simp only [Complex.sub_re] at hre
    have hBC := ptrA_posDef hpd
    have hB := ptrC_posDef hBC
    have hAB := ptrC_posDef (posDef_reindex e hpd)
    simp only [g, Hn_pd _ hpd, Hn_pd _ hBC, Hn_pd _ hB, Hn_pd _ hAB]
    linarith
  have h0 : 0 ≤ g 0 :=
    ge_of_tendsto (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall hpos)
  simp only [g, P, Complex.ofReal_zero, zero_smul, add_zero] at h0
  linarith

end SSA5


/-! ## S5b: SSA in the published `DattaDiscord.mutualInfo` form: `I(A;B) ≤ I(A;BC)`. -/
section SSA6

lemma vn_eq_Hn {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    QAlgorithms.vnEntropy M = -Hn M / Real.log 2 := by
  have hf : (fun x : ℝ => x * Real.logb 2 x) = fun x => (Real.log 2)⁻¹ * (x * Real.log x) := by
    funext x; rw [Real.logb]; ring
  rw [QAlgorithms.vnEntropy, Hn, hf, cfc_const_mul _ _ M Real.continuous_mul_log.continuousOn,
    trace_smul, Complex.smul_re, smul_eq_mul]
  ring

lemma traceRight_eq {X C : Type} [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    (M : Matrix (X × C) (X × C) ℂ) : QAlgorithms.traceRight M = ptrC M := by
  ext i j; simp [QAlgorithms.traceRight, ptrC]

lemma traceLeft_eq {X C : Type} [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    (M : Matrix (X × C) (X × C) ℂ) : QAlgorithms.traceLeft M = ptrA M := by
  ext i j; simp [QAlgorithms.traceLeft, ptrA]

/-- **Strong subadditivity**, mutual-information form: `I(A;B)_ρ ≤ I(A;BC)_ρ` for PSD `ρ` on `A × (B × C)`. -/
theorem ssa_mi {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
    (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hρ : ρ.PosSemidef) :
    DattaDiscord.mutualInfo
        (ptrC (reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm ρ)) ≤
      DattaDiscord.mutualInfo ρ := by
  unfold DattaDiscord.mutualInfo
  rw [traceRight_eq, traceLeft_eq, traceRight_eq, traceLeft_eq, ptrC_ptrC_assoc, ptrA_ptrC_assoc]
  simp only [vn_eq_Hn]
  have h := ssa_psd ρ hρ
  have hinv : 0 < (Real.log 2)⁻¹ := inv_pos.mpr (Real.log_pos one_lt_two)
  have h2 := mul_le_mul_of_nonneg_right h hinv.le
  simp only [neg_div, div_eq_mul_inv]
  linarith

end SSA6

end SSALib


set_option autoImplicit false

namespace PureAux
open Matrix
open scoped ComplexOrder Kronecker


lemma trace_cfc_herm {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc]
  first
    | rw [Unitary.coe_star_mul_self]
    | rw [Unitary.star_mul_self]
    | rw [Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2]
  rw [Matrix.one_mul, Matrix.trace_diagonal]
  rfl

lemma vn_eq {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    QAlgorithms.vnEntropy s = (∑ i, Real.negMulLog (hs.eigenvalues i)) / Real.log 2 := by
  rw [QAlgorithms.vnEntropy, trace_cfc_herm hs, Complex.re_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Complex.ofReal_re, Real.negMulLog, Real.logb]
  ring

lemma vn_eq_roots {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    QAlgorithms.vnEntropy A = (A.charpoly.roots.map (fun z => Real.negMulLog z.re)).sum / Real.log 2 := by
  rw [vn_eq hA, hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_eq_multiset_sum]
  congr 1

/-- `S(AB) = S(BA)` for rectangular `A, B` (nonzero spectra agree, `negMulLog 0 = 0`). -/
lemma vn_mul_comm {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (B : Matrix n m ℂ) (h1 : (A * B).IsHermitian) (h2 : (B * A).IsHermitian) :
    QAlgorithms.vnEntropy (A * B) = QAlgorithms.vnEntropy (B * A) := by
  have key := congrArg Polynomial.roots (Matrix.charpoly_mul_comm' A B)
  have hne : ∀ (k : ℕ) (p : Polynomial ℂ), p.Monic → (Polynomial.X ^ k * p) ≠ 0 := fun k p hp =>
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hp.ne_zero
  rw [Polynomial.roots_mul (hne _ _ (Matrix.charpoly_monic _)),
    Polynomial.roots_mul (hne _ _ (Matrix.charpoly_monic _)),
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at key
  have hs : ∀ (k : ℕ) (s : Multiset ℂ), ((k • ({0} : Multiset ℂ) + s).map (fun z => Real.negMulLog z.re)).sum
      = (s.map (fun z => Real.negMulLog z.re)).sum := by
    intro k s
    simp [Multiset.map_add, Multiset.map_nsmul, Multiset.sum_add, Multiset.sum_nsmul]
  rw [vn_eq_roots h1, vn_eq_roots h2, ← hs (Fintype.card n), key, hs]

/-- coefficient matrix of a bipartite vector -/
def coef {X Y : Type*} (ψ : EuclideanSpace ℂ (X × Y)) : Matrix X Y ℂ := Matrix.of fun x y => ψ (x, y)

lemma traceRight_pure {X Y : Type*} [Fintype Y] (ψ : EuclideanSpace ℂ (X × Y)) :
    QAlgorithms.traceRight (QAlgorithms.pureDensity ψ) = coef ψ * (coef ψ)ᴴ := by
  ext x x'
  simp [QAlgorithms.traceRight, QAlgorithms.pureDensity, coef, Matrix.mul_apply]

lemma traceLeft_pure {X Y : Type*} [Fintype X] (ψ : EuclideanSpace ℂ (X × Y)) :
    QAlgorithms.traceLeft (QAlgorithms.pureDensity ψ) = ((coef ψ)ᴴ * coef ψ)ᵀ := by
  ext y y'
  simp [QAlgorithms.traceLeft, QAlgorithms.pureDensity, coef, Matrix.mul_apply, mul_comm]

/-- For a pure bipartite state the two marginals have equal entropy. -/
theorem vn_pure_complement {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (ψ : EuclideanSpace ℂ (X × Y)) :
    QAlgorithms.vnEntropy (QAlgorithms.traceLeft (QAlgorithms.pureDensity ψ)) =
      QAlgorithms.vnEntropy (QAlgorithms.traceRight (QAlgorithms.pureDensity ψ)) := by
  rw [traceLeft_pure, traceRight_pure]
  have hT : ((coef ψ)ᴴ * coef ψ)ᵀ.IsHermitian := (isHermitian_conjTranspose_mul_self _).transpose
  rw [vn_eq_roots hT, Matrix.charpoly_transpose, ← vn_eq_roots (isHermitian_conjTranspose_mul_self _)]
  exact vn_mul_comm _ _ (isHermitian_conjTranspose_mul_self _) (isHermitian_mul_conjTranspose_self _)

/-- A pure state has zero entropy. -/
theorem vn_pure {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) (h : ‖ψ‖ = 1) :
    QAlgorithms.vnEntropy (QAlgorithms.pureDensity ψ) = 0 := by
  have hP : QAlgorithms.pureDensity ψ =
      Matrix.replicateCol Unit (fun i => ψ i) * (Matrix.replicateCol Unit (fun i => ψ i))ᴴ := by
    ext i j; simp [QAlgorithms.pureDensity, Matrix.mul_apply]
  rw [hP, vn_mul_comm _ _ (isHermitian_mul_conjTranspose_self _) (isHermitian_conjTranspose_mul_self _)]
  have hn := EuclideanSpace.norm_sq_eq ψ
  rw [h] at hn
  have hs : ∑ i, star (ψ i) * ψ i = 1 := by
    have : ∑ i, star (ψ i) * ψ i = ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => by rw [Complex.star_def, Complex.conj_mul']
    rw [this, ← hn]; simp
  have h1 : (Matrix.replicateCol Unit (fun i => ψ i))ᴴ * Matrix.replicateCol Unit (fun i => ψ i) = 1 := by
    ext u v
    simpa [Matrix.mul_apply] using hs
  have hr : (Polynomial.X - 1 : Polynomial ℂ).roots = {1} := by
    simpa using Polynomial.roots_X_sub_C (1 : ℂ)
  rw [h1, vn_eq_roots isHermitian_one]
  simp [Matrix.charpoly_one, hr]

/-- Mutual information of a pure state: `I(X;Y) = 2 S(X)`. -/
theorem mi_pure {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (ψ : EuclideanSpace ℂ (X × Y)) (h : ‖ψ‖ = 1) :
    DattaDiscord.mutualInfo (QAlgorithms.pureDensity ψ) =
      2 * QAlgorithms.vnEntropy (QAlgorithms.traceRight (QAlgorithms.pureDensity ψ)) := by
  rw [DattaDiscord.mutualInfo, vn_pure_complement, vn_pure ψ h]; ring

lemma eig_intertwine {n : Type} [Fintype n] [DecidableEq n] {σ : Matrix n n ℂ} (hσ : σ.IsHermitian) :
    σ * (hσ.eigenvectorUnitary : Matrix n n ℂ) =
      (hσ.eigenvectorUnitary : Matrix n n ℂ) * Matrix.diagonal (fun i => ((hσ.eigenvalues i : ℝ) : ℂ)) := by
  have hs := congrArg (· * (hσ.eigenvectorUnitary : Matrix n n ℂ)) hσ.spectral_theorem
  beta_reduce at hs
  rw [hs, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]
  rfl

/-- Every PSD matrix is the marginal of a (sub-normalised) pure state with reference `S`. -/
theorem exists_purification {S : Type} [Fintype S] [DecidableEq S] {ρ : Matrix S S ℂ}
    (hρ : ρ.PosSemidef) :
    ∃ ψ : EuclideanSpace ℂ (S × S), QAlgorithms.traceLeft (QAlgorithms.pureDensity ψ) = ρ := by
  set U : Matrix S S ℂ := (hρ.1.eigenvectorUnitary : Matrix S S ℂ) with hU
  set sq : Matrix S S ℂ :=
    U * Matrix.diagonal (fun i => ((Real.sqrt (hρ.1.eigenvalues i) : ℝ) : ℂ)) with hsq
  refine ⟨WithLp.toLp 2 (fun p => sq p.2 p.1), ?_⟩
  have h1 : QAlgorithms.traceLeft (QAlgorithms.pureDensity (WithLp.toLp 2 (fun p : S × S => sq p.2 p.1)))
      = sq * sqᴴ := by
    ext s s'
    simp [QAlgorithms.traceLeft, QAlgorithms.pureDensity, Matrix.mul_apply]
  have h2 : sq * sqᴴ = U * Matrix.diagonal (fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    rw [hsq, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal, ← Matrix.mul_assoc]
    congr 3
    funext i
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hρ.eigenvalues_nonneg i)]
  have h3 : ρ = U * Matrix.diagonal (fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    rw [hU, ← eig_intertwine hρ.1, Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff.mp hρ.1.eigenvectorUnitary.2, Matrix.mul_one]
  rw [h1, h2, ← h3]

lemma trace_eig {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    s.trace.re = ∑ i, hs.eigenvalues i := by
  have hsa : IsSelfAdjoint s := hs
  have h1 : cfc (fun x : ℝ => x) s = s := cfc_id' ℝ s hsa
  conv_lhs => rw [← h1]
  rw [trace_cfc_herm hs, Complex.re_sum]
  simp only [Complex.ofReal_re]

/-- `S(ρ) ≥ 0` for a density matrix. -/
theorem vn_nonneg {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) : 0 ≤ QAlgorithms.vnEntropy ρ := by
  have hsum : ∑ i, hρ.1.eigenvalues i = 1 := by rw [← trace_eig hρ.1, htr]; simp
  rw [vn_eq hρ.1]
  refine div_nonneg (Finset.sum_nonneg fun i _ =>
    Real.negMulLog_nonneg (hρ.eigenvalues_nonneg i) ?_) (Real.log_nonneg one_le_two)
  rw [← hsum]
  exact Finset.single_le_sum (fun j _ => hρ.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- `S(ρ) ≤ log₂ d` for a density matrix of dimension `d`. -/
theorem vn_le_log_card {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) : QAlgorithms.vnEntropy ρ ≤ Real.log (Fintype.card n) / Real.log 2 := by
  have hsum : ∑ i, hρ.1.eigenvalues i = 1 := by rw [← trace_eig hρ.1, htr]; simp
  have hc : (0 : ℝ) < Fintype.card n := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h | h
    · exfalso; rw [Fintype.card_eq_zero_iff] at h; haveI := h; simp at hsum
    · exact_mod_cast h
  have hc' := hc.ne'
  rw [vn_eq hρ.1]
  refine div_le_div_of_nonneg_right ?_ (Real.log_nonneg one_le_two)
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := fun _ => (1 : ℝ) / Fintype.card n) (p := hρ.1.eigenvalues) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
    (fun i _ => Set.mem_Ici.mpr (hρ.eigenvalues_nonneg i))
  simp only [smul_eq_mul, ← Finset.mul_sum, hsum, mul_one] at hJ
  have h2 : Real.negMulLog (1 / (Fintype.card n : ℝ)) =
      1 / Fintype.card n * Real.log (Fintype.card n) := by
    simp [Real.negMulLog, Real.log_inv]
  rw [h2] at hJ
  exact le_of_mul_le_mul_left hJ (by positivity)

lemma trace_tr_left {a b : Type*} [Fintype a] [Fintype b] (M : Matrix (a × b) (a × b) ℂ) :
    (QAlgorithms.traceLeft M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, QAlgorithms.traceLeft, Matrix.of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma psd_tr_left {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {M : Matrix (a × b) (a × b) ℂ} (h : M.PosSemidef) : (QAlgorithms.traceLeft M).PosSemidef := by
  have e : QAlgorithms.traceLeft M = ∑ x : a,
      (Matrix.of fun (j : b) (p : a × b) => if p = (x, j) then (1 : ℂ) else 0) * M *
        (Matrix.of fun (j : b) (p : a × b) => if p = (x, j) then (1 : ℂ) else 0)ᴴ := by
    ext i j
    simp [QAlgorithms.traceLeft, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e]
  exact Matrix.posSemidef_sum _ (fun x _ => h.mul_mul_conjTranspose_same _)

lemma psd_tr_right {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {M : Matrix (a × b) (a × b) ℂ} (h : M.PosSemidef) : (QAlgorithms.traceRight M).PosSemidef := by
  have e : QAlgorithms.traceRight M = ∑ x : b,
      (Matrix.of fun (j : a) (p : a × b) => if p = (j, x) then (1 : ℂ) else 0) * M *
        (Matrix.of fun (j : a) (p : a × b) => if p = (j, x) then (1 : ℂ) else 0)ᴴ := by
    ext i j
    simp [QAlgorithms.traceRight, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e]
  exact Matrix.posSemidef_sum _ (fun x _ => h.mul_mul_conjTranspose_same _)

lemma trace_pure {ι : Type*} [Fintype ι] (Ψ : EuclideanSpace ℂ ι) (h : ‖Ψ‖ = 1) :
    (QAlgorithms.pureDensity Ψ).trace = 1 := by
  have h2 := EuclideanSpace.norm_sq_eq Ψ
  rw [h, one_pow] at h2
  simp only [Matrix.trace, Matrix.diag, QAlgorithms.pureDensity, Matrix.of_apply, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  exact_mod_cast h2.symm

open scoped ComplexOrder in
lemma psd_pure {ι : Type*} [Fintype ι] (Ψ : EuclideanSpace ℂ ι) :
    (QAlgorithms.pureDensity Ψ).PosSemidef := by
  have e : QAlgorithms.pureDensity Ψ =
      (Matrix.of fun i (_ : Unit) => Ψ i) * (Matrix.of fun i (_ : Unit) => Ψ i)ᴴ := by
    ext i j
    simp [QAlgorithms.pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e]; exact Matrix.posSemidef_self_mul_conjTranspose _

lemma trace_tr_right {a b : Type*} [Fintype a] [Fintype b] (M : Matrix (a × b) (a × b) ℂ) :
    (QAlgorithms.traceRight M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, QAlgorithms.traceRight, Matrix.of_apply, Fintype.sum_prod_type]

lemma tr_right_sum {α β ι : Type*} [Fintype β] [Fintype ι] (Y : ι → Matrix (α × β) (α × β) ℂ) :
    QAlgorithms.traceRight (∑ i, Y i) = ∑ i, QAlgorithms.traceRight (Y i) := by
  ext x x'
  simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.sum_apply]
  exact Finset.sum_comm

lemma tr_right_cyc {a b r : Type*} [Fintype a] [Fintype b] [Fintype r] [DecidableEq r]
    (A : Matrix b a ℂ) (Y : Matrix (r × a) (r × b) ℂ) :
    QAlgorithms.traceRight (((1 : Matrix r r ℂ) ⊗ₖ A) * Y) =
      QAlgorithms.traceRight (Y * ((1 : Matrix r r ℂ) ⊗ₖ A)) := by
  ext s s'
  simp [QAlgorithms.traceRight, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

section Chan
open WildeQIT WildeQIT.EADamping

lemma psd_idTensor {r a b : Type} [Fintype r] [DecidableEq r] [Fintype a] [Fintype b] [DecidableEq a]
    (N : QChannel a b) {X : Matrix (r × a) (r × a) ℂ} (hX : X.PosSemidef) :
    (idTensorApply N X).PosSemidef := by
  unfold idTensorApply
  exact Matrix.posSemidef_sum _ (fun i _ => hX.mul_mul_conjTranspose_same _)

/-- A channel on the second factor does not change the first marginal. -/
lemma tr_right_idTensor {r a b : Type} [Fintype r] [DecidableEq r] [Fintype a] [Fintype b] [DecidableEq a]
    (N : QChannel a b) (X : Matrix (r × a) (r × a) ℂ) :
    QAlgorithms.traceRight (idTensorApply N X) = QAlgorithms.traceRight X := by
  have hk : ∀ i, ((1 : Matrix r r ℂ) ⊗ₖ N.K i)ᴴ * ((1 : Matrix r r ℂ) ⊗ₖ N.K i) =
      (1 : Matrix r r ℂ) ⊗ₖ ((N.K i)ᴴ * N.K i) := by
    intro i
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul]
  have hs : ∑ i, (1 : Matrix r r ℂ) ⊗ₖ ((N.K i)ᴴ * N.K i) = 1 := by
    have : ∑ i, (1 : Matrix r r ℂ) ⊗ₖ ((N.K i)ᴴ * N.K i) =
        (1 : Matrix r r ℂ) ⊗ₖ (∑ i, (N.K i)ᴴ * N.K i) := by
      ext p q
      simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]
    rw [this, N.complete, Matrix.one_kronecker_one]
  unfold idTensorApply
  rw [tr_right_sum]
  have e : ∀ i, QAlgorithms.traceRight (((1 : Matrix r r ℂ) ⊗ₖ N.K i) * X * ((1 : Matrix r r ℂ) ⊗ₖ N.K i)ᴴ)
      = QAlgorithms.traceRight (X * ((1 : Matrix r r ℂ) ⊗ₖ ((N.K i)ᴴ * N.K i))) := by
    intro i
    rw [Matrix.mul_assoc, tr_right_cyc, Matrix.mul_assoc, hk]
  simp_rw [e, ← tr_right_sum, ← Matrix.mul_sum, hs, Matrix.mul_one]

/-- `I(R;B) ≤ log₂|a| + log₂|b|` for any pure input: the channel mutual information is bounded. -/
theorem mi_out_le {r a b : Type} [Fintype r] [DecidableEq r] [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) (ψ : EuclideanSpace ℂ (r × a)) (hψ : ‖ψ‖ = 1) :
    DattaDiscord.mutualInfo (idTensorApply N (QAlgorithms.pureDensity ψ)) ≤
      (Real.log (Fintype.card a) + Real.log (Fintype.card b)) / Real.log 2 := by
  have hX : (QAlgorithms.pureDensity ψ).PosSemidef := psd_pure ψ
  have htrX : (QAlgorithms.pureDensity ψ).trace = 1 := trace_pure ψ hψ
  have hY := psd_idTensor N hX
  have htrY : (idTensorApply N (QAlgorithms.pureDensity ψ)).trace = 1 := by
    rw [← trace_tr_right, tr_right_idTensor, trace_tr_right, htrX]
  rw [DattaDiscord.mutualInfo, tr_right_idTensor, ← vn_pure_complement]
  have h1 := vn_le_log_card (psd_tr_left hX) (by rw [trace_tr_left, htrX])
  have h2 := vn_le_log_card (psd_tr_left hY) (by rw [trace_tr_left, htrY])
  have h3 := vn_nonneg hY htrY
  rw [add_div]; linarith

theorem bdd_channelMI {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (N : QChannel a b) : BddAbove (Set.range fun φ : WildeQIT.Degradable.PureInput a =>
      DattaDiscord.mutualInfo (idTensorApply N (QAlgorithms.pureDensity φ.ψ))) :=
  ⟨_, by rintro _ ⟨φ, rfl⟩; exact mi_out_le N φ.ψ φ.norm_eq_one⟩

end Chan

end PureAux

/-! ## D3 complete: `I(M; Bⁿ T_B)_ω ≤ n · I(N)` for every EA code. -/
namespace D3F
open Matrix WildeQIT WildeQIT.EADamping
open scoped ComplexOrder

theorem hgen_thm {z a' b' : Type} [Fintype z] [DecidableEq z] [Fintype a'] [Fintype b']
    [DecidableEq a'] [DecidableEq b'] (M : QChannel a' b') (σ : Matrix (z × a') (z × a') ℂ)
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    DattaDiscord.mutualInfo (idTensorApply M σ) ≤ channelMutualInfo M :=
  DG.mi_le_channelMI (fun hρ => PureAux.exists_purification hρ) (fun ρ hρ => SSALib.ssa_mi ρ hρ)
    (fun N => PureAux.bdd_channelMI N) M σ hσ htr

theorem d3_full {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (N : QChannel a b) (n k : ℕ) (c : EACode a b n k) (hk : 0 < k) :
    DattaDiscord.mutualInfo (EAConv.cqState c N) ≤ n * channelMutualInfo N :=
  DG3.d3_assembled (fun M σ hσ htr => hgen_thm M σ hσ htr) N
    (DG4.d3c (fun M σ hσ htr => hgen_thm M σ hσ htr) N) hk c

end D3F

/-! ## D2a: data processing `I(R; Φ(B)) ≤ I(R; B)` for a local channel (Kraus isometry + SSA). -/
namespace DG5
open Matrix SubaddAux WildeQIT WildeQIT.EADamping
open scoped Kronecker ComplexOrder

/-- The Kraus isometry `V (y,i) x = K_i y x`. -/
def isoV {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (Φ : QChannel a b) :
    Matrix (b × Φ.ι) a ℂ := fun p x => Φ.K p.2 p.1 x

lemma isoV_iso {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (Φ : QChannel a b) :
    (isoV Φ)ᴴ * isoV Φ = 1 := by
  rw [← Φ.complete]
  ext x x'
  simp only [isoV, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma tr_left_kron_conj {R p q : Type} [Fintype R] [DecidableEq R] [Fintype q]
    (A : Matrix p q ℂ) (X : Matrix (R × q) (R × q) ℂ) :
    QAlgorithms.traceLeft (((1 : Matrix R R ℂ) ⊗ₖ A) * X * ((1 : Matrix R R ℂ) ⊗ₖ A)ᴴ) =
      A * QAlgorithms.traceLeft X * Aᴴ := by
  ext i j
  simp only [QAlgorithms.traceLeft, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, star_zero, apply_ite (star : ℂ → ℂ), mul_ite, mul_zero,
    Finset.sum_mul, Finset.mul_sum, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  rw [Finset.sum_comm]

lemma iso_conj_vn {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : Wᴴ * W = 1) {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    QAlgorithms.vnEntropy (W * X * Wᴴ) = QAlgorithms.vnEntropy X := by
  have h1 : (W * X * Wᴴ).IsHermitian := isHermitian_mul_mul_conjTranspose W hX
  have h2 : Wᴴ * (W * X) = X := by rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
  rw [PureAux.vn_mul_comm (W * X) Wᴴ h1 (by rw [h2]; exact hX), h2]

lemma iso_kron {R m n : Type} [Fintype R] [DecidableEq R] [Fintype m] [Fintype n]
    [DecidableEq n] (W : Matrix m n ℂ) (hW : Wᴴ * W = 1) :
    ((1 : Matrix R R ℂ) ⊗ₖ W)ᴴ * ((1 : Matrix R R ℂ) ⊗ₖ W) = 1 := by
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul, hW,
    one_kronecker_one]

lemma tr_right_iso {R m n : Type} [Fintype R] [DecidableEq R] [Fintype m] [Fintype n]
    [DecidableEq n] (W : Matrix m n ℂ) (hW : Wᴴ * W = 1) (X : Matrix (R × n) (R × n) ℂ) :
    QAlgorithms.traceRight (((1 : Matrix R R ℂ) ⊗ₖ W) * X * ((1 : Matrix R R ℂ) ⊗ₖ W)ᴴ) =
      QAlgorithms.traceRight X := by
  rw [Matrix.mul_assoc, DG4.tr_right_cyc, Matrix.mul_assoc]
  rw [show ((1 : Matrix R R ℂ) ⊗ₖ W)ᴴ * ((1 : Matrix R R ℂ) ⊗ₖ W) = 1 from iso_kron W hW,
    Matrix.mul_one]

/-- Tracing the Kraus environment of `(1 ⊗ V) ω (1 ⊗ V)†` gives `(id ⊗ Φ) ω`. -/
lemma env_trace {R a b : Type} [Fintype R] [DecidableEq R] [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (Φ : QChannel a b) (ω : Matrix (R × a) (R × a) ℂ) :
    QAlgorithms.traceRight (reindex (Equiv.prodAssoc R b Φ.ι).symm (Equiv.prodAssoc R b Φ.ι).symm
      (((1 : Matrix R R ℂ) ⊗ₖ isoV Φ) * ω * ((1 : Matrix R R ℂ) ⊗ₖ isoV Φ)ᴴ)) =
      idTensorApply Φ ω := by
  ext ⟨r1, y1⟩ ⟨r2, y2⟩
  simp only [QAlgorithms.traceRight, Matrix.of_apply, reindex_apply, submatrix_apply,
    Equiv.symm_symm, Equiv.prodAssoc_apply, idTensorApply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply,
    isoV]

/-- **D2a (data processing)**. -/
theorem mi_dp {R a b : Type} [Fintype R] [DecidableEq R] [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] [Nonempty R] [Nonempty b] (Φ : QChannel a b) (ω : Matrix (R × a) (R × a) ℂ)
    (hω : ω.PosSemidef) (hι : Nonempty Φ.ι) :
    DattaDiscord.mutualInfo (idTensorApply Φ ω) ≤ DattaDiscord.mutualInfo ω := by
  classical
  have := hι
  have hW := iso_kron (R := R) (isoV Φ) (isoV_iso Φ)
  have hps' := hω.mul_mul_conjTranspose_same ((1 : Matrix R R ℂ) ⊗ₖ isoV Φ)
  have hssa := SSALib.ssa_mi _ hps'
  rw [← SSALib.traceRight_eq, env_trace Φ ω] at hssa
  have heq : DattaDiscord.mutualInfo (((1 : Matrix R R ℂ) ⊗ₖ isoV Φ) * ω *
      ((1 : Matrix R R ℂ) ⊗ₖ isoV Φ)ᴴ) = DattaDiscord.mutualInfo ω := by
    unfold DattaDiscord.mutualInfo
    rw [tr_right_iso _ (isoV_iso Φ), tr_left_kron_conj,
      iso_conj_vn _ (isoV_iso Φ) (herm_tr_left hω.1), iso_conj_vn _ hW hω.1]
  linarith

end DG5

/-! ## D2b: measurement channel on Bob's side + Fano on the classical output. -/
namespace DG6
open Matrix WildeQIT WildeQIT.EADamping
open scoped Kronecker ComplexOrder

/-- Gibbs term inequality with only `0 < y` needed. -/
lemma gterm {t x y : ℝ} (ht : 0 ≤ t) (htx : t ≤ x) (hy : 0 < y) :
    Real.negMulLog t ≤ -(t * Real.log x) - t * Real.log y + x * y - t := by
  rcases ht.eq_or_lt with h | h
  · subst h
    rw [Real.negMulLog_zero]
    nlinarith [mul_nonneg htx hy.le]
  · have hx : 0 < x := by linarith
    have hl := Real.log_le_sub_one_of_pos (show 0 < x * y / t by positivity)
    rw [Real.log_div (by positivity) h.ne', Real.log_mul hx.ne' hy.ne'] at hl
    have hm : t * (Real.log x + Real.log y - Real.log t) ≤ t * (x * y / t - 1) :=
      mul_le_mul_of_nonneg_left hl h.le
    have e : t * (x * y / t - 1) = x * y - t := by field_simp
    rw [Real.negMulLog]
    nlinarith [hm, e]

/-- The measurement channel of a family `B_j` with `∑ B_jᴴ B_j = 1`:
Kraus operators `K_(j,e) = |j⟩⟨row e of B_j|`. -/
noncomputable def measCh {D : Type} [Fintype D] [DecidableEq D] {k : ℕ} (B : Fin k → Matrix D D ℂ)
    (hB : ∑ j, (B j)ᴴ * B j = 1) : QChannel D (Fin k) where
  ι := Fin k × D
  K := fun p => Matrix.of fun y x => if y = p.1 then B p.1 p.2 x else 0
  complete := by
    rw [← hB]
    ext x x'
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun e _ => ?_))
    simp [apply_ite (star : ℂ → ℂ)]

lemma meas_out {D : Type} [Fintype D] [DecidableEq D] {k : ℕ} (B : Fin k → Matrix D D ℂ)
    (hB : ∑ j, (B j)ᴴ * B j = 1) (X : Matrix (Fin k × D) (Fin k × D) ℂ) (m m' y y' : Fin k) :
    idTensorApply (measCh B hB) X (m, y) (m', y') =
      if y = y' then ∑ e, ∑ x, ∑ x', B y e x * X (m, x) (m', x') * star (B y e x') else 0 := by
  simp only [idTensorApply, measCh, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply, Fintype.sum_prod_type]
  refine (Fintype.sum_prod_type _).trans ?_
  by_cases h : y = y'
  · subst h
    simp [ite_mul, mul_ite, apply_ite (star : ℂ → ℂ), Finset.sum_ite_eq, Finset.sum_mul, mul_assoc]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  · simp [ite_mul, mul_ite, apply_ite (star : ℂ → ℂ), Finset.sum_ite_eq, h]

/-- Fano (natural log): `H(M,J) ≤ H(J) + log 2 + ε log k` for a joint law with uniform `M`
and success probability `∑_m q(m,m) ≥ 1 - ε`. -/
lemma fano_nat {k : ℕ} (hk : 0 < k) (q : Fin k × Fin k → ℝ) (hq : ∀ p, 0 ≤ q p)
    (hrow : ∀ m, ∑ j, q (m, j) = 1 / k) (ε : ℝ) (hs : 1 - ε ≤ ∑ m, q (m, m)) :
    ∑ p, Real.negMulLog (q p) ≤
      ∑ j, Real.negMulLog (∑ m, q (m, j)) + Real.log 2 + ε * Real.log k := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨r, hr⟩ : ∃ r : Fin k → ℝ, r = fun j => ∑ m, q (m, j) := ⟨_, rfl⟩
  have hr' : ∀ j, r j = ∑ m, q (m, j) := fun j => by rw [hr]
  obtain ⟨c, hc⟩ : ∃ c : Fin k × Fin k → ℝ,
      c = fun p => (if p.1 = p.2 then (1 / 2 : ℝ) else 0) + 1 / (2 * k) := ⟨_, rfl⟩
  have hc' : ∀ p, c p = (if p.1 = p.2 then (1 / 2 : ℝ) else 0) + 1 / (2 * k) := fun p => by rw [hc]
  have h2k : 0 < 1 / (2 * (k : ℝ)) := div_pos one_pos (by linarith)
  have hcpos : ∀ p, 0 < c p := fun p => by rw [hc']; split_ifs <;> linarith
  have hqr : ∀ p : Fin k × Fin k, q p ≤ r p.2 := fun p => by
    rw [hr' p.2]
    exact Finset.single_le_sum (f := fun m => q (m, p.2)) (fun m _ => hq _) (Finset.mem_univ p.1)
  have hlk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  have hterm : ∀ p : Fin k × Fin k, Real.negMulLog (q p) ≤
      -(q p * Real.log (r p.2)) + q p * Real.log 2 + q p * Real.log k
        - (if p.1 = p.2 then q p * Real.log k else 0) + r p.2 * c p - q p := by
    intro p
    have h1 := gterm (hq p) (hqr p) (hcpos p)
    have h2 : -(q p * Real.log (c p)) ≤
        q p * Real.log 2 + q p * Real.log k - (if p.1 = p.2 then q p * Real.log k else 0) := by
      by_cases h : p.1 = p.2
      · rw [if_pos h]
        have hl : Real.log (1 / 2) ≤ Real.log (c p) :=
          Real.log_le_log (by norm_num) (by rw [hc', if_pos h]; linarith)
        rw [one_div, Real.log_inv] at hl
        nlinarith [mul_nonneg (hq p) (by linarith : 0 ≤ Real.log (c p) + Real.log 2)]
      · rw [if_neg h, hc', if_neg h, zero_add, one_div, Real.log_inv,
          Real.log_mul two_ne_zero hk0]
        linarith
    linarith
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => hterm p)
  have hT : ∑ p : Fin k × Fin k, (-(q p * Real.log (r p.2)) + q p * Real.log 2 + q p * Real.log k
        - (if p.1 = p.2 then q p * Real.log k else 0) + r p.2 * c p - q p) =
      -(∑ p : Fin k × Fin k, q p * Real.log (r p.2)) + (∑ p, q p) * Real.log 2
        + (∑ p, q p) * Real.log k - (∑ p : Fin k × Fin k, if p.1 = p.2 then q p * Real.log k else 0)
        + (∑ p : Fin k × Fin k, r p.2 * c p) - ∑ p, q p := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_mul]
  have F1 : ∑ p, q p = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hk0
  have Fr : ∑ j, r j = 1 := by
    simp only [hr']
    rw [Finset.sum_comm]
    simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hk0
  have F2 : ∑ p : Fin k × Fin k, q p * Real.log (r p.2) = ∑ j, r j * Real.log (r j) := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_mul, hr' j]
  have hcs : ∀ j, ∑ m, c (m, j) = 1 := by
    intro j
    simp only [hc', Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp <;> ring
  have F3 : ∑ p : Fin k × Fin k, r p.2 * c p = 1 := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hcs, mul_one]
    exact Fr
  have F4 : ∑ p : Fin k × Fin k, (if p.1 = p.2 then q p * Real.log k else 0) =
      Real.log k * ∑ m, q (m, m) := by
    simp only [Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  have hHr : ∑ j, Real.negMulLog (∑ m, q (m, j)) = -∑ j, r j * Real.log (r j) := by
    simp only [← hr', Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  rw [hT, F1, F2, F3, F4] at hsum
  rw [hHr]
  have hm : Real.log k * (1 - ∑ m, q (m, m)) ≤ Real.log k * ε :=
    mul_le_mul_of_nonneg_left (by linarith) hlk
  nlinarith [hm]

end DG6

namespace DG6
open Matrix WildeQIT WildeQIT.EADamping
open scoped Kronecker ComplexOrder

lemma sqrt_sq {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    (cfc Real.sqrt A)ᴴ * cfc Real.sqrt A = A := by
  have hsa : IsSelfAdjoint A := hA.1
  have e : ∀ i, Real.sqrt (hA.1.eigenvalues i) * Real.sqrt (hA.1.eigenvalues i) =
      hA.1.eigenvalues i := fun i => Real.mul_self_sqrt (hA.eigenvalues_nonneg i)
  rw [SSALib.herm_cfc A hA.1, SSALib.cfc_mul_cfc A hA.1, SSALib.cfc_eig A hA.1]
  conv_rhs => rw [← cfc_id' ℝ A hsa, SSALib.cfc_eig A hA.1]
  simp only [e]

lemma vn_diag {n : Type} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    QAlgorithms.vnEntropy (Matrix.diagonal (fun i => (d i : ℂ))) =
      (∑ i, Real.negMulLog (d i)) / Real.log 2 := by
  rw [QAlgorithms.vnEntropy, SSALib.cfc_diag, Matrix.trace_diagonal, Complex.re_sum, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Complex.ofReal_re, Real.negMulLog, Real.logb]
  ring

/-- Fano for a classical joint law (diagonal state) with uniform `M`. -/
theorem fano_diag {k : ℕ} (hk : 0 < k) (q : Fin k × Fin k → ℝ) (hq : ∀ p, 0 ≤ q p)
    (hrow : ∀ m, ∑ j, q (m, j) = 1 / k) (ε : ℝ) (hs : 1 - ε ≤ ∑ m, q (m, m)) :
    (1 - ε) * Real.logb 2 k ≤
      1 + DattaDiscord.mutualInfo (Matrix.diagonal (fun p => (q p : ℂ))) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hR : QAlgorithms.traceRight (Matrix.diagonal (fun p => (q p : ℂ))) =
      Matrix.diagonal (fun _ : Fin k => ((1 / k : ℝ) : ℂ)) := by
    ext m m'
    by_cases h : m = m'
    · subst h
      simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.diagonal_apply_eq]
      rw [← hrow m, Complex.ofReal_sum]
    · rw [Matrix.diagonal_apply_ne _ h]
      simp only [QAlgorithms.traceRight, Matrix.of_apply]
      exact Finset.sum_eq_zero
        (fun x _ => Matrix.diagonal_apply_ne _ (fun h' => h (congrArg Prod.fst h')))
  have hL : QAlgorithms.traceLeft (Matrix.diagonal (fun p => (q p : ℂ))) =
      Matrix.diagonal (fun j => ((∑ m, q (m, j) : ℝ) : ℂ)) := by
    ext j j'
    by_cases h : j = j'
    · subst h
      simp only [QAlgorithms.traceLeft, Matrix.of_apply, Matrix.diagonal_apply_eq, Complex.ofReal_sum]
    · rw [Matrix.diagonal_apply_ne _ h]
      simp only [QAlgorithms.traceLeft, Matrix.of_apply]
      exact Finset.sum_eq_zero
        (fun x _ => Matrix.diagonal_apply_ne _ (fun h' => h (congrArg Prod.snd h')))
  have hK : ∑ _m : Fin k, Real.negMulLog (1 / k) = Real.log k := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.negMulLog, one_div,
      Real.log_inv]
    field_simp
  have hF := fano_nat hk q hq hrow ε hs
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  unfold DattaDiscord.mutualInfo
  rw [hR, hL, vn_diag, vn_diag, vn_diag, hK, Real.logb]
  set Hr := ∑ j, Real.negMulLog (∑ m, q (m, j))
  set Hq := ∑ p, Real.negMulLog (q p)
  set A := Real.log k
  set L := Real.log 2
  have h5 : (1 - ε) * (A / L) - (1 + (A / L + Hr / L - Hq / L)) =
      ((1 - ε) * A - (A + Hr - Hq)) / L - 1 := by ring
  have h4 : ((1 - ε) * A - (A + Hr - Hq)) / L ≤ 1 := (div_le_one hlog2).mpr (by linarith)
  linarith

lemma cq_apply {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {n k : ℕ} (c : EACode a b n k) (N : QChannel a b) (m m' : Fin k)
    (x x' : (Fin n → b) × Fin c.dB) :
    EAConv.cqState c N (m, x) (m', x') =
      if m = m' then (1 / k : ℂ) * EAConv.outState c N m x x' else 0 := by
  unfold EAConv.cqState
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, smul_eq_mul]
  by_cases h : m = m'
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single m]
    · simp [Matrix.single_apply]
    · intro m0 _ hm0
      simp [Matrix.single_apply, hm0]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun m0 _ => ?_)
    by_cases h1 : m0 = m
    · subst h1
      simp [Matrix.single_apply, h]
    · simp [Matrix.single_apply, h1]

lemma psd_outState {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {n k : ℕ} (c : EACode a b n k) (N : QChannel a b) (m : Fin k) :
    (EAConv.outState c N m).PosSemidef :=
  EAConv.psd_leftApply _ (EAConv.psd_leftApply _ (EAConv.psd_pure _))

lemma tr_outState {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {n k : ℕ} (c : EACode a b n k) (N : QChannel a b) (m : Fin k) :
    (EAConv.outState c N m).trace = 1 := by
  rw [← SubaddAux.trace_tr_left, EAConv.outState_tl, SubaddAux.trace_tr_left,
    EAConv.trace_pure _ c.norm_Ψ]

/-- **D2** (Fano + Holevo for the decoder, Wilde §21.5): `(1-ε) log k ≤ 1 + I(M; Bⁿ T_B)_ω`. -/
theorem hD2 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (N : QChannel a b) (n k : ℕ) (c : EACode a b n k) (ε : ℝ) (hk : 0 < k) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) (herr : ∀ m, c.errorProb N m ≤ ε) :
    (1 - ε) * Real.logb 2 k ≤ 1 + DattaDiscord.mutualInfo (EAConv.cqState c N) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  obtain ⟨B, hBd⟩ : ∃ B : Fin k → Matrix ((Fin n → b) × Fin c.dB) ((Fin n → b) × Fin c.dB) ℂ,
      B = fun j => cfc Real.sqrt (c.dec j) := ⟨_, rfl⟩
  have hBB : ∀ j, (B j)ᴴ * B j = c.dec j := fun j => by rw [hBd]; exact sqrt_sq _ (c.dec_povm.1 j)
  have hB : ∑ j, (B j)ᴴ * B j = 1 := by simp_rw [hBB]; exact c.dec_povm.2
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hD : Nonempty ((Fin n → b) × Fin c.dB) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := tr_outState c N ⟨0, hk⟩
    rw [Matrix.trace, Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact zero_ne_one h1
  have hι : Nonempty (measCh B hB).ι := by
    obtain ⟨x⟩ := hD
    exact ⟨show Fin k × _ from (⟨0, hk⟩, x)⟩
  have hdp := DG5.mi_dp (measCh B hB) (EAConv.cqState c N) (EAConv.cqState_psd c N) hι
  obtain ⟨w, hwd⟩ : ∃ w : Fin k × Fin k → ℂ,
      w = fun p => (1 / k : ℂ) * (B p.2 * EAConv.outState c N p.1 * (B p.2)ᴴ).trace := ⟨_, rfl⟩
  have hkc : (1 : ℂ) / k = ((1 / k : ℝ) : ℂ) := by push_cast; ring
  have hk0c : (0 : ℂ) ≤ 1 / (k : ℂ) := by
    rw [hkc]
    exact Complex.zero_le_real.mpr (by positivity)
  have hw0 : ∀ p, 0 ≤ w p := fun p => by
    simp only [hwd]
    exact mul_nonneg hk0c (((psd_outState c N p.1).mul_mul_conjTranspose_same (B p.2)).trace_nonneg)
  have hre : ∀ p, (((w p).re : ℝ) : ℂ) = w p := fun p => by
    have h := Complex.nonneg_iff.mp (hw0 p)
    exact Complex.ext (by simp) (by simp [← h.2])
  have hout : idTensorApply (measCh B hB) (EAConv.cqState c N) =
      Matrix.diagonal (fun p => (((w p).re : ℝ) : ℂ)) := by
    ext ⟨m, y⟩ ⟨m', y'⟩
    rw [meas_out]
    simp only [hre, cq_apply]
    by_cases h1 : y = y'
    · by_cases h2 : m = m'
      · subst h1; subst h2
        rw [if_pos rfl, Matrix.diagonal_apply_eq]
        simp only [hwd, if_true, Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun e _ => ?_)
        exact Finset.sum_comm.trans
          (Finset.sum_congr rfl (fun x' _ => Finset.sum_congr rfl (fun x _ => by ring)))
      · simp [Matrix.diagonal_apply, h2]
    · simp [Matrix.diagonal_apply, h1]
  have hq : ∀ p, 0 ≤ (w p).re := fun p => (Complex.nonneg_iff.mp (hw0 p)).1
  have hrowC : ∀ m, ∑ j, w (m, j) = 1 / k := by
    intro m
    simp only [hwd]
    rw [← Finset.mul_sum]
    have e1 : ∀ j, (B j * EAConv.outState c N m * (B j)ᴴ).trace =
        ((B j)ᴴ * B j * EAConv.outState c N m).trace := fun j => Matrix.trace_mul_cycle _ _ _
    simp_rw [e1]
    rw [← Matrix.trace_sum, ← Finset.sum_mul, hB, Matrix.one_mul, tr_outState, mul_one]
  have hrowR : ∀ m, ∑ j, (w (m, j)).re = 1 / k := by
    intro m
    rw [← Complex.re_sum, hrowC, hkc, Complex.ofReal_re]
  have herr' : ∀ m, c.errorProb N m = 1 - ((c.dec m) * EAConv.outState c N m).trace.re := by
    intro m
    show ((1 - c.dec m) * EAConv.outState c N m).trace.re = _
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, tr_outState, Complex.sub_re, Complex.one_re]
  have hwm : ∀ m, (w (m, m)).re = (1 / k) * (1 - c.errorProb N m) := by
    intro m
    rw [herr' m]
    simp only [hwd]
    rw [Matrix.trace_mul_cycle, hBB, hkc, Complex.re_ofReal_mul]
    ring
  have hs : 1 - ε ≤ ∑ m, (w (m, m)).re := by
    simp_rw [hwm]
    calc 1 - ε = ∑ _m : Fin k, (1 / k : ℝ) * (1 - ε) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
            mul_one_div_cancel hk0, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun m _ =>
          mul_le_mul_of_nonneg_left (by linarith [herr m]) (by positivity))
  have hfano : (1 - ε) * Real.logb 2 k ≤
      1 + DattaDiscord.mutualInfo (Matrix.diagonal (fun p => (((w p).re : ℝ) : ℂ))) :=
    fano_diag hk (fun p => (w p).re) hq hrowR ε hs
  rw [← hout] at hfano
  linarith

end DG6

open WildeQIT WildeQIT.EADamping in
/-- C3 (converse of BSST) from the one-shot converse D1:
`(1 - ε) log₂ k ≤ 1 + n I(N)` for every `(n, k, ε)` EA code (Fano + Holevo + additivity). -/
theorem c3_of_oneShot {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (N : QChannel a b) (C : ℝ) (hC : IsAchievableEARate N C)
    (hD1 : ∀ (n k : ℕ) (c : EACode a b n k) (ε : ℝ), 0 < k → 0 ≤ ε → ε < 1 →
      (∀ m, c.errorProb N m ≤ ε) → (1 - ε) * Real.logb 2 k ≤ 1 + n * channelMutualInfo N) :
    C ≤ channelMutualInfo N := by
  set I := channelMutualInfo N with hI
  by_contra hlt
  rw [not_le] at hlt
  set g := C - I with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  set x := C - g / 2 with hx
  have hxg : 0 < |x| + g := by positivity
  set ε := g / (4 * (|x| + g)) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεq : ε * (4 * (|x| + g)) = g := by rw [hε]; field_simp
  have hε1 : ε < 1 := by nlinarith [abs_nonneg x]
  have hεx : ε * |x| ≤ g / 4 := by nlinarith [abs_nonneg x]
  set η := (1 - ε) * x - I with hη
  have hη0 : g / 4 ≤ η := by
    have h1 : ε * x ≤ ε * |x| := mul_le_mul_of_nonneg_left (le_abs_self x) hε0.le
    rw [hη, hx]; rw [hx] at h1; nlinarith
  have hηpos : 0 < η := by linarith
  obtain ⟨N₀, hN₀⟩ := hC ε hε0 hε1 (g / 2) (by positivity)
  set n : ℕ := N₀ + ⌈1 / η⌉₊ + 1 with hn
  obtain ⟨k, hk, c, herr⟩ := hN₀ n (by omega)
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hk
  have hlog : (n : ℝ) * x ≤ Real.logb 2 k := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hkpos]
    simpa [hx] using hk
  have hD := hD1 n k c ε (by exact_mod_cast hkpos) hε0.le hε1 herr
  have h1 : (1 - ε) * ((n : ℝ) * x) ≤ (1 - ε) * Real.logb 2 k :=
    mul_le_mul_of_nonneg_left hlog (by linarith)
  have hnη : (n : ℝ) * η ≤ 1 := by rw [hη]; nlinarith
  have hnbig : 1 / η < (n : ℝ) := by
    have := Nat.le_ceil (1 / η)
    have hcast : ((N₀ + ⌈1 / η⌉₊ + 1 : ℕ) : ℝ) = (N₀ : ℝ) + (⌈1 / η⌉₊ : ℝ) + 1 := by push_cast; ring
    rw [hn, hcast]
    have : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
    linarith
  have : 1 < (n : ℝ) * η := by
    rw [div_lt_iff₀ hηpos] at hnbig; linarith
  linarith

open WildeQIT WildeQIT.EADamping in
/-- D1 (one-shot converse): `(1-ε) log₂ k ≤ 1 + n I(N)` from D2 (Fano + Holevo) and D3. -/
theorem oneShot_conv {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (N : QChannel a b) (n k : ℕ) (c : EACode a b n k) (ε : ℝ) (hk : 0 < k) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) (herr : ∀ m, c.errorProb N m ≤ ε) :
    (1 - ε) * Real.logb 2 k ≤ 1 + n * channelMutualInfo N := by
  have h2 := DG6.hD2 N n k c ε hk hε0 hε1 herr
  have h3 := D3F.d3_full N n k c hk
  linarith

open WildeQIT WildeQIT.EADamping in
theorem solution {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] [Nonempty a] (N : QChannel a b) (C : ℝ)
    (hC : IsAchievableEARate N C) : C ≤ channelMutualInfo N := by
  exact c3_of_oneShot N C hC (fun n k c ε hk h0 h1 herr => oneShot_conv N n k c ε hk h0 h1 herr)
