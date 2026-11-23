-- Prove2me | solution 1 for OptimalTraceDistance.Estimation.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T05:30:31.08014+00:00
-- url     : https://prove2.me/submissions/570884b2-1779-4a5a-95a2-da35f37e839b

import Theorems.Thm_OptimalTraceDistance_Estimation_lemma_4_4
import Theorems.Thm_OptimalTraceDistance_Estimation_proposition_4_5
import Theorems.Thm_OptimalTraceDistance_Estimation_proposition_2_6
import Theorems.Thm_OptimalTraceDistance_Estimation_lemma_2_3

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder MatrixOrder
noncomputable section

namespace OTDProp32
open Matrix OptimalTraceDistance.Estimation

variable {d : ℕ}

lemma kron_mul {ι : Type*} [Fintype ι] {r : ℕ} (A B : Fin r → Matrix ι ι ℂ) :
    OptimalSpectrum.Entangled.kronFamily (fun j => A j * B j) =
      OptimalSpectrum.Entangled.kronFamily A * OptimalSpectrum.Entangled.kronFamily B := by
  ext x y
  simp only [OptimalSpectrum.Entangled.kronFamily, mul_apply, Matrix.of_apply]
  have := Fintype.prod_sum (fun (j : Fin r) (c : ι) => A j (x j) c * B j c (y j))
  rw [this]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.prod_mul_distrib]

lemma kron_conj {ι : Type*} [Fintype ι] {r : ℕ} (A : Fin r → Matrix ι ι ℂ) :
    (OptimalSpectrum.Entangled.kronFamily A)ᴴ =
      OptimalSpectrum.Entangled.kronFamily (fun j => (A j)ᴴ) := by
  ext x y
  simp [OptimalSpectrum.Entangled.kronFamily, conjTranspose_apply, star_prod]

lemma powerState_psd {ι : Type*} [Fintype ι] [DecidableEq ι] {τ : Matrix ι ι ℂ} (hτ : τ.PosSemidef)
    (n : ℕ) : (powerState τ n).PosSemidef := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hτ.nonneg
  have : powerState τ n = (OptimalSpectrum.Entangled.kronFamily (fun _ : Fin n => B))ᴴ *
      OptimalSpectrum.Entangled.kronFamily (fun _ : Fin n => B) := by
    rw [kron_conj, ← kron_mul]
    simp only [powerState, tensor, hB, Matrix.star_eq_conjTranspose]
  rw [this]; exact posSemidef_conjTranspose_mul_self _

lemma labelled_psd {d : ℕ} {ρ σ : Mat d} (hρ : Density ρ) (hσ : Density σ) :
    (labelledState ρ σ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · ext ⟨b, i⟩ ⟨b', j⟩
    simp only [labelledState, conjTranspose_apply]
    by_cases h : b' = b
    · subst h
      simp only [if_true]
      cases b'
      · simp only [Bool.false_eq_true, if_false, star_mul', star_inv₀, star_ofNat]
        rw [show star (ρ j i) = ρ i j from by
          have := congrFun (congrFun hρ.1.1 i) j; simpa [conjTranspose_apply] using this]
      · simp only [if_true, star_mul', star_inv₀, star_ofNat]
        rw [show star (σ j i) = σ i j from by
          have := congrFun (congrFun hσ.1.1 i) j; simpa [conjTranspose_apply] using this]
    · rw [if_neg h, if_neg (Ne.symm h)]; simp
  · set u : Fin d → ℂ := fun i => x (false, i)
    set w : Fin d → ℂ := fun i => x (true, i)
    have e : star x ⬝ᵥ (labelledState ρ σ *ᵥ x) =
        (2:ℂ)⁻¹ * (star u ⬝ᵥ (ρ *ᵥ u)) + (2:ℂ)⁻¹ * (star w ⬝ᵥ (σ *ᵥ w)) := by
      simp only [dotProduct, mulVec, labelledState, Fintype.sum_prod_type, Fintype.sum_bool,
        Pi.star_apply, u, w]
      simp [Finset.mul_sum, Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc]
      ring_nf
    rw [e]
    have h2 : (0:ℂ) ≤ (2:ℂ)⁻¹ := by
      rw [show (2:ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl]; exact_mod_cast (by norm_num : (0:ℝ) ≤ 2⁻¹)
    exact add_nonneg (mul_nonneg h2 (hρ.1.dotProduct_mulVec_nonneg u))
      (mul_nonneg h2 (hσ.1.dotProduct_mulVec_nonneg w))


lemma herm_smul_real' {ι : Type*} [Fintype ι] (c : ℝ) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    ((c : ℂ) • A).IsHermitian := by
  unfold IsHermitian at hA ⊢; rw [conjTranspose_smul, hA]; simp [Complex.conj_ofReal]

lemma discr {a b c : ℝ} (h : ∀ t : ℝ, 0 ≤ a + 2 * t * b + t^2 * c) : b^2 ≤ a * c := by
  have ha : 0 ≤ a := by simpa using h 0
  have hc : 0 ≤ c := by
    by_contra hc; push Not at hc
    set t := Real.sqrt ((a + 1) / (-c))
    have ht2 : t^2 = (a + 1) / (-c) := Real.sq_sqrt (by
      have : 0 < -c := by linarith
      positivity)
    have h1 := h t
    have h2 := h (-t)
    have hcne : c ≠ 0 := by linarith
    have e : t^2 * c = -(a + 1) := by
      rw [ht2, div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hcne]; ring
    nlinarith
  rcases eq_or_lt_of_le hc with h0 | hpos
  · subst h0
    have hb : b = 0 := by
      by_contra hb
      have := h (-(a + 1) / (2 * b))
      have : 2 * (-(a + 1) / (2 * b)) * b = -(a + 1) := by field_simp
      nlinarith
    subst hb; simp
  · have := h (-b / c)
    have e : a + 2 * (-b / c) * b + (-b / c)^2 * c = a - b^2 / c := by field_simp; ring
    rw [e] at this
    have : b^2 / c ≤ a := by linarith
    rw [div_le_iff₀ hpos] at this; linarith

section var
variable {ι : Type*} [Fintype ι] {R : Matrix ι ι ℂ}

def qf (R : Matrix ι ι ℂ) (A B : Matrix ι ι ℂ) : ℝ := (R * A * B).trace.re

def vr (R : Matrix ι ι ℂ) (G : Matrix ι ι ℂ) : ℝ := (R * (G * G)).trace.re - ((R * G).trace.re) ^ 2

lemma qf_nonneg (hR : R.PosSemidef) {H : Matrix ι ι ℂ} (hH : H.IsHermitian) : 0 ≤ qf R H H := by
  unfold qf
  have h1 : (R * H * H).trace = (H * R * H).trace := by
    rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
  have h2 : (Hᴴ * R * H).PosSemidef := hR.conjTranspose_mul_mul_same H
  rw [hH.eq] at h2
  rw [h1]; exact (Complex.nonneg_iff.mp h2.trace_nonneg).1

lemma qf_symm {A B : Matrix ι ι ℂ} (hR : R.IsHermitian) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    qf R A B = qf R B A := by
  unfold qf
  have : (R * B * A).trace = star ((R * A * B).trace) := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, conjTranspose_mul, hR.eq, hA.eq, hB.eq]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm B, Matrix.mul_assoc, Matrix.trace_mul_comm A,
      Matrix.mul_assoc]
  rw [this]; simp [Complex.star_def]

lemma qf_add_left (A A' B : Matrix ι ι ℂ) : qf R (A + A') B = qf R A B + qf R A' B := by
  unfold qf; rw [Matrix.mul_add, Matrix.add_mul, trace_add, Complex.add_re]

lemma qf_add_right (A B B' : Matrix ι ι ℂ) : qf R A (B + B') = qf R A B + qf R A B' := by
  unfold qf; rw [Matrix.mul_add, trace_add, Complex.add_re]

lemma qf_smul_left (t : ℝ) (A B : Matrix ι ι ℂ) : qf R ((t:ℂ) • A) B = t * qf R A B := by
  unfold qf; rw [Matrix.mul_smul, Matrix.smul_mul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

lemma qf_smul_right (t : ℝ) (A B : Matrix ι ι ℂ) : qf R A ((t:ℂ) • B) = t * qf R A B := by
  unfold qf; rw [Matrix.mul_smul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

lemma cauchy (hR : R.PosSemidef) {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    qf R A B ^ 2 ≤ qf R A A * qf R B B := by
  have key : ∀ t : ℝ, 0 ≤ qf R A A + 2 * t * qf R A B + t^2 * qf R B B := by
    intro t
    have h := qf_nonneg hR (hA.add (herm_smul_real' t hB))
    have e : qf R (A + (t:ℂ) • B) (A + (t:ℂ) • B) =
        qf R A A + 2 * t * qf R A B + t^2 * qf R B B := by
      rw [qf_add_left, qf_add_right, qf_add_right, qf_smul_right, qf_smul_left, qf_smul_left,
        qf_smul_right, qf_symm hR.1 hB hA]
      ring
    rw [e] at h; exact h
  exact discr key




lemma qf_neg (A : Matrix ι ι ℂ) : qf R (-A) (-A) = qf R A A := by
  unfold qf; simp

lemma sqrt_qf_add (hR : R.PosSemidef) {U V : Matrix ι ι ℂ} (hU : U.IsHermitian) (hV : V.IsHermitian) :
    Real.sqrt (qf R (U + V) (U + V)) ≤ Real.sqrt (qf R U U) + Real.sqrt (qf R V V) := by
  have h1 := qf_nonneg hR hU
  have h2 := qf_nonneg hR hV
  have hc := cauchy hR hU hV
  have e : qf R (U + V) (U + V) = qf R U U + 2 * qf R U V + qf R V V := by
    rw [qf_add_left, qf_add_right, qf_add_right, qf_symm hR.1 hV hU]; ring
  rw [Real.sqrt_le_left (by positivity), e]
  have : qf R U V ≤ Real.sqrt (qf R U U) * Real.sqrt (qf R V V) := by
    rw [← Real.sqrt_mul h1]
    exact Real.le_sqrt_of_sq_le hc
  nlinarith [Real.sq_sqrt h1, Real.sq_sqrt h2]

variable [DecidableEq ι]

lemma vr_eq (hR1 : R.trace.re = 1) (G : Matrix ι ι ℂ) :
    vr R G = qf R (G - (((R * G).trace.re : ℝ) : ℂ) • 1) (G - (((R * G).trace.re : ℝ) : ℂ) • 1) := by
  set m := (R * G).trace.re
  unfold vr qf
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    trace_sub, trace_smul, smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul, sq]
  rw [hR1, ← Matrix.mul_assoc]; ring

lemma vr_triangle (hR : R.PosSemidef) (hR1 : R.trace.re = 1) {A B C : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) (c : ℝ) :
    Real.sqrt (vr R (A + B - C + (c:ℂ) • 1)) ≤
      Real.sqrt (vr R A) + Real.sqrt (vr R B) + Real.sqrt (vr R C) := by
  set mA := (R * A).trace.re
  set mB := (R * B).trace.re
  set mC := (R * C).trace.re
  have hm : (R * (A + B - C + (c:ℂ) • 1)).trace.re = mA + mB - mC + c := by
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, trace_add,
      trace_sub, trace_smul, smul_eq_mul, Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul]
    rw [hR1, mul_one]
  have hX := hA.sub (herm_smul_real' mA isHermitian_one)
  have hY := hB.sub (herm_smul_real' mB isHermitian_one)
  have hZ := hC.sub (herm_smul_real' mC isHermitian_one)
  rw [vr_eq hR1, vr_eq hR1 A, vr_eq hR1 B, vr_eq hR1 C, hm]
  have e : A + B - C + (c:ℂ) • 1 - (((mA + mB - mC + c : ℝ)) : ℂ) • (1 : Matrix ι ι ℂ) =
      (A - (mA:ℂ) • 1) + ((B - (mB:ℂ) • 1) + -(C - (mC:ℂ) • 1)) := by
    push_cast; rw [add_smul, sub_smul, add_smul]; abel
  rw [e]
  refine (sqrt_qf_add hR hX (hY.add hZ.neg)).trans ?_
  have := sqrt_qf_add hR hY hZ.neg
  rw [qf_neg] at this
  linarith

end var


/-! ### foldl max -/

lemma foldl_max_ge : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => by simp
  | (b :: l), a => by
    have ih := foldl_max_ge l (max a b)
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨le_trans (le_max_left a b) ih.1, fun x hx => ?_⟩
    rcases hx with rfl | hx
    · exact le_trans (le_max_right a x) ih.1
    · exact ih.2 x hx

lemma foldl_max_le : ∀ (l : List ℕ) (a b : ℕ), a ≤ b → (∀ x ∈ l, x ≤ b) → l.foldl max a ≤ b
  | [], a, b, h, _ => by simpa using h
  | (c :: l), a, b, h, hl => by
    simp only [List.foldl_cons]
    exact foldl_max_le l _ b (max_le h (hl c (by simp))) (fun x hx => hl x (by simp [hx]))

lemma len_le_deg (g : TraceExpression d) (w : Word d) (hw : w ∈ g.words) :
    w.factors.length ≤ expressionDegree g :=
  (foldl_max_ge _ 0).2 _ (List.mem_map.mpr ⟨w, hw, rfl⟩)

lemma deg_le_of (g : TraceExpression d) (b : ℕ) (h : ∀ w ∈ g.words, w.factors.length ≤ b) :
    expressionDegree g ≤ b := by
  unfold expressionDegree
  refine foldl_max_le _ 0 b (Nat.zero_le b) (fun x hx => ?_)
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  exact h w hw

/-! ### kernels -/

def KL (k : ℕ) (L : MatrixExpression d) := (L.map (fun w => wordKernel w k)).sum

lemma KL_append (k : ℕ) (L₁ L₂ : MatrixExpression d) : KL k (L₁ ++ L₂) = KL k L₁ + KL k L₂ := by
  simp [KL]

lemma kron_scale0 {ι : Type*} [Fintype ι] {k : ℕ} (c : ℂ) (H : Fin (k+1) → Matrix ι ι ℂ) :
    OptimalSpectrum.Entangled.kronFamily (fun i => if i.val = 0 then c • H i else H i) =
      c • OptimalSpectrum.Entangled.kronFamily H := by
  ext x y
  simp only [OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.succ_ne_zero, if_false, ↓reduceIte, Matrix.smul_apply,
    smul_eq_mul]
  ring

lemma kernel_aux {k : ℕ} (S : (Fin k → Bool × Fin d) → ℂ)
    (V : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) (c : ℂ) :
    (fun x y : Fin k → Bool × Fin d => if (fun i => (x i).1) = (fun i => (y i).1) then
        S x * (c • V) (fun i => (x i).2) (fun i => (y i).2) else 0) =
      c • (fun x y : Fin k → Bool × Fin d => if (fun i => (x i).1) = (fun i => (y i).1) then
        S x * V (fun i => (x i).2) (fun i => (y i).2) else 0 : Matrix _ _ ℂ) := by
  funext x y
  show _ = c * _
  beta_reduce
  by_cases hb : (fun i => (x i).1) = (fun i => (y i).1)
  · simp only [hb, ↓reduceIte]
    have : (c • V) (fun i => (x i).2) (fun i => (y i).2) = c * V (fun i => (x i).2) (fun i => (y i).2) :=
      rfl
    rw [this]; ring
  · simp only [hb, ↓reduceIte, mul_zero]

lemma wordKernel_scale (c : ℝ) (w : Word d) (k : ℕ) (hk : 1 ≤ k) :
    wordKernel ⟨w.factors, (c:ℂ) • w.tail⟩ k = (c:ℂ) • wordKernel w k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  unfold wordKernel
  simp only
  by_cases h : w.factors.length = k' + 1
  · simp only [h, ↓reduceIte]
    have hK : tensor (k'+1) (fun i : Fin (k'+1) => if i.val = 0 then ((c:ℂ) • w.tail) *
        (w.factors[i.val]?.getD (1,false)).1 else (w.factors[i.val]?.getD (1,false)).1) =
        (c:ℂ) • tensor (k'+1) (fun i : Fin (k'+1) => if i.val = 0 then w.tail *
          (w.factors[i.val]?.getD (1,false)).1 else (w.factors[i.val]?.getD (1,false)).1) := by
      rw [← kron_scale0]
      congr 1; funext i; split_ifs <;> simp [Matrix.smul_mul]
    rw [hK, Matrix.mul_smul]
    exact kernel_aux _ _ _
  · simp only [h, ↓reduceIte, smul_zero]

lemma KL_scale (c : ℝ) (k : ℕ) (hk : 1 ≤ k) (L : MatrixExpression d) :
    KL k (exprScale c L) = (c:ℂ) • KL k L := by
  unfold KL exprScale
  induction L with
  | nil => simp
  | cons w L ih =>
    simp only [List.map_cons, List.sum_cons, List.map_map] at ih ⊢
    rw [smul_add, ← ih, wordKernel_scale c w k hk]

lemma KL_zero (k : ℕ) (L : MatrixExpression d) (h : ∀ w ∈ L, w.factors.length ≠ k) : KL k L = 0 := by
  unfold KL
  apply List.sum_eq_zero
  intro A hA
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hA
  unfold wordKernel; simp [h w hw]


/-! ### linearity -/

section lin
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma hermPart_add (A B : Matrix ι ι ℂ) : hermPart (A + B) = hermPart A + hermPart B := by
  unfold hermPart; rw [conjTranspose_add, ← smul_add]; congr 1; abel

lemma hermPart_sub (A B : Matrix ι ι ℂ) : hermPart (A - B) = hermPart A - hermPart B := by
  unfold hermPart; rw [conjTranspose_sub, ← smul_sub]; congr 1; abel

lemma hermPart_zero : hermPart (0 : Matrix ι ι ℂ) = 0 := by simp [hermPart]

lemma symmetrize_add {k : ℕ} (A B : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    symmetrize (A + B) = symmetrize A + symmetrize B := by
  unfold symmetrize
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 2; funext π; rw [Matrix.mul_add, Matrix.add_mul]

lemma symmetrize_sub {k : ℕ} (A B : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    symmetrize (A - B) = symmetrize A - symmetrize B := by
  unfold symmetrize
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  congr 2; funext π; rw [Matrix.mul_sub, Matrix.sub_mul]

lemma symmetrize_zero {k : ℕ} : symmetrize (0 : Matrix (Fin k → ι) (Fin k → ι) ℂ) = 0 := by
  simp [symmetrize]

lemma embed_add {k n : ℕ} (e : Fin k ↪ Fin n) (A B : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    embed e (A + B) = embed e A + embed e B := by
  ext x y; show embed e (A + B) x y = embed e A x y + embed e B x y
  unfold embed; split_ifs <;> simp

lemma embed_sub {k n : ℕ} (e : Fin k ↪ Fin n) (A B : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    embed e (A - B) = embed e A - embed e B := by
  ext x y; show embed e (A - B) x y = embed e A x y - embed e B x y
  unfold embed; split_ifs <;> simp

lemma uStat_add (n k : ℕ) (A B : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    uStatistic n k (A + B) = uStatistic n k A + uStatistic n k B := by
  unfold uStatistic; simp only [embed_add, Finset.sum_add_distrib, smul_add]

lemma uStat_sub (n k : ℕ) (A B : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    uStatistic n k (A - B) = uStatistic n k A - uStatistic n k B := by
  unfold uStatistic; simp only [embed_sub, Finset.sum_sub_distrib, smul_sub]

lemma uStat_zero (n k : ℕ) : uStatistic n k (0 : Matrix (Fin k → ι) (Fin k → ι) ℂ) = 0 := by
  have := uStat_sub n k (0 : Matrix (Fin k → ι) (Fin k → ι) ℂ) 0
  simpa using this

end lin

lemma eK_eq (g : TraceExpression d) (k : ℕ) : expressionKernel g k = hermPart (symmetrize (KL k g.words)) := rfl

lemma eK_zero (g : TraceExpression d) (k : ℕ) (hk : expressionDegree g < k) : expressionKernel g k = 0 := by
  rw [eK_eq, KL_zero k g.words (fun w hw => by have := len_le_deg g w hw; omega), symmetrize_zero,
    hermPart_zero]

lemma sumK_ext (g : TraceExpression d) (n D : ℕ) (hD : expressionDegree g ≤ D) :
    ∑ k ∈ Finset.Icc 1 D, uStatistic n k (expressionKernel g k) =
      ∑ k ∈ Finset.Icc 1 (expressionDegree g), uStatistic n k (expressionKernel g k) := by
  symm
  apply Finset.sum_subset
  · intro k hk; simp at hk ⊢; omega
  · intro k hk hk'
    simp at hk hk'
    rw [eK_zero g k (by omega), uStat_zero]

lemma obs_decomp (f g₁ g₂ g₃ : TraceExpression d) (n : ℕ)
    (hw : f.words = g₁.words ++ g₂.words ++ exprScale (-1) g₃.words) :
    ∃ c : ℝ, observable f n = observable g₁ n + observable g₂ n - observable g₃ n +
      (c:ℂ) • (1 : Matrix (Fin n → Bool × Fin d) (Fin n → Bool × Fin d) ℂ) := by
  set D := expressionDegree f
  have hlen3 : ∀ w ∈ exprScale (-1) g₃.words, w.factors.length ≤ D := fun w hw' =>
    len_le_deg f w (by rw [hw]; simp [hw'])
  have h1 : expressionDegree g₁ ≤ D := deg_le_of g₁ D (fun w hw' => len_le_deg f w (by rw [hw]; simp [hw']))
  have h2 : expressionDegree g₂ ≤ D := deg_le_of g₂ D (fun w hw' => len_le_deg f w (by rw [hw]; simp [hw']))
  have h3 : expressionDegree g₃ ≤ D := by
    refine deg_le_of g₃ D (fun w hw' => ?_)
    have := hlen3 ⟨w.factors, (((-1:ℝ)):ℂ) • w.tail⟩ (List.mem_map.mpr ⟨w, hw', rfl⟩)
    simpa using this
  have hK : ∀ k ∈ Finset.Icc 1 D, uStatistic n k (expressionKernel f k) =
      uStatistic n k (expressionKernel g₁ k) + uStatistic n k (expressionKernel g₂ k) -
        uStatistic n k (expressionKernel g₃ k) := by
    intro k hk
    simp at hk
    rw [eK_eq, eK_eq, eK_eq, eK_eq, hw, KL_append, KL_append, KL_scale (-1) k hk.1]
    rw [show KL k g₁.words + KL k g₂.words + ((((-1:ℝ)):ℂ) • KL k g₃.words) =
      KL k g₁.words + KL k g₂.words - KL k g₃.words by simp [sub_eq_add_neg]]
    rw [symmetrize_sub, symmetrize_add, hermPart_sub, hermPart_add, uStat_sub, uStat_add]
  refine ⟨(evaluate f 0 0).re - (evaluate g₁ 0 0).re - (evaluate g₂ 0 0).re + (evaluate g₃ 0 0).re, ?_⟩
  unfold observable
  rw [Finset.sum_congr rfl hK, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sumK_ext g₁ n D h1, sumK_ext g₂ n D h2, sumK_ext g₃ n D h3]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  module


/-! ### degrees -/

lemma pow_var_len (t : Bool) : ∀ k : ℕ, ∀ w ∈ exprPow (exprVar d t) k, w.factors.length = k
  | 0, w, hw => by simp [exprPow, exprConst] at hw; subst hw; rfl
  | k+1, w, hw => by
    simp only [exprPow, exprMul, exprVar, List.flatMap, List.map_cons, List.map_nil,
      List.mem_flatten, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hw
    obtain ⟨l, ⟨a, ha, rfl⟩, hw⟩ := hw
    rw [List.mem_singleton] at hw
    rw [hw]
    simp [wordMul, pow_var_len t k a ha]

lemma deg_poly_var (p : Polynomial ℝ) (t : Bool) :
    expressionDegree (traceExpr (exprPoly p (exprVar d t))) ≤ p.natDegree := by
  refine deg_le_of _ _ (fun w hw => ?_)
  simp only [traceExpr, exprPoly, List.mem_flatMap, Finset.mem_toList] at hw
  obtain ⟨k, hk, hw⟩ := hw
  simp only [exprScale, List.mem_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  rw [pow_var_len t k w' hw']
  exact Polynomial.le_natDegree_of_mem_supp k hk

lemma subst_len (Q : Mat d) (g : TraceExpression d) :
    ∀ w ∈ (substituteCompression Q g).words, ∃ w' ∈ g.words, w.factors.length = w'.factors.length := by
  intro w hw
  simp only [substituteCompression, List.mem_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  refine ⟨w', hw', ?_⟩
  rcases w' with ⟨fs, tl⟩
  cases fs <;> simp

lemma deg_subst (Q : Mat d) (g : TraceExpression d) :
    expressionDegree (substituteCompression Q g) ≤ expressionDegree g := by
  refine deg_le_of _ _ (fun w hw => ?_)
  obtain ⟨w', hw', he⟩ := subst_len Q g w hw
  rw [he]; exact len_le_deg g w' hw'

lemma subst_one (g : TraceExpression d) : substituteCompression (1 : Mat d) g = g := by
  rcases g with ⟨c, ws⟩
  simp only [substituteCompression, TraceExpression.mk.injEq, true_and]
  conv_rhs => rw [← List.map_id ws]
  refine List.map_congr_left (fun w _ => ?_)
  rcases w with ⟨fs, tl⟩
  cases fs with
  | nil => rfl
  | cons At xs =>
    simp

/-! ### Hermitian observables -/

lemma herm_finsum {ι κ : Type*} [Fintype ι] (S : Finset κ) (A : κ → Matrix ι ι ℂ)
    (h : ∀ k ∈ S, (A k).IsHermitian) : (∑ k ∈ S, A k).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_sum]
  exact Finset.sum_congr rfl (fun k hk => h k hk)

lemma embed_herm {ι : Type*} [Fintype ι] [DecidableEq ι] {k n : ℕ} (e : Fin k ↪ Fin n)
    {H : Matrix (Fin k → ι) (Fin k → ι) ℂ} (hH : H.IsHermitian) : (embed e H).IsHermitian := by
  ext x y
  simp only [conjTranspose_apply, embed]
  have hc : (∀ i, i ∉ Set.range e → y i = x i) ↔ (∀ i, i ∉ Set.range e → x i = y i) :=
    ⟨fun h i hi => (h i hi).symm, fun h i hi => (h i hi).symm⟩
  by_cases h : ∀ i, i ∉ Set.range e → x i = y i
  · rw [if_pos (hc.mpr h), if_pos h]
    have := congrFun (congrFun hH (x ∘ e)) (y ∘ e)
    simpa [conjTranspose_apply] using this
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h, star_zero]

lemma uStat_herm {ι : Type*} [Fintype ι] [DecidableEq ι] (n k : ℕ)
    {H : Matrix (Fin k → ι) (Fin k → ι) ℂ} (hH : H.IsHermitian) : (uStatistic n k H).IsHermitian := by
  unfold uStatistic
  have hs : (∑ e : Fin k ↪ Fin n, embed e H).IsHermitian :=
    herm_finsum _ _ (fun e _ => embed_herm e hH)
  unfold IsHermitian at hs ⊢
  rw [conjTranspose_smul, hs]; congr 1; simp

lemma hermPart_herm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : (hermPart A).IsHermitian := by
  unfold hermPart IsHermitian
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]; simp

lemma obs_herm (g : TraceExpression d) (n : ℕ) : (observable g n).IsHermitian := by
  unfold observable
  refine IsHermitian.add ?_ (herm_finsum _ _ (fun k _ => uStat_herm n k (hermPart_herm _)))
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact herm_smul_real' _ isHermitian_one


lemma trace_powerState {ι : Type*} [Fintype ι] (τ : Matrix ι ι ℂ) (n : ℕ) :
    (powerState τ n).trace = τ.trace ^ n := by
  simp only [powerState, tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.trace, Matrix.diag,
    Matrix.of_apply]
  have h := Fintype.prod_sum (fun (_ : Fin n) (i : ι) => τ i i)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [h]

lemma trace_labelled {d : ℕ} {ρ σ : Mat d} (hρ : Density ρ) (hσ : Density σ) :
    (labelledState ρ σ).trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, labelledState, if_true, Fintype.sum_prod_type,
    Fintype.sum_bool, if_false, Bool.false_eq_true]
  have h1 := hρ.2; have h2 := hσ.2
  simp only [Matrix.trace, Matrix.diag] at h1 h2
  rw [← Finset.mul_sum, ← Finset.mul_sum, h1, h2]; norm_num


lemma log_pow_le {x : ℝ} (hx : 1 ≤ x) (k : ℕ) (hk : 1 ≤ k) :
    Real.log x ^ k ≤ (k:ℝ)^k * x := by
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have h := Real.log_le_rpow_div (x := x) (by linarith) (by positivity : (0:ℝ) < 1/k)
  have h2 : Real.log x ≤ k * x ^ ((1:ℝ)/k) := by
    rw [div_eq_mul_inv, show ((1:ℝ)/k)⁻¹ = k by field_simp] at h; linarith
  have h3 := pow_le_pow_left₀ hL h2 k
  rw [mul_pow, ← Real.rpow_natCast (x ^ ((1:ℝ)/k)), ← Real.rpow_mul (by linarith)] at h3
  rw [show (1:ℝ)/k * (k:ℕ) = 1 by field_simp, Real.rpow_one] at h3
  exact h3

lemma log4_le_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 4 ≤ 4096 * Real.sqrt x := by
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have h := Real.log_le_rpow_div (x := x) (by linarith) (by norm_num : (0:ℝ) < 1/8)
  have h2 : Real.log x ≤ 8 * x ^ ((1:ℝ)/8) := by
    rw [div_eq_mul_inv, show ((1:ℝ)/8)⁻¹ = 8 by norm_num] at h; linarith
  have h3 := pow_le_pow_left₀ hL h2 4
  rw [mul_pow, ← Real.rpow_natCast (x ^ ((1:ℝ)/8)), ← Real.rpow_mul (by linarith)] at h3
  rw [Real.sqrt_eq_rpow]
  norm_num at h3 ⊢; linarith

lemma exp_le_of_le_log {x L : ℝ} {d : ℝ} (hd : 0 < d) (hL : L = Real.log d) (h : x ≤ L) :
    Real.exp x ≤ d := by
  calc Real.exp x ≤ Real.exp L := Real.exp_le_exp.mpr h
    _ = d := by rw [hL, Real.exp_log hd]

lemma exp_sub_one_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.exp t - 1 ≤ 2 * t := by
  have := Real.add_one_le_exp t
  have hconv : Real.exp t ≤ 1 + (Real.exp 1 - 1) * t := by
    have := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ 1) (by linarith : (0:ℝ) ≤ 1 - t) h0
      (by ring : (1 - t) + t = 1)
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at this
    linarith
  have he : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  nlinarith


/-! numeric lemmas, with abstract constants -/

lemma log_facts {d : ℕ} (hd : 2 ≤ d) :
    0 < Real.log d ∧ ∀ k : ℕ, k ≤ 10 → Real.log d ^ k ≤ 2 * 10^10 * d := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hL : 0 < Real.log d := Real.log_pos (by linarith)
  refine ⟨hL, fun k hk => ?_⟩
  have h10 : Real.log d ^ 10 ≤ (10:ℝ)^10 * d := by
    have := log_pow_le (x := d) (by linarith) 10 (by norm_num); simpa using this
  have hk' : Real.log d ^ k ≤ 1 + Real.log d ^ 10 := by
    rcases le_total (Real.log d) 1 with h | h
    · have := pow_le_one₀ hL.le h (n := k); have : 0 ≤ Real.log d ^ 10 := by positivity
      linarith
    · have := pow_le_pow_right₀ h hk; linarith
  nlinarith


lemma big_le {a C X : ℝ} (hC : 0 ≤ C) (ha : a ≤ 2^250) (hX : 0 ≤ X) :
    a * X ≤ 2^250 * (1 + C) * X := by
  apply mul_le_mul_of_nonneg_right _ hX
  nlinarith

lemma big_le' {a C X : ℝ} (hC : 0 ≤ C) (ha0 : 0 ≤ a) (ha : a ≤ 2^250) (hX : 0 ≤ X) :
    a * C * X ≤ 2^250 * (1 + C) * X := by
  apply mul_le_mul_of_nonneg_right _ hX
  nlinarith [mul_le_mul_of_nonneg_right ha hC]

lemma corr_num {C44 Kk : ℝ} (hC : 0 < C44) (hK : 2^250 * (1 + C44) ≤ Kk)
    {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/32) {n : ℕ}
    (hn : Kk * (d:ℝ)^2 / (ε^2 * Real.log d ^ 2 * (1 + Real.log d ^ 2)) ≤ n) :
    2 ≤ ⌈2^40 * Real.log d / ε⌉₊ ∧ 2 * ⌈2^40 * Real.log d / ε⌉₊ ≤ n ∧
      (Real.exp (C44 * ((⌈2^40 * Real.log d / ε⌉₊ : ℕ) : ℝ)^2 / n) - 1) /
        ((⌈2^40 * Real.log d / ε⌉₊ : ℕ) : ℝ)^2 ≤ ε^2/1024 := by
  obtain ⟨hL, hLk⟩ := log_facts hd
  set L := Real.log d
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hL2 : 1/2 < L := by
    have h2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hdR
    have := Real.log_two_gt_d9; linarith
  set x := 2^40 * L / ε with hx
  have hx2 : 2 ≤ x := by rw [hx, le_div_iff₀ hε]; linarith
  set Kc := ⌈x⌉₊
  have hKc1 : x ≤ Kc := Nat.le_ceil x
  have hKc2 : (Kc:ℝ) ≤ 2 * x := by have := Nat.ceil_lt_add_one (by linarith : 0 ≤ x); linarith
  have hKcpos : (0:ℝ) < Kc := by linarith
  have hKK : 0 < Kk := lt_of_lt_of_le (by positivity) hK
  set D := ε^2 * L^2 * (1 + L^2) with hD
  have hDpos : 0 < D := by positivity
  set B := Kk * (d:ℝ)^2 / D with hB
  have hnpos : (0:ℝ) < n := lt_of_lt_of_le (by positivity) hn
  have hL2' := hLk 2 (by norm_num); have hL3 := hLk 3 (by norm_num)
  have hL4 := hLk 4 (by norm_num); have hL5 := hLk 5 (by norm_num); have hL6 := hLk 6 (by norm_num)
  have hdd : (d:ℝ) ≤ (d:ℝ)^2 := le_self_pow₀ (by linarith) (by norm_num)
  have hKd : 2^250 * (1 + C44) * (d:ℝ)^2 ≤ Kk * (d:ℝ)^2 :=
    mul_le_mul_of_nonneg_right hK (by positivity)
  refine ⟨by exact_mod_cast (le_trans hx2 hKc1 : (2:ℝ) ≤ Kc), ?_, ?_⟩
  · have hmain : 4 * x ≤ B := by
      rw [hB, le_div_iff₀ hDpos]
      have e : 4 * x * D = 2^42 * ε * (L^3 + L^5) := by rw [hx, hD]; field_simp; ring
      rw [e]
      have h1 : 2^42 * ε * (L^3 + L^5) ≤ 2^42 * (L^3 + L^5) := by
        have : 0 ≤ L^3 + L^5 := by positivity
        nlinarith only [this, hε1]
      have h2 : 2^42 * (L^3 + L^5) ≤ 2^42 * (4 * 10^10 * (d:ℝ)^2) := by linarith only [hL3, hL5, hdd]
      have h3 : 2^42 * (4 * 10^10 * (d:ℝ)^2) ≤ 2^250 * (1 + C44) * (d:ℝ)^2 := by
        rw [← mul_assoc]; exact big_le hC.le (by norm_num) (by positivity)
      exact le_trans h1 (le_trans h2 (le_trans h3 hKd))
    have : 2 * (Kc:ℝ) ≤ n := by linarith
    exact_mod_cast this
  · set t := C44 * (Kc:ℝ)^2 / n
    have ht0 : 0 ≤ t := by positivity
    have hKc_sq : (Kc:ℝ)^2 ≤ 4 * x^2 := by nlinarith only [hKc2, hKcpos]
    have hmain2 : C44 * (4 * x^2) ≤ B := by
      rw [hB, le_div_iff₀ hDpos]
      have e : C44 * (4 * x^2) * D = 2^82 * C44 * (L^4 + L^6) := by rw [hx, hD]; field_simp; ring
      rw [e]
      have h2 : 2^82 * C44 * (L^4 + L^6) ≤ 2^82 * C44 * (4 * 10^10 * (d:ℝ)^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith only [hL4, hL6, hdd]
      have h3 : 2^82 * C44 * (4 * 10^10 * (d:ℝ)^2) ≤ 2^250 * (1 + C44) * (d:ℝ)^2 := by
        rw [show 2^82 * C44 * (4 * 10^10 * (d:ℝ)^2) = (2^82 * (4 * 10^10)) * C44 * (d:ℝ)^2 by ring]
        exact big_le' hC.le (by norm_num) (by norm_num) (by positivity)
      exact le_trans h2 (le_trans h3 hKd)
    have ht1 : t ≤ 1 := by
      rw [div_le_one hnpos]
      exact le_trans (mul_le_mul_of_nonneg_left hKc_sq hC.le) (hmain2.trans hn)
    calc (Real.exp t - 1) / (Kc:ℝ)^2 ≤ 2 * t / (Kc:ℝ)^2 :=
          div_le_div_of_nonneg_right (exp_sub_one_le ht0 ht1) (by positivity)
      _ = 2 * C44 / n := by simp only [t]; field_simp
      _ ≤ 2 * C44 / B := div_le_div_of_nonneg_left (by positivity) (by positivity) hn
      _ ≤ ε^2 / 1024 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num), hB]
          rw [show ε^2 * (Kk * (d:ℝ)^2 / D) = Kk * (d:ℝ)^2 / (L^2 * (1 + L^2)) by
            rw [hD]; field_simp]
          rw [le_div_iff₀ (by positivity)]
          have h2 : 2 * C44 * 1024 * (L^2 * (1 + L^2)) ≤ 2048 * C44 * (4 * 10^10 * (d:ℝ)^2) := by
            rw [show 2 * C44 * 1024 * (L^2 * (1 + L^2)) = 2048 * C44 * (L^2 + L^4) by ring]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith only [hL2', hL4, hdd]
          have h3 : 2048 * C44 * (4 * 10^10 * (d:ℝ)^2) ≤ 2^250 * (1 + C44) * (d:ℝ)^2 := by
            rw [show 2048 * C44 * (4 * 10^10 * (d:ℝ)^2) = (2048 * (4 * 10^10)) * C44 * (d:ℝ)^2 by ring]
            exact big_le' hC.le (by norm_num) (by norm_num) (by positivity)
          exact le_trans h2 (le_trans h3 hKd)


set_option maxHeartbeats 2000000 in
lemma case1_num {C44 Kk : ℝ} (hC : 0 < C44) (hK : 2^250 * (1 + C44)^2 ≤ Kk)
    {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/32) {n : ℕ}
    (hn : Kk * (d:ℝ)^2 / (ε^2 * Real.log d ^ 2) ≤ n) :
    2 ≤ ⌈2^40 * (d:ℝ) / ε⌉₊ ∧ 2 * ⌈2^40 * (d:ℝ) / ε⌉₊ ≤ n ∧
      1/(n:ℝ) + (Real.exp (C44 * ((⌈2^40 * (d:ℝ) / ε⌉₊ : ℕ) : ℝ) / Real.sqrt n) +
        Real.exp (C44 * (1 / Real.log d) * ((⌈2^40 * (d:ℝ) / ε⌉₊ : ℕ) : ℝ)^2 / n)) /
          ((⌈2^40 * (d:ℝ) / ε⌉₊ : ℕ) : ℝ)^2 ≤ ε^2/256 := by
  obtain ⟨hL, hLk⟩ := log_facts hd
  set L := Real.log d with hLdef
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0:ℝ) < d := by linarith
  set x := 2^40 * (d:ℝ) / ε with hx
  have hx2 : 2 ≤ x := by rw [hx, le_div_iff₀ hε]; linarith
  set Kr := ⌈x⌉₊
  have hK1 : x ≤ Kr := Nat.le_ceil x
  have hK2 : (Kr:ℝ) ≤ 2 * x := by have := Nat.ceil_lt_add_one (by linarith : 0 ≤ x); linarith
  have hKrpos : (0:ℝ) < Kr := by linarith
  have hKK : 0 < Kk := lt_of_lt_of_le (by positivity) hK
  set B := Kk * (d:ℝ)^2 / (ε^2 * L^2) with hB
  have hBpos : 0 < B := by positivity
  have hnpos : (0:ℝ) < n := lt_of_lt_of_le hBpos hn
  have hL2 := hLk 2 (by norm_num)
  have hdd : (d:ℝ) ≤ (d:ℝ)^2 := le_self_pow₀ (by linarith) (by norm_num)
  have hC1 : (1:ℝ) ≤ (1 + C44)^2 := by nlinarith only [hC]
  have hKbig : 2^250 ≤ Kk := le_trans (by nlinarith only [hC1]) hK
  refine ⟨by exact_mod_cast (le_trans hx2 hK1 : (2:ℝ) ≤ Kr), ?_, ?_⟩
  · have hmain : 4 * x ≤ B := by
      rw [hB, le_div_iff₀ (by positivity)]
      have e : 4 * x * (ε^2 * L^2) = 2^42 * ε * (L^2 * d) := by rw [hx]; field_simp; ring
      rw [e]
      have h1 : 2^42 * ε * (L^2 * d) ≤ 2^42 * (2 * 10^10 * d * d) := by
        have : L^2 * d ≤ 2 * 10^10 * d * d := mul_le_mul_of_nonneg_right hL2 hdpos.le
        have h0 : 0 ≤ L^2 * d := by positivity
        nlinarith only [this, h0, hε1]
      have h2 : 2^42 * (2 * 10^10 * d * d) ≤ Kk * (d:ℝ)^2 := by
        have : 2^42 * (2 * 10^10 * d * d) = (2^42 * (2 * 10^10)) * (d:ℝ)^2 := by ring
        rw [this]; exact mul_le_mul_of_nonneg_right (le_trans (by norm_num) hKbig) (by positivity)
      linarith
    have : 2 * (Kr:ℝ) ≤ n := by linarith
    exact_mod_cast this
  · -- exponent bounds
    have hBs : Real.sqrt B = Real.sqrt Kk * d / (ε * L) := by
      rw [hB, Real.sqrt_div (by positivity), Real.sqrt_mul hKK.le, Real.sqrt_sq hdpos.le,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hε.le, Real.sqrt_sq hL.le]
    have hsq : Real.sqrt Kk * d / (ε * L) ≤ Real.sqrt n := hBs ▸ Real.sqrt_le_sqrt hn
    have hsK : 2^41 * C44 ≤ Real.sqrt Kk := by
      rw [show 2^41 * C44 = Real.sqrt ((2^41 * C44)^2) by rw [Real.sqrt_sq (by positivity)]]
      apply Real.sqrt_le_sqrt
      refine le_trans ?_ hK
      nlinarith only [hC]
    have he1 : C44 * Kr / Real.sqrt n ≤ L := by
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
      rw [div_le_iff₀ hsn]
      calc C44 * (Kr:ℝ) ≤ C44 * (2 * x) := mul_le_mul_of_nonneg_left hK2 hC.le
        _ = 2^41 * C44 * (d / ε) := by rw [hx]; ring
        _ ≤ Real.sqrt Kk * (d / ε) := mul_le_mul_of_nonneg_right hsK (by positivity)
        _ = L * (Real.sqrt Kk * d / (ε * L)) := by field_simp
        _ ≤ L * Real.sqrt n := mul_le_mul_of_nonneg_left hsq hL.le
    have he2 : C44 * (1 / L) * (Kr:ℝ)^2 / n ≤ L := by
      rw [div_le_iff₀ hnpos]
      have hKsq : (Kr:ℝ)^2 ≤ 4 * x^2 := by nlinarith only [hK2, hKrpos]
      calc C44 * (1 / L) * (Kr:ℝ)^2 ≤ C44 * (1 / L) * (4 * x^2) :=
            mul_le_mul_of_nonneg_left hKsq (by positivity)
        _ = L * (2^82 * C44 * d^2 / (ε^2 * L^2)) := by rw [hx]; field_simp; ring
        _ ≤ L * B := by
            apply mul_le_mul_of_nonneg_left _ hL.le
            rw [hB]; apply div_le_div_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            refine le_trans ?_ hK; nlinarith only [hC]
        _ ≤ L * n := mul_le_mul_of_nonneg_left hn hL.le
    have hE1 := exp_le_of_le_log hdpos hLdef he1
    have hE2 := exp_le_of_le_log hdpos hLdef he2
    have t1 : 1/(n:ℝ) ≤ ε^2/512 := by
      calc 1/(n:ℝ) ≤ 1/B := div_le_div_of_nonneg_left (by norm_num) hBpos hn
        _ = ε^2 * L^2 / (Kk * d^2) := by rw [hB]; field_simp
        _ ≤ ε^2/512 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            have : 512 * L^2 ≤ Kk * d^2 := by
              have h1 : 512 * L^2 ≤ 512 * (2 * 10^10 * (d:ℝ)^2) := by linarith only [hL2, hdd]
              have h2 : 512 * (2 * 10^10 * (d:ℝ)^2) ≤ Kk * (d:ℝ)^2 := by
                rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_trans (by norm_num) hKbig) (by positivity)
              linarith
            nlinarith only [this, sq_nonneg ε]
    have t2 : (Real.exp (C44 * Kr / Real.sqrt n) + Real.exp (C44 * (1 / L) * (Kr:ℝ)^2 / n)) / (Kr:ℝ)^2
        ≤ ε^2/512 := by
      calc _ ≤ (2 * d) / (Kr:ℝ)^2 := div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ ≤ (2 * d) / x^2 := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            exact pow_le_pow_left₀ (by linarith) hK1 2
        _ = 2 * ε^2 / (2^80 * d) := by rw [hx]; field_simp
        _ ≤ ε^2/512 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith only [sq_nonneg ε, hdR]
    linarith


lemma le_root {y n : ℝ} (hy : 0 ≤ y) (k : ℕ) (hk : 0 < k) (h : y ^ k ≤ n) : y ≤ n ^ (1 / (k:ℝ)) := by
  have := Real.rpow_le_rpow (by positivity) h (by positivity : (0:ℝ) ≤ 1 / (k:ℝ))
  rwa [← Real.rpow_natCast, ← Real.rpow_mul hy, mul_one_div_cancel (by positivity), Real.rpow_one] at this

lemma root_le {y n : ℝ} (hn : 0 ≤ n) (hy : 0 ≤ y) (k : ℕ) (hk : 0 < k) (h : n ≤ y ^ k) : n ^ (1 / (k:ℝ)) ≤ y := by
  have := Real.rpow_le_rpow hn h (by positivity : (0:ℝ) ≤ 1 / (k:ℝ))
  rwa [← Real.rpow_natCast, ← Real.rpow_mul hy, mul_one_div_cancel (by positivity), Real.rpow_one] at this

set_option maxHeartbeats 2000000 in
lemma case2_num {C45 Kk : ℝ} (hC : 0 < C45) (hK : 2^250 * (1 + C45)^4 ≤ Kk)
    {d : ℕ} (hd : 2 ≤ d) (hdbig : 2^28 * C45 ≤ Real.sqrt d) {ε : ℝ} (hε : 0 < ε)
    (hεL : 1 < ε * Real.log d) {n : ℕ}
    (hn : Kk * (d:ℝ)^2 / (ε^4 * Real.log d ^ 4) ≤ n) :
    C45 * (Real.log d)^2 / ((ε/8)^6 * n) + C45 / ((d:ℝ)^2 * (ε/8)^2) *
      (Real.exp (C45 * Real.sqrt d / ((ε/8) * (n:ℝ)^(1/4:ℝ))) +
        Real.exp (C45 * ((1 / Real.log d) * (d:ℝ)^2 / ((ε/8)^4 * n))^(1/3:ℝ))) ≤ ε^2/256 := by
  obtain ⟨hL, hLk⟩ := log_facts hd
  set L := Real.log d with hLdef
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0:ℝ) < d := by linarith
  have hKK : 0 < Kk := lt_of_lt_of_le (by positivity) hK
  have hC1 : (1:ℝ) ≤ (1 + C45)^4 := one_le_pow₀ (by linarith)
  have hKbig : 2^250 ≤ Kk := le_trans (by nlinarith only [hC1]) hK
  have hK4 : 4096 * C45^4 ≤ Kk := by
    refine le_trans ?_ hK
    have : C45^4 ≤ (1 + C45)^4 := pow_le_pow_left₀ hC.le (by linarith) 4
    nlinarith only [this, hC1]
  have hK3 : 4096 * C45^3 ≤ Kk := by
    refine le_trans ?_ hK
    have : C45^3 ≤ (1 + C45)^4 := by
      have h1 : C45^3 ≤ (1 + C45)^3 := pow_le_pow_left₀ hC.le (by linarith) 3
      have h2 : (1 + C45)^3 ≤ (1 + C45)^4 := pow_le_pow_right₀ (by linarith) (by norm_num)
      linarith
    nlinarith only [this, hC1]
  set B := Kk * (d:ℝ)^2 / (ε^4 * L^4) with hB
  have hBpos : 0 < B := by positivity
  have hnpos : (0:ℝ) < n := lt_of_lt_of_le hBpos hn
  have hεL4 : 1 ≤ ε^4 * L^4 := by
    have := pow_le_pow_left₀ (by norm_num) hεL.le 4; rw [mul_pow] at this; simpa using this
  have hL10 := hLk 10 (by norm_num)
  have hdd : (d:ℝ) ≤ (d:ℝ)^2 := le_self_pow₀ (by linarith) (by norm_num)
  -- term 1
  have t1 : C45 * L^2 / ((ε/8)^6 * n) ≤ ε^2/512 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hn' : B ≤ n := hn
    have step : ε^2 * ((ε/8)^6 * B) = Kk * (d:ℝ)^2 * (ε^4) / (8^6 * L^4) := by
      rw [hB]; field_simp
    have h1 : ε^2 * ((ε/8)^6 * B) ≤ ε^2 * ((ε/8)^6 * n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hn' (by positivity)
    have h2 : Kk * (d:ℝ)^2 / (8^6 * L^8) ≤ Kk * (d:ℝ)^2 * (ε^4) / (8^6 * L^4) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : Kk * (d:ℝ)^2 * (8^6 * L^4) * 1 ≤ Kk * (d:ℝ)^2 * (8^6 * L^4) * (ε^4 * L^4) :=
        mul_le_mul_of_nonneg_left hεL4 (by positivity)
      have e1 : Kk * (d:ℝ)^2 * (8^6 * L^4) * (ε^4 * L^4) = Kk * (d:ℝ)^2 * ε^4 * (8^6 * L^8) := by ring
      linarith
    have h3 : C45 * L^2 * 512 ≤ Kk * (d:ℝ)^2 / (8^6 * L^8) := by
      rw [le_div_iff₀ (by positivity)]
      have e : C45 * L^2 * 512 * (8^6 * L^8) = (512 * 8^6) * C45 * L^10 := by ring
      rw [e]
      have h4 : (512 * 8^6) * C45 * L^10 ≤ (512 * 8^6) * C45 * (2 * 10^10 * d^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith only [hL10, hdd]
      have h5 : (512 * 8^6) * C45 * (2 * 10^10 * (d:ℝ)^2) ≤ Kk * (d:ℝ)^2 := by
        rw [show (512 * 8^6) * C45 * (2 * 10^10 * (d:ℝ)^2) = ((512 * 8^6 * (2 * 10^10)) * C45) * (d:ℝ)^2 by ring]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        refine le_trans ?_ hK
        have : C45 ≤ (1 + C45)^4 := by
          have h1 : C45 ≤ 1 + C45 := by linarith
          have h2 : (1 + C45) ≤ (1 + C45)^4 := by
            calc (1 + C45) = (1 + C45)^1 := (pow_one _).symm
              _ ≤ (1 + C45)^4 := pow_le_pow_right₀ (by linarith) (by norm_num)
          linarith
        nlinarith only [this, hC]
      linarith
    rw [step] at h1
    linarith
  -- exponent 1
  have he1 : C45 * Real.sqrt d / ((ε/8) * (n:ℝ)^(1/4:ℝ)) ≤ L := by
    set y := 8 * C45 * Real.sqrt d / (ε * L) with hy
    have hy0 : 0 ≤ y := by positivity
    have hy4 : y^4 ≤ n := by
      refine le_trans ?_ hn
      rw [hy, hB, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have e1 : (8 * C45 * Real.sqrt d)^4 = 4096 * C45^4 * (d:ℝ)^2 := by
        rw [mul_pow, mul_pow, show (Real.sqrt d)^4 = ((Real.sqrt d)^2)^2 by ring,
          Real.sq_sqrt hdpos.le]; ring
      rw [e1, mul_pow]
      have : 4096 * C45^4 * (d:ℝ)^2 ≤ Kk * (d:ℝ)^2 := mul_le_mul_of_nonneg_right hK4 (by positivity)
      have hpos : 0 ≤ ε^4 * L^4 := by positivity
      nlinarith only [this, hpos, hεL4, hKK, hdd, hdR]
    have hroot := le_root hy0 4 (by norm_num) hy4
    norm_num at hroot
    have hn4 : 0 < (n:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos hnpos _
    rw [div_le_iff₀ (by positivity)]
    have : C45 * Real.sqrt d = (ε/8) * L * y := by rw [hy]; field_simp
    rw [this]
    have hh : (ε/8) * L * y ≤ (ε/8) * L * (n:ℝ)^(1/4:ℝ) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    linarith
  -- exponent 2
  have he2 : C45 * ((1 / L) * (d:ℝ)^2 / ((ε/8)^4 * n))^(1/3:ℝ) ≤ L := by
    have hin : (1 / L) * (d:ℝ)^2 / ((ε/8)^4 * n) ≤ (L / C45)^3 := by
      have h1 : (1 / L) * (d:ℝ)^2 / ((ε/8)^4 * n) ≤ (1 / L) * (d:ℝ)^2 / ((ε/8)^4 * B) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hn (by positivity))
      have h2 : (1 / L) * (d:ℝ)^2 / ((ε/8)^4 * B) = 4096 * L^3 / Kk := by
        rw [hB]; field_simp; ring
      have h3 : 4096 * L^3 / Kk ≤ (L / C45)^3 := by
        rw [div_pow, div_le_div_iff₀ hKK (by positivity)]
        have : 4096 * C45^3 * L^3 ≤ Kk * L^3 := mul_le_mul_of_nonneg_right hK3 (by positivity)
        linarith
      linarith
    have hr := root_le (by positivity) (by positivity) 3 (by norm_num) hin
    norm_num at hr
    have : C45 * ((1 / L) * (d:ℝ)^2 / ((ε/8)^4 * n))^(1/3:ℝ) ≤ C45 * (L / C45) :=
      mul_le_mul_of_nonneg_left (by simpa using hr) hC.le
    rw [mul_div_cancel₀ _ hC.ne'] at this
    exact this
  have hE1 := exp_le_of_le_log hdpos hLdef he1
  have hE2 := exp_le_of_le_log hdpos hLdef he2
  -- term 2
  have t2 : C45 / ((d:ℝ)^2 * (ε/8)^2) *
      (Real.exp (C45 * Real.sqrt d / ((ε/8) * (n:ℝ)^(1/4:ℝ))) +
        Real.exp (C45 * ((1 / L) * (d:ℝ)^2 / ((ε/8)^4 * n))^(1/3:ℝ))) ≤ ε^2/512 := by
    calc _ ≤ C45 / ((d:ℝ)^2 * (ε/8)^2) * (2 * d) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 128 * C45 / (d * ε^2) := by field_simp; ring
      _ ≤ ε^2/512 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have hL4 := log4_le_sqrt (x := d) (by linarith)
          have hsd : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hdpos.le
          have key : 65536 * C45 * L^4 ≤ d := by
            calc 65536 * C45 * L^4 ≤ 65536 * C45 * (4096 * Real.sqrt d) :=
                  mul_le_mul_of_nonneg_left hL4 (by positivity)
              _ = (2^28 * C45) * Real.sqrt d := by ring
              _ ≤ Real.sqrt d * Real.sqrt d :=
                  mul_le_mul_of_nonneg_right hdbig (Real.sqrt_nonneg _)
              _ = d := hsd
          have : 128 * C45 * 512 * 1 ≤ 128 * C45 * 512 * (ε^4 * L^4) :=
            mul_le_mul_of_nonneg_left hεL4 (by positivity)
          nlinarith only [this, mul_le_mul_of_nonneg_left key (by positivity : (0:ℝ) ≤ ε^4), hC, hε, hL]
  linarith


lemma deg2_num {C26 Kk : ℝ} (hC : 0 < C26) (hK : 2^250 * (1 + C26) ≤ Kk)
    {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/32) {n : ℕ}
    (hn : Kk * (d:ℝ)^2 / (ε^4 * Real.log d ^ 4) ≤ n) {D : ℕ}
    (hD : (D:ℝ) ≤ C26 * Real.sqrt d / (ε/8)) : 2 * D ≤ n := by
  obtain ⟨hL, hLk⟩ := log_facts hd
  set L := Real.log d
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0:ℝ) < d := by linarith
  have hL4 := hLk 4 (by norm_num)
  have hsd : Real.sqrt d ≤ d := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have key : 2 * (C26 * Real.sqrt d / (ε/8)) ≤ Kk * (d:ℝ)^2 / (ε^4 * L^4) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    rw [show 2 * (C26 * Real.sqrt d) * (ε ^ 4 * L ^ 4) = 2 * C26 * (Real.sqrt d * ε^4 * L^4) by ring]
    have he4 : ε^4 ≤ ε := by
      have h1 : ε^3 ≤ 1 := pow_le_one₀ hε.le (by linarith)
      nlinarith [pow_pos hε 3]
    have h1 : Real.sqrt d * ε^4 * L^4 ≤ d * ε * (2 * 10^10 * d) :=
      mul_le_mul (mul_le_mul hsd he4 (by positivity) hdpos.le) hL4 (by positivity) (by positivity)
    have h2 : 2 * C26 * (Real.sqrt d * ε^4 * L^4) ≤ 2 * C26 * (d * ε * (2 * 10^10 * d)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2 * C26 * (d * ε * (2 * 10^10 * d)) ≤ Kk * (d:ℝ)^2 * (ε / 8) := by
      rw [show 2 * C26 * (d * ε * (2 * 10^10 * d)) = ((8 * 2 * (2 * 10^10)) * C26) * ((d:ℝ)^2 * (ε / 8)) by ring,
        show Kk * (d:ℝ)^2 * (ε / 8) = Kk * ((d:ℝ)^2 * (ε / 8)) by ring]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      refine le_trans ?_ hK
      nlinarith
    linarith
  have : 2 * (D:ℝ) ≤ n := by linarith
  exact_mod_cast this



lemma pv_eq (g : TraceExpression d) (n : ℕ) (ρ σ : Mat d) :
    polynomialVariance g n ρ σ = vr (powerState (labelledState ρ σ) n) (observable g n) := by
  unfold polynomialVariance variance vr tr
  rw [pow_two]

lemma vr_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℂ} (hR : R.PosSemidef)
    (hR1 : R.trace.re = 1) {G : Matrix ι ι ℂ} (hG : G.IsHermitian) : 0 ≤ vr R G := by
  rw [vr_eq hR1]
  exact qf_nonneg hR (hG.sub (herm_smul_real' _ isHermitian_one))

lemma proj_one : projector (1 : Mat d) := ⟨isHermitian_one, by simp⟩

lemma sqrt_bound {V c : ℝ} (hc : 0 ≤ c) (h : V ≤ c^2) : Real.sqrt V ≤ c := by
  calc Real.sqrt V ≤ Real.sqrt (c^2) := Real.sqrt_le_sqrt h
    _ = c := Real.sqrt_sq hc

lemma max_aux {ε L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/32) : max 1 (ε^2 * L^2) ≤ 1 + L^2 := by
  apply max_le (by nlinarith [sq_nonneg L])
  have : ε^2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg L]

lemma sq_le_one_aux {ε L : ℝ} (h0 : 0 ≤ ε * L) (h : ε * L ≤ 1) : ε^2 * L^2 ≤ 1 := by
  nlinarith

lemma one_le_sq_aux {ε L : ℝ} (h : 1 < ε * L) : 1 ≤ ε^2 * L^2 := by
  nlinarith

lemma fin_aux {V ε : ℝ} (h1 : Real.sqrt V ^ 2 = V) (h2 : Real.sqrt V ^ 2 ≤ (ε/8)^2) : V ≤ ε^2/64 := by
  have : (ε/8)^2 = ε^2/64 := by ring
  linarith

end OTDProp32

set_option maxHeartbeats 4000000 in
open Matrix OptimalTraceDistance.Estimation OTDProp32 in
theorem solution : ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∃ C : ℝ, 0 < C ∧
  ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/32 →
  ∀ ρ σ : Mat d, Density ρ → Density σ → ∀ Q : Mat d, projector Q →
  ∀ n : ℕ, C*rate d ε ≤ (n : ℝ) →
    expressionDegree (f d ε Q) ≤ n ∧
    (opNorm (compress Q (plus ρ σ)) ≤ 1/Real.log d →
      polynomialVariance (f d ε Q) n ρ σ ≤ ε^2/64) := by
  obtain ⟨C44, hC44, h44⟩ := lemma_4_4
  obtain ⟨C45, hC45, h45⟩ := proposition_4_5
  obtain ⟨C26, hC26, h26⟩ := proposition_2_6
  set A := 1 + C44 + C45 + C26 with hA
  have hA1 : 1 ≤ A := by linarith
  have hA4 : A ≤ A^4 := by
    calc A = A^1 := (pow_one A).symm
      _ ≤ A^4 := pow_le_pow_right₀ hA1 (by norm_num)
  set Kk := 2^250 * A^4 with hKk
  have hKpos : 0 < Kk := by positivity
  have hK44 : 2^250 * (1 + C44) ≤ Kk := by
    rw [hKk]; apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  have hK44' : 2^250 * (1 + C44)^2 ≤ Kk := by
    rw [hKk]; apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : (1 + C44)^2 ≤ A^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : A^2 ≤ A^4 := pow_le_pow_right₀ hA1 (by norm_num)
    linarith
  have hK45 : 2^250 * (1 + C45)^4 ≤ Kk := by
    rw [hKk]; apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hK26 : 2^250 * (1 + C26) ≤ Kk := by
    rw [hKk]; apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  refine ⟨⌈(2^28 * C45)^2⌉₊ + 2, by omega, Kk, hKpos, ?_⟩
  intro d hd ε hε hε1 ρ σ hρ hσ Q hQ n hn
  have hd2 : 2 ≤ d := by omega
  obtain ⟨hL, -⟩ := log_facts hd2
  set L := Real.log d with hLdef
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd2
  have hdpos : (0:ℝ) < d := by linarith
  have hdbig : 2^28 * C45 ≤ Real.sqrt d := by
    have h1 : (2^28 * C45)^2 ≤ (d:ℝ) := by
      have := Nat.le_ceil ((2^28 * C45)^2)
      have h2 : ((⌈(2^28 * C45)^2⌉₊ : ℕ) : ℝ) ≤ d := by exact_mod_cast (by omega : ⌈(2^28 * C45)^2⌉₊ ≤ d)
      linarith
    rw [show 2^28 * C45 = Real.sqrt ((2^28 * C45)^2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt h1
  have hrate_gen : Kk * (d:ℝ)^2 / (ε^2 * L^2 * (1 + L^2)) ≤ n := by
    refine le_trans ?_ hn
    unfold rate
    rw [mul_div_assoc']
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact max_aux hε hε1
  obtain ⟨hKc2, hKcn, hKcV⟩ := corr_num hC44 hK44 hd2 hε hε1 hrate_gen
  set Kc := ⌈2^40 * Real.log d / ε⌉₊ with hKc
  have hqc := (lemma_2_3 Kc hKc2).1
  have hdeg_corr : expressionDegree (univariate d Kc) ≤ Kc :=
    (deg_poly_var (q Kc) true).trans hqc
  set fr := (if ε * Real.log d ≤ 1 then
      traceExpr (exprPoly (q ⌈constructionC₀ * d / ε⌉₊) (exprVar d true))
    else multiscale constructionA d (ε/8)) with hfr
  have hfr_deg : expressionDegree fr ≤ n ∧
      (opNorm (compress Q (plus ρ σ)) ≤ 1/Real.log d →
        polynomialVariance (substituteCompression Q fr) n ρ σ ≤ ε^2/256) := by
    by_cases hc : ε * Real.log d ≤ 1
    · rw [hfr, if_pos hc]
      have hrate1 : Kk * (d:ℝ)^2 / (ε^2 * L^2) ≤ n := by
        refine le_trans (le_of_eq ?_) hn
        unfold rate
        have h0 : 0 ≤ ε * L := by positivity
        have : max 1 (ε^2 * L^2) = 1 := max_eq_left (sq_le_one_aux h0 hc)
        rw [this]; ring
      obtain ⟨hKr2, hKrn, hKrV⟩ := case1_num hC44 hK44' hd2 hε hε1 hrate1
      have hKr_eq : ⌈constructionC₀ * d / ε⌉₊ = ⌈2^40 * (d:ℝ) / ε⌉₊ := rfl
      rw [hKr_eq]
      refine ⟨((deg_poly_var _ true).trans (lemma_2_3 _ hKr2).1).trans (by omega), fun hnorm => ?_⟩
      have := (h44 d (by omega) ρ σ hρ hσ Q hQ _ n hKr2 hKrn).2 (1 / Real.log d) (by positivity) hnorm
      exact this.trans hKrV
    · rw [hfr, if_neg hc]
      push Not at hc
      have hrate2 : Kk * (d:ℝ)^2 / (ε^4 * L^4) ≤ n := by
        refine le_trans (le_of_eq ?_) hn
        unfold rate
        have : max 1 (ε^2 * L^2) = ε^2 * L^2 := max_eq_right (one_le_sq_aux hc)
        rw [this]; ring
      have hε8 : 0 < ε/8 := by positivity
      have hdegF := (h26 d hd2 (ε/8) hε8 (by linarith) 0 0 isHermitian_zero isHermitian_zero
        PosSemidef.zero (by simp [tr]) (by simp [lePSD, PosSemidef.zero])
        (by simp [lePSD, PosSemidef.zero])).1
      have h2F : 2 * expressionDegree (F d (ε/8)) ≤ n :=
        deg2_num hC26 hK26 hd2 hε hε1 hrate2 hdegF
      refine ⟨by
        show expressionDegree (F d (ε/8)) ≤ n
        omega, fun hnorm => ?_⟩
      have := h45 d hd2 (ε/8) hε8 (by linarith) ρ σ hρ hσ Q hQ (1 / Real.log d) (by positivity)
        hnorm n h2F
      exact this.trans (case2_num hC45 hK45 hd2 hdbig hε hc hrate2)
  have hw : (f d ε Q).words = (substituteCompression Q fr).words ++ (univariate d Kc).words ++
      exprScale (-1) (substituteCompression Q (univariate d Kc)).words := rfl
  constructor
  · refine deg_le_of _ _ (fun w hw1 => ?_)
    rw [hw] at hw1
    simp only [List.mem_append] at hw1
    rcases hw1 with (h1 | h2) | h3
    · obtain ⟨w', hw2, he⟩ := subst_len Q fr w h1
      rw [he]; exact (len_le_deg fr w' hw2).trans hfr_deg.1
    · exact (len_le_deg _ w h2).trans (hdeg_corr.trans (by omega))
    · simp only [exprScale, List.mem_map] at h3
      obtain ⟨w', hw2, rfl⟩ := h3
      obtain ⟨w2, hw3, he⟩ := subst_len Q (univariate d Kc) w' hw2
      show w'.factors.length ≤ n
      rw [he]; exact (len_le_deg _ w2 hw3).trans (hdeg_corr.trans (by omega))
  · intro hnorm
    set R := powerState (labelledState ρ σ) n
    have hR : R.PosSemidef := powerState_psd (labelled_psd hρ hσ) n
    have hR1 : R.trace.re = 1 := by
      rw [trace_powerState, trace_labelled hρ hσ, one_pow, Complex.one_re]
    obtain ⟨c, hc⟩ := obs_decomp (f d ε Q) (substituteCompression Q fr) (univariate d Kc)
      (substituteCompression Q (univariate d Kc)) n hw
    have hVr := hfr_deg.2 hnorm
    have hV2 : polynomialVariance (univariate d Kc) n ρ σ ≤ ε^2/1024 := by
      have := (h44 d (by omega) ρ σ hρ hσ 1 proj_one Kc n hKc2 hKcn).1
      rw [subst_one] at this
      exact this.trans hKcV
    have hV3 : polynomialVariance (substituteCompression Q (univariate d Kc)) n ρ σ ≤ ε^2/1024 :=
      (h44 d (by omega) ρ σ hρ hσ Q hQ Kc n hKc2 hKcn).1.trans hKcV
    rw [pv_eq] at hVr hV2 hV3 ⊢
    rw [hc]
    have htri := vr_triangle hR hR1 (obs_herm (substituteCompression Q fr) n)
      (obs_herm (univariate d Kc) n) (obs_herm (substituteCompression Q (univariate d Kc)) n) c
    have s1 := sqrt_bound (by positivity : (0:ℝ) ≤ ε/16)
      (hVr.trans_eq (by ring) : vr R (observable (substituteCompression Q fr) n) ≤ (ε/16)^2)
    have s2 := sqrt_bound (by positivity : (0:ℝ) ≤ ε/32)
      (hV2.trans_eq (by ring) : vr R (observable (univariate d Kc) n) ≤ (ε/32)^2)
    have s3 := sqrt_bound (by positivity : (0:ℝ) ≤ ε/32)
      (hV3.trans_eq (by ring) : vr R (observable (substituteCompression Q (univariate d Kc)) n) ≤ (ε/32)^2)
    set V := vr R (observable (substituteCompression Q fr) n + observable (univariate d Kc) n -
        observable (substituteCompression Q (univariate d Kc)) n + (c:ℂ) • 1)
    have htot : Real.sqrt V ≤ ε/8 := by linarith
    have hnn : 0 ≤ V := vr_nonneg hR hR1 ((((obs_herm _ n).add (obs_herm _ n)).sub (obs_herm _ n)).add
      (herm_smul_real' c isHermitian_one))
    have h1 := Real.sq_sqrt hnn
    have h2 : Real.sqrt V ^ 2 ≤ (ε/8)^2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) htot 2
    exact fin_aux h1 h2
