-- Prove2me | solution 1 for PlotkinShmoysTardos.general_relaxed_decision
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T23:05:39.746765+00:00
-- url     : https://prove2.me/submissions/d2a332d0-445a-43a1-9c13-cd3ef398cdae

import Mathlib
import Definitions.Def_PlotkinShmoysTardos_General
import Definitions.Def_PlotkinShmoysTardos_relaxedOptimality
import Definitions.Def_PlotkinShmoysTardos_improveGeneral

set_option autoImplicit false
set_option linter.all false

namespace PSTProof
open PlotkinShmoysTardos

section Analytic

variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)

/-- normalized residual of row `i` -/
noncomputable def rr (x : Fin n → ℝ) (i : Fin m) : ℝ := (A.mulVec x i - b i) / d i

/-- potential as a plain sum -/
noncomputable def Phi (α : ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, Real.exp (α * rr A b d x i)

lemma rr_le_lam [NeZero m] (x : Fin n → ℝ) (i : Fin m) : rr A b d x i ≤ lam A b d x := by
  unfold lam
  exact Finset.le_sup' (fun i => (A.mulVec x i - b i) / d i) (Finset.mem_univ i)

lemma exists_rr_eq_lam [NeZero m] (x : Fin n → ℝ) : ∃ i, rr A b d x i = lam A b d x := by
  obtain ⟨i, -, h⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin m))
    (fun i => (A.mulVec x i - b i) / d i)
  refine ⟨i, ?_⟩
  unfold lam
  rw [h]
  rfl

lemma abs_rr_le {P : Set (Fin n → ℝ)} {ρ : ℝ} (hd : ∀ i, 0 < d i) (hW : IsWidthBound A b d P ρ)
    {x : Fin n → ℝ} (hx : x ∈ P) (i : Fin m) : |rr A b d x i| ≤ ρ := by
  unfold rr
  rw [abs_div, abs_of_pos (hd i), div_le_iff₀ (hd i)]
  exact hW i x hx

lemma lam_le_rho [NeZero m] {P : Set (Fin n → ℝ)} {ρ : ℝ} (hd : ∀ i, 0 < d i)
    (hW : IsWidthBound A b d P ρ) {x : Fin n → ℝ} (hx : x ∈ P) : lam A b d x ≤ ρ := by
  obtain ⟨i, hi⟩ := exists_rr_eq_lam A b d x
  rw [← hi]
  exact (le_abs_self _).trans (abs_rr_le A b d hd hW hx i)

lemma dual_dot_d (hd : ∀ i, 0 < d i) (α : ℝ) (x : Fin n → ℝ) :
    dual A b d α x ⬝ᵥ d = Phi A b d α x := by
  unfold dual Phi rr
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := (hd i).ne'
  rw [mul_div_assoc]
  field_simp

lemma dual_dot_res (α : ℝ) (x x' : Fin n → ℝ) :
    dual A b d α x ⬝ᵥ (A.mulVec x' - b) =
      ∑ i, Real.exp (α * rr A b d x i) * rr A b d x' i := by
  unfold dual rr
  simp only [dotProduct, Pi.sub_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_div_assoc]
  ring

lemma dual_nonneg (hd : ∀ i, 0 < d i) (α : ℝ) (x : Fin n → ℝ) : 0 ≤ dual A b d α x := by
  intro i
  unfold dual
  exact mul_nonneg (le_of_lt (one_div_pos.mpr (hd i))) (Real.exp_pos _).le

lemma Phi_pos [NeZero m] (α : ℝ) (x : Fin n → ℝ) : 0 < Phi A b d α x := by
  unfold Phi
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

lemma Phi_ge [NeZero m] {α : ℝ} (x : Fin n → ℝ) :
    Real.exp (α * lam A b d x) ≤ Phi A b d α x := by
  obtain ⟨i, hi⟩ := exists_rr_eq_lam A b d x
  rw [← hi]
  unfold Phi
  exact Finset.single_le_sum (f := fun i => Real.exp (α * rr A b d x i))
    (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

lemma Phi_le [NeZero m] {α : ℝ} (hα : 0 ≤ α) (x : Fin n → ℝ) :
    Phi A b d α x ≤ m * Real.exp (α * lam A b d x) := by
  unfold Phi
  calc ∑ i, Real.exp (α * rr A b d x i) ≤ ∑ _i : Fin m, Real.exp (α * lam A b d x) :=
        Finset.sum_le_sum fun i _ =>
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (rr_le_lam A b d x i) hα)
    _ = m * Real.exp (α * lam A b d x) := by simp

/-- `L = log (6 m ρ / λ₀)` is at least `1/2` when `0 < λ₀ ≤ ρ`. -/
lemma logQ_ge [NeZero m] {ρ l0 : ℝ} (h0 : 0 < l0) (h0ρ : l0 ≤ ρ) :
    1 / 2 ≤ Real.log (6 * m * ρ / l0) := by
  have hm : (1 : ℝ) ≤ m := by
    have := NeZero.pos m
    exact_mod_cast this
  have hρ : 0 < ρ := lt_of_lt_of_le h0 h0ρ
  have hQ : 2 ≤ 6 * m * ρ / l0 := by
    rw [le_div_iff₀ h0]
    have := mul_le_mul_of_nonneg_right hm hρ.le
    linarith
  have h2 : Real.log 2 ≤ Real.log (6 * m * ρ / l0) := Real.log_le_log (by norm_num) hQ
  have := Real.log_two_gt_d9
  linarith

lemma alpha_eq {ρ l0 : ℝ} : alphaOf m ρ l0 = 4 / l0 * Real.log (6 * m * ρ / l0) := rfl

lemma alpha_pos [NeZero m] {ρ l0 : ℝ} (h0 : 0 < l0) (h0ρ : l0 ≤ ρ) : 0 < alphaOf m ρ l0 := by
  rw [alpha_eq]
  have hL := logQ_ge (m := m) h0 h0ρ
  exact mul_pos (by positivity) (by linarith)

lemma alpha_mul [NeZero m] {ρ l0 : ℝ} (h0 : 0 < l0) :
    alphaOf m ρ l0 * l0 = 4 * Real.log (6 * m * ρ / l0) := by
  rw [alpha_eq]
  field_simp

/-- (G1): the dual at a point with `λ ≥ λ₀/2` satisfies `λ yᵗd ≤ 4 yᵗ(Ax-b)`. -/
lemma g1 [NeZero m] {P : Set (Fin n → ℝ)} {ρ l0 : ℝ} (hd : ∀ i, 0 < d i)
    (hW : IsWidthBound A b d P ρ) {x : Fin n → ℝ} (hx : x ∈ P) (h0 : 0 < l0) (h0ρ : l0 ≤ ρ)
    (hl : l0 / 2 ≤ lam A b d x) :
    lam A b d x * Phi A b d (alphaOf m ρ l0) x ≤
      4 * ∑ i, Real.exp (alphaOf m ρ l0 * rr A b d x i) * rr A b d x i := by
  set α := alphaOf m ρ l0 with hαdef
  set l := lam A b d x with hldef
  set L := Real.log (6 * m * ρ / l0) with hLdef
  have hρ : 0 < ρ := lt_of_lt_of_le h0 h0ρ
  have hα : 0 < α := alpha_pos h0 h0ρ
  have hL : 1 / 2 ≤ L := logQ_ge h0 h0ρ
  have hαl0 : α * l0 = 4 * L := alpha_mul h0
  have hlρ : l ≤ ρ := lam_le_rho A b d hd hW hx
  have hlpos : 0 < l := by linarith
  have hαl : 2 * L ≤ α * l := by
    have := mul_le_mul_of_nonneg_left hl hα.le; linarith
  set E := Real.exp (α * l / 4) with hE
  have hEpos : 0 < E := Real.exp_pos _
  -- termwise lower bound
  have hterm : ∀ i, -(5 * ρ * E) ≤ (4 * rr A b d x i - l) * Real.exp (α * rr A b d x i) := by
    intro i
    have hri := abs_le.mp (abs_rr_le A b d hd hW hx i)
    have hei := Real.exp_pos (α * rr A b d x i)
    by_cases hc : l / 4 ≤ rr A b d x i
    · have : 0 ≤ (4 * rr A b d x i - l) * Real.exp (α * rr A b d x i) :=
        mul_nonneg (by linarith) hei.le
      have : 0 ≤ 5 * ρ * E := by positivity
      linarith
    · push_neg at hc
      have hle : Real.exp (α * rr A b d x i) ≤ E :=
        Real.exp_le_exp.mpr (by have := mul_le_mul_of_nonneg_left hc.le hα.le; linarith)
      have h1 : 0 ≤ (4 * rr A b d x i - l + 5 * ρ) * Real.exp (α * rr A b d x i) :=
        mul_nonneg (by linarith) hei.le
      have h2 : 0 ≤ 5 * ρ * (E - Real.exp (α * rr A b d x i)) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
  obtain ⟨i0, hi0⟩ := exists_rr_eq_lam A b d x
  -- main inequality: sum of (4 r_i - l) e_i ≥ 0
  have hsum : ∑ i, (-(5 * ρ * E) + if i = i0 then (3 * l * Real.exp (α * l) + 5 * ρ * E) else 0)
      ≤ ∑ i, (4 * rr A b d x i - l) * Real.exp (α * rr A b d x i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h : i = i0
    · subst h
      simp only [if_true, hi0]
      apply le_of_eq
      ring
    · simp only [h, if_false, add_zero]
      exact hterm i
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i0] at hsum
  simp only [Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  -- 3 l e^{α l} ≥ 5 m ρ E
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.pos m
  have hsplit : Real.exp (α * l) = E * Real.exp (3 * α * l / 4) := by
    rw [hE, ← Real.exp_add]; ring_nf
  have hQpos : 0 < 6 * m * ρ / l0 := by positivity
  have hbig : 6 * m * ρ / l0 ≤ Real.exp (3 * α * l / 4) := by
    rw [← Real.exp_log hQpos]
    exact Real.exp_le_exp.mpr (by rw [← hLdef]; linarith)
  have hk : 3 * m * ρ ≤ l * (6 * m * ρ / l0) := by
    rw [mul_div_assoc']
    rw [le_div_iff₀ h0]
    have : 0 ≤ m * ρ := by positivity
    have := mul_le_mul_of_nonneg_left hl this
    linarith
  have hkey : 5 * m * ρ * E ≤ 3 * l * Real.exp (α * l) := by
    rw [hsplit]
    have h1 : l * (6 * m * ρ / l0) ≤ l * Real.exp (3 * α * l / 4) :=
      mul_le_mul_of_nonneg_left hbig hlpos.le
    have h3 : 0 ≤ m * ρ * E := by positivity
    have h5 : 3 * m * ρ ≤ l * Real.exp (3 * α * l / 4) := hk.trans h1
    have := mul_le_mul_of_nonneg_left h5 hEpos.le
    linarith
  have hres : ∑ i, (4 * rr A b d x i - l) * Real.exp (α * rr A b d x i) =
      4 * ∑ i, Real.exp (α * rr A b d x i) * rr A b d x i - l * Phi A b d α x := by
    unfold Phi
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hρE : 0 ≤ ρ * E := by positivity
  linarith

/-- If the (G2) test passed at a point with `λ ≥ λ₀/2`, no exact solution exists. -/
lemma no_exact [NeZero m] {P : Set (Fin n → ℝ)} {ρ l0 : ℝ} {O : (Fin m → ℝ) → (Fin n → ℝ)}
    (hd : ∀ i, 0 < d i) (hW : IsWidthBound A b d P ρ) (hO : IsMinOracle A P O)
    {x : Fin n → ℝ} (hx : x ∈ P) (h0 : 0 < l0) (h0ρ : l0 ≤ ρ) (hl : l0 / 2 ≤ lam A b d x)
    (htest : dual A b d (alphaOf m ρ l0) x ⬝ᵥ (A.mulVec x - b) -
        dual A b d (alphaOf m ρ l0) x ⬝ᵥ (A.mulVec (O (dual A b d (alphaOf m ρ l0) x)) - b) ≤
        lam A b d x / 5 * (dual A b d (alphaOf m ρ l0) x ⬝ᵥ d)) :
    ¬ ∃ z, IsExact A b P z := by
  rintro ⟨z, hzP, hz⟩
  set y := dual A b d (alphaOf m ρ l0) x with hy
  have hy0 : 0 ≤ y := dual_nonneg A b d hd _ x
  obtain ⟨-, hmin⟩ := hO y hy0
  have hmz := hmin z hzP
  have hlin : ∀ w : Fin n → ℝ, y ⬝ᵥ (A.mulVec w - b) = Matrix.vecMul y A ⬝ᵥ w - y ⬝ᵥ b := by
    intro w
    rw [dotProduct_sub, Matrix.dotProduct_mulVec]
  have hz0 : y ⬝ᵥ (A.mulVec z - b) ≤ 0 := by
    simp only [dotProduct, Pi.sub_apply]
    exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hy0 i) (by linarith [hz i])
  have hG1 := g1 A b d hd hW hx h0 h0ρ hl
  rw [← dual_dot_res, ← dual_dot_d A b d hd] at hG1
  rw [hlin, hlin] at htest
  rw [hlin] at hz0
  have hΦ : 0 < y ⬝ᵥ d := by rw [hy, dual_dot_d A b d hd]; exact Phi_pos A b d _ x
  have hlpos : 0 < lam A b d x := by linarith
  have := mul_pos hlpos hΦ
  rw [← hy] at hG1
  rw [hlin] at hG1
  linarith

/-- `e^u ≤ 1 + u + (14/27) u²` for `|u| ≤ 1/12`. -/
lemma exp_le_quad {u : ℝ} (hu : |u| ≤ 1 / 12) : Real.exp u ≤ 1 + u + 14 / 27 * u ^ 2 := by
  have h := Real.exp_bound (x := u) (by linarith) (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat] at h
  norm_num at h
  have h3 : |u| ^ 3 = |u| * u ^ 2 := by rw [pow_succ, sq_abs]; ring
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  have h4 : |u| * u ^ 2 ≤ 1 / 12 * u ^ 2 := mul_le_mul_of_nonneg_right hu hu2
  have h5 := (abs_le.mp h).2
  linarith

/-- residual of a convex combination -/
lemma rr_comb (hd : ∀ i, 0 < d i) (σ : ℝ) (x xt : Fin n → ℝ) (i : Fin m) :
    rr A b d ((1 - σ) • x + σ • xt) i = rr A b d x i + σ * (rr A b d xt i - rr A b d x i) := by
  unfold rr
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have := (hd i).ne'
  field_simp
  ring

lemma sigma_mul_alpha [NeZero m] {ρ l0 : ℝ} (h0 : 0 < l0) (h0ρ : l0 ≤ ρ) :
    alphaOf m ρ l0 * sigmaOf m ρ l0 = l0 / (24 * ρ ^ 2) := by
  have hα := (alpha_pos (m := m) h0 h0ρ).ne'
  unfold sigmaOf
  field_simp

lemma sigma_mem [NeZero m] {ρ l0 : ℝ} (h0 : 0 < l0) (h0ρ : l0 ≤ ρ) :
    0 ≤ sigmaOf m ρ l0 ∧ sigmaOf m ρ l0 ≤ 1 := by
  have hα := alpha_pos (m := m) h0 h0ρ
  have hρ : 0 < ρ := lt_of_lt_of_le h0 h0ρ
  have hσ : sigmaOf m ρ l0 = l0 / (24 * ρ ^ 2) / alphaOf m ρ l0 := by
    rw [← sigma_mul_alpha (m := m) h0 h0ρ]; field_simp
  have hαl0 := alpha_mul (m := m) (ρ := ρ) h0
  have hL := logQ_ge (m := m) h0 h0ρ
  refine ⟨by rw [hσ]; positivity, ?_⟩
  rw [hσ, div_le_one hα, div_le_iff₀ (by positivity)]
  -- l0 ≤ α * 24 ρ²; α l0 = 4L ≥ 2, so α ≥ 2/l0 ≥ 2/ρ
  have : 2 ≤ alphaOf m ρ l0 * l0 := by linarith
  have h2 : 2 * ρ ≤ alphaOf m ρ l0 * ρ * ρ :=
    mul_le_mul_of_nonneg_right (by linarith [mul_le_mul_of_nonneg_left h0ρ hα.le]) hρ.le
  linarith

/-- one moving step decreases the potential by the factor `1 - λ₀²/(2000 ρ²)`. -/
lemma pot_step [NeZero m] {P : Set (Fin n → ℝ)} {ρ l0 : ℝ} {O : (Fin m → ℝ) → (Fin n → ℝ)}
    (hd : ∀ i, 0 < d i) (hW : IsWidthBound A b d P ρ) (hO : IsMinOracle A P O)
    {x : Fin n → ℝ} (hx : x ∈ P) (h0 : 0 < l0) (h0ρ : l0 ≤ ρ) (hl : l0 / 2 ≤ lam A b d x)
    (hfail : ¬ (dual A b d (alphaOf m ρ l0) x ⬝ᵥ (A.mulVec x - b) -
        dual A b d (alphaOf m ρ l0) x ⬝ᵥ (A.mulVec (O (dual A b d (alphaOf m ρ l0) x)) - b) ≤
        lam A b d x / 5 * (dual A b d (alphaOf m ρ l0) x ⬝ᵥ d))) :
    Phi A b d (alphaOf m ρ l0) ((1 - sigmaOf m ρ l0) • x +
        sigmaOf m ρ l0 • O (dual A b d (alphaOf m ρ l0) x)) ≤
      (1 - l0 ^ 2 / (2000 * ρ ^ 2)) * Phi A b d (alphaOf m ρ l0) x := by
  set α := alphaOf m ρ l0 with hαdef
  set σ := sigmaOf m ρ l0 with hσdef
  set y := dual A b d α x with hy
  set xt := O y with hxt
  have hρ : 0 < ρ := lt_of_lt_of_le h0 h0ρ
  have hy0 : 0 ≤ y := dual_nonneg A b d hd _ x
  have hxtP : xt ∈ P := (hO y hy0).1
  set t := l0 / (24 * ρ ^ 2) with ht
  have hασ : α * σ = t := sigma_mul_alpha h0 h0ρ
  have htpos : 0 < t := by positivity
  have ht2 : t * (2 * ρ) ≤ 1 / 12 := by
    rw [ht]; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right h0ρ hρ.le; linarith
  set e : Fin m → ℝ := fun i => Real.exp (α * rr A b d x i) with he
  set δ : Fin m → ℝ := fun i => rr A b d xt i - rr A b d x i with hδ
  have hδb : ∀ i, |δ i| ≤ 2 * ρ := by
    intro i
    have h1 := abs_le.mp (abs_rr_le A b d hd hW hx i)
    have h2 := abs_le.mp (abs_rr_le A b d hd hW hxtP i)
    rw [abs_le]; simp only [hδ]; constructor <;> linarith
  -- termwise bound
  have hterm : ∀ i, Real.exp (α * rr A b d ((1 - σ) • x + σ • xt) i) ≤
      e i + t * (e i * δ i) + 14 / 27 * t ^ 2 * (e i * (4 * ρ ^ 2)) := by
    intro i
    rw [rr_comb A b d hd]
    have hsplit : α * (rr A b d x i + σ * (rr A b d xt i - rr A b d x i)) =
        α * rr A b d x i + t * δ i := by rw [← hασ]; simp only [hδ]; ring
    rw [hsplit, Real.exp_add]
    have hu : |t * δ i| ≤ 1 / 12 := by
      rw [abs_mul, abs_of_pos htpos]
      calc t * |δ i| ≤ t * (2 * ρ) := mul_le_mul_of_nonneg_left (hδb i) htpos.le
        _ ≤ 1 / 12 := ht2
    have hq := exp_le_quad hu
    have hei : 0 < e i := Real.exp_pos _
    have hδ2 : (δ i) ^ 2 ≤ 4 * ρ ^ 2 := by
      obtain ⟨hh1, hh2⟩ := abs_le.mp (hδb i)
      have := mul_nonneg (sub_nonneg.2 hh2) (neg_le_iff_add_nonneg.1 hh1); linarith
    have : Real.exp (α * rr A b d x i) = e i := rfl
    rw [this]
    have h1 : e i * Real.exp (t * δ i) ≤ e i * (1 + t * δ i + 14 / 27 * (t * δ i) ^ 2) :=
      mul_le_mul_of_nonneg_left hq hei.le
    have h2 : e i * (t ^ 2 * (δ i) ^ 2) ≤ e i * (t ^ 2 * (4 * ρ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδ2 (sq_nonneg t)) hei.le
    linarith
  have hsumδ : ∑ i, e i * δ i = y ⬝ᵥ (A.mulVec xt - b) - y ⬝ᵥ (A.mulVec x - b) := by
    rw [hy, dual_dot_res, dual_dot_res, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [he, hδ]; ring
  have hΦ : y ⬝ᵥ d = Phi A b d α x := dual_dot_d A b d hd α x
  have hΦe : Phi A b d α x = ∑ i, e i := rfl
  rw [hΦ] at hfail
  push_neg at hfail
  have hlt : ∑ i, e i * δ i < -(lam A b d x / 5 * Phi A b d α x) := by
    rw [hsumδ]; linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.sum_mul, ← hΦe] at hsum
  have hPhi_pos : 0 < Phi A b d α x := Phi_pos A b d α x
  -- arithmetic: t * l / 5 - (56/27) t² ρ² ≥ l0²/(2000 ρ²)
  have htρ : t * ρ ^ 2 = l0 / 24 := by rw [ht]; field_simp
  have hkap : l0 ^ 2 / (2000 * ρ ^ 2) = t * l0 * (24 / 2000) := by
    rw [ht]; field_simp
  have hfac : l0 ^ 2 / (2000 * ρ ^ 2) ≤ t * lam A b d x / 5 - 14 / 27 * t ^ 2 * (4 * ρ ^ 2) := by
    rw [hkap]
    have : 14 / 27 * t ^ 2 * (4 * ρ ^ 2) = 56 / 27 * t * (l0 / 24) := by rw [← htρ]; ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hl htpos.le
    have := mul_pos htpos h0
    linarith
  have hPhix : Phi A b d α ((1 - σ) • x + σ • xt) =
      ∑ i, Real.exp (α * rr A b d ((1 - σ) • x + σ • xt) i) := rfl
  rw [hPhix]
  linarith [mul_le_mul_of_nonneg_right hfac hPhi_pos.le, mul_lt_mul_of_pos_left hlt htpos]

end Analytic

section Driver

variable {m n : ℕ} [NeZero m] {A : Matrix (Fin m) (Fin n) ℝ} {b d : Fin m → ℝ}
  {P : Set (Fin n → ℝ)} {ρ : ℝ} {O : (Fin m → ℝ) → (Fin n → ℝ)} {ε : ℝ}

/-- invariant of the driver -/
def Inv (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (P : Set (Fin n → ℝ)) (ρ ε : ℝ)
    (s : RunState n) : Prop :=
  s.cs.x ∈ P ∧ s.cs.evals ≤ s.cs.calls + 1 ∧
  (s.cs.tag = Tag.g2 → ¬ ∃ z, IsExact A b P z) ∧
  (s.phase = Phase.inCall → ε < s.lam0 ∧ s.lam0 ≤ ρ ∧ s.cs.tag = Tag.running) ∧
  (∀ x, s.phase = Phase.done (Output.approx x) → IsApprox A b d P ε x) ∧
  (s.phase = Phase.done Output.infeasible → ¬ ∃ z, IsExact A b P z)

lemma step_between (cs : CallState n) (l0 : ℝ) :
    runStep A b d ρ O ε ⟨cs, l0, Phase.between⟩ =
      if lam A b d cs.x ≤ ε then ⟨cs, l0, Phase.done (Output.approx cs.x)⟩
      else if cs.tag = Tag.g2 then ⟨cs, l0, Phase.done Output.infeasible⟩
      else ⟨{ cs with tag := Tag.running }, lam A b d cs.x, Phase.inCall⟩ := rfl

lemma step_done (cs : CallState n) (l0 : ℝ) (o : Output n) :
    runStep A b d ρ O ε ⟨cs, l0, Phase.done o⟩ = ⟨cs, l0, Phase.done o⟩ := rfl

lemma step_halved (x : Fin n → ℝ) (c e : ℕ) (l0 : ℝ) (h1 : lam A b d x < l0 / 2) :
    runStep A b d ρ O ε ⟨⟨x, Tag.running, c, e⟩, l0, Phase.inCall⟩ =
      ⟨⟨x, Tag.halved, c, e⟩, l0, Phase.between⟩ := by
  simp only [runStep, callStep, if_pos h1]
  rfl

lemma step_g2 (x : Fin n → ℝ) (c e : ℕ) (l0 : ℝ) (h1 : ¬ lam A b d x < l0 / 2)
    (h2 : dual A b d (alphaOf m ρ l0) x ⬝ᵥ (A.mulVec x - b) -
        dual A b d (alphaOf m ρ l0) x ⬝ᵥ (A.mulVec (O (dual A b d (alphaOf m ρ l0) x)) - b) ≤
        lam A b d x / 5 * (dual A b d (alphaOf m ρ l0) x ⬝ᵥ d)) :
    runStep A b d ρ O ε ⟨⟨x, Tag.running, c, e⟩, l0, Phase.inCall⟩ =
      ⟨⟨x, Tag.g2, c + 1, e⟩, l0, Phase.between⟩ := by
  simp only [runStep, callStep, if_neg h1, if_pos h2]
  rfl

lemma step_move (x : Fin n → ℝ) (c e : ℕ) (l0 : ℝ) (h1 : ¬ lam A b d x < l0 / 2)
    (h2 : ¬ (dual A b d (alphaOf m ρ l0) x ⬝ᵥ (A.mulVec x - b) -
        dual A b d (alphaOf m ρ l0) x ⬝ᵥ (A.mulVec (O (dual A b d (alphaOf m ρ l0) x)) - b) ≤
        lam A b d x / 5 * (dual A b d (alphaOf m ρ l0) x ⬝ᵥ d))) :
    runStep A b d ρ O ε ⟨⟨x, Tag.running, c, e⟩, l0, Phase.inCall⟩ =
      ⟨⟨(1 - sigmaOf m ρ l0) • x + sigmaOf m ρ l0 • O (dual A b d (alphaOf m ρ l0) x),
        Tag.running, c + 1, e + 1⟩, l0, Phase.inCall⟩ := by
  simp only [runStep, callStep, if_neg h1, if_neg h2]
  rfl

lemma approx_of_lam {x : Fin n → ℝ} (hd : ∀ i, 0 < d i) (hx : x ∈ P) (h : lam A b d x ≤ ε) :
    IsApprox A b d P ε x := by
  refine ⟨hx, fun i => ?_⟩
  have h1 := rr_le_lam A b d x i
  unfold rr at h1
  rw [div_le_iff₀ (hd i)] at h1
  linarith [mul_le_mul_of_nonneg_right h (hd i).le]

lemma inv_step (hε0 : 0 < ε) (hd : ∀ i, 0 < d i) (hconv : Convex ℝ P)
    (hW : IsWidthBound A b d P ρ) (hO : IsMinOracle A P O) (s : RunState n)
    (hI : Inv A b d P ρ ε s) : Inv A b d P ρ ε (runStep A b d ρ O ε s) := by
  obtain ⟨⟨x, tag, c, e⟩, l0, ph⟩ := s
  obtain ⟨hx, he, hg, hc, ha, hinf⟩ := hI
  cases ph with
  | between =>
    rw [step_between]
    split_ifs with h1 h2
    · refine ⟨hx, he, hg, by simp, ?_, by simp⟩
      intro x' hx'
      simp only [Phase.done.injEq, Output.approx.injEq] at hx'
      subst hx'
      exact approx_of_lam hd hx h1
    · exact ⟨hx, he, hg, by simp, by simp, fun _ => hg h2⟩
    · exact ⟨hx, he, by simp, fun _ => ⟨lt_of_not_ge h1, lam_le_rho A b d hd hW hx, rfl⟩,
        by simp, by simp⟩
  | inCall =>
    obtain ⟨hε, hρ', htag⟩ := hc rfl
    obtain rfl : tag = Tag.running := htag
    have h0 : 0 < l0 := lt_trans hε0 hε
    by_cases h1 : lam A b d x < l0 / 2
    · rw [step_halved x c e l0 h1]
      exact ⟨hx, he, by simp, by simp, by simp, by simp⟩
    · by_cases h2 : dual A b d (alphaOf m ρ l0) x ⬝ᵥ (A.mulVec x - b) -
          dual A b d (alphaOf m ρ l0) x ⬝ᵥ (A.mulVec (O (dual A b d (alphaOf m ρ l0) x)) - b) ≤
          lam A b d x / 5 * (dual A b d (alphaOf m ρ l0) x ⬝ᵥ d)
      · rw [step_g2 x c e l0 h1 h2]
        refine ⟨hx, by simp only at he ⊢; omega, fun _ => ?_, by simp, by simp, by simp⟩
        exact no_exact A b d hd hW hO hx h0 hρ' (le_of_not_gt h1) h2
      · rw [step_move x c e l0 h1 h2]
        have hy0 := dual_nonneg A b d hd (alphaOf m ρ l0) x
        have hxt := (hO _ hy0).1
        obtain ⟨hσ0, hσ1⟩ := sigma_mem (m := m) h0 hρ'
        refine ⟨hconv hx hxt (by linarith) hσ0 (by ring), by simp only at he ⊢; omega,
          by simp, fun _ => ⟨hε, hρ', rfl⟩, by simp, by simp⟩
  | done o =>
    rw [step_done]
    exact ⟨hx, he, hg, hc, ha, hinf⟩

lemma inv_iter (hε0 : 0 < ε) (hd : ∀ i, 0 < d i) (hconv : Convex ℝ P)
    (hW : IsWidthBound A b d P ρ) (hO : IsMinOracle A P O) (k : ℕ) (s : RunState n)
    (hI : Inv A b d P ρ ε s) : Inv A b d P ρ ε ((runStep A b d ρ O ε)^[k] s) := by
  induction k with
  | zero => exact hI
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact inv_step hε0 hd hconv hW hO _ ih

/-- the calls inside one IMPROVE-GENERAL call -/
lemma callPhase (hε0 : 0 < ε) (hd : ∀ i, 0 < d i) (hconv : Convex ℝ P)
    (hW : IsWidthBound A b d P ρ) (hO : IsMinOracle A P O) :
    ∀ (N : ℕ) (s : RunState n), Inv A b d P ρ ε s → s.phase = Phase.inCall →
      Phi A b d (alphaOf m ρ s.lam0) s.cs.x * (1 - s.lam0 ^ 2 / (2000 * ρ ^ 2)) ^ N <
        Real.exp (alphaOf m ρ s.lam0 * (s.lam0 / 2)) →
      ∃ j ≤ N + 1, ((runStep A b d ρ O ε)^[j] s).phase = Phase.between ∧
        ((runStep A b d ρ O ε)^[j] s).cs.calls ≤ s.cs.calls + j ∧
        (((runStep A b d ρ O ε)^[j] s).cs.tag = Tag.g2 ∨
          (((runStep A b d ρ O ε)^[j] s).cs.tag = Tag.halved ∧
            lam A b d ((runStep A b d ρ O ε)^[j] s).cs.x < s.lam0 / 2)) := by
  intro N
  induction N with
  | zero =>
    intro s hI hp hpot
    obtain ⟨⟨x, tag, c, e⟩, l0, ph⟩ := s
    obtain rfl : ph = Phase.inCall := hp
    obtain ⟨hx, he, hg, hc, ha, hinf⟩ := hI
    obtain ⟨hε, hρ', htag⟩ := hc rfl
    obtain rfl : tag = Tag.running := htag
    have h0 : 0 < l0 := lt_trans hε0 hε
    by_cases h1 : lam A b d x < l0 / 2
    · refine ⟨1, by omega, ?_⟩
      rw [Function.iterate_one, step_halved x c e l0 h1]
      exact ⟨rfl, by simp, Or.inr ⟨rfl, h1⟩⟩
    · by_cases h2 : dual A b d (alphaOf m ρ l0) x ⬝ᵥ (A.mulVec x - b) -
          dual A b d (alphaOf m ρ l0) x ⬝ᵥ (A.mulVec (O (dual A b d (alphaOf m ρ l0) x)) - b) ≤
          lam A b d x / 5 * (dual A b d (alphaOf m ρ l0) x ⬝ᵥ d)
      · refine ⟨1, by omega, ?_⟩
        rw [Function.iterate_one, step_g2 x c e l0 h1 h2]
        exact ⟨rfl, by simp, Or.inl rfl⟩
      · exfalso
        simp only [pow_zero, mul_one] at hpot
        have hα := (alpha_pos (m := m) h0 hρ').le
        have h3 := Phi_ge A b d (α := alphaOf m ρ l0) x
        have h4 : Real.exp (alphaOf m ρ l0 * (l0 / 2)) ≤ Real.exp (alphaOf m ρ l0 * lam A b d x) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_not_gt h1) hα)
        linarith
  | succ N ih =>
    intro s hI hp hpot
    obtain ⟨⟨x, tag, c, e⟩, l0, ph⟩ := s
    obtain rfl : ph = Phase.inCall := hp
    have hI' := hI
    obtain ⟨hx, he, hg, hc, ha, hinf⟩ := hI
    obtain ⟨hε, hρ', htag⟩ := hc rfl
    obtain rfl : tag = Tag.running := htag
    have h0 : 0 < l0 := lt_trans hε0 hε
    by_cases h1 : lam A b d x < l0 / 2
    · refine ⟨1, by omega, ?_⟩
      rw [Function.iterate_one, step_halved x c e l0 h1]
      exact ⟨rfl, by simp, Or.inr ⟨rfl, h1⟩⟩
    · by_cases h2 : dual A b d (alphaOf m ρ l0) x ⬝ᵥ (A.mulVec x - b) -
          dual A b d (alphaOf m ρ l0) x ⬝ᵥ (A.mulVec (O (dual A b d (alphaOf m ρ l0) x)) - b) ≤
          lam A b d x / 5 * (dual A b d (alphaOf m ρ l0) x ⬝ᵥ d)
      · refine ⟨1, by omega, ?_⟩
        rw [Function.iterate_one, step_g2 x c e l0 h1 h2]
        exact ⟨rfl, by simp, Or.inl rfl⟩
      · have hstep := step_move (ε := ε) x c e l0 h1 h2
        have hI2 := inv_step hε0 hd hconv hW hO _ hI'
        rw [hstep] at hI2
        have hdec := pot_step A b d hd hW hO hx h0 hρ' (le_of_not_gt h1) h2
        have hρ : 0 < ρ := lt_of_lt_of_le h0 hρ'
        have hk0 : 0 ≤ 1 - l0 ^ 2 / (2000 * ρ ^ 2) := by
          rw [sub_nonneg, div_le_one (by positivity)]
          linarith [pow_le_pow_left₀ h0.le hρ' 2, sq_nonneg ρ]
        have hpw := pow_nonneg hk0 N
        obtain ⟨j, hj, hph, hcalls, htg⟩ := ih _ hI2 rfl (by
          simp only
          calc _ ≤ (1 - l0 ^ 2 / (2000 * ρ ^ 2)) * Phi A b d (alphaOf m ρ l0) x *
                (1 - l0 ^ 2 / (2000 * ρ ^ 2)) ^ N := mul_le_mul_of_nonneg_right hdec hpw
            _ = Phi A b d (alphaOf m ρ l0) x * (1 - l0 ^ 2 / (2000 * ρ ^ 2)) ^ (N + 1) := by ring
            _ < _ := hpot)
        refine ⟨j + 1, by omega, ?_⟩
        rw [Function.iterate_succ_apply, hstep]
        refine ⟨hph, ?_, htg⟩
        simp only at hcalls ⊢
        omega

end Driver

section Driver2

variable {m n : ℕ} [NeZero m] {A : Matrix (Fin m) (Fin n) ℝ} {b d : Fin m → ℝ}
  {P : Set (Fin n → ℝ)} {ρ : ℝ} {O : (Fin m → ℝ) → (Fin n → ℝ)} {ε : ℝ}

lemma iter_comp {α : Type} (f : α → α) (a j : ℕ) (s : α) :
    f^[a + j + 1] s = f^[a] (f^[j] (f s)) := by
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one]

lemma finish_step (s : RunState n) (hp : s.phase = Phase.between)
    (h : s.cs.tag = Tag.g2 ∨ lam A b d s.cs.x ≤ ε) :
    (∃ o, (runStep A b d ρ O ε s).phase = Phase.done o) ∧
      (runStep A b d ρ O ε s).cs.calls = s.cs.calls := by
  obtain ⟨cs, l0, ph⟩ := s
  obtain rfl : ph = Phase.between := hp
  rw [step_between]
  split_ifs with h1 h2
  · exact ⟨⟨_, rfl⟩, rfl⟩
  · exact ⟨⟨_, rfl⟩, rfl⟩
  · exfalso
    rcases h with h | h
    · exact h2 h
    · exact h1 h

lemma Nexists (hε0 : 0 < ε) {x : Fin n → ℝ} (hl : ε < lam A b d x) (hlρ : lam A b d x ≤ ρ) :
    ∃ N : ℕ, Phi A b d (alphaOf m ρ (lam A b d x)) x *
        (1 - (lam A b d x) ^ 2 / (2000 * ρ ^ 2)) ^ N <
        Real.exp (alphaOf m ρ (lam A b d x) * (lam A b d x / 2)) ∧
      (N : ℝ) + 1 ≤ (6000 * Real.log (6 * m * ρ / ε) + 2) * ρ ^ 2 / (lam A b d x) ^ 2 := by
  set l := lam A b d x with hldef
  have h0 : 0 < l := lt_trans hε0 hl
  have hρ : 0 < ρ := lt_of_lt_of_le h0 hlρ
  set α := alphaOf m ρ l with hαdef
  have hα : 0 < α := alpha_pos h0 hlρ
  set L := Real.log (6 * m * ρ / l) with hLdef
  have hαl : α * l = 4 * L := alpha_mul h0
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.pos m
  have hm0 : (0 : ℝ) < m := by linarith
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hlogmL : Real.log m ≤ L := by
    apply Real.log_le_log hm0
    rw [le_div_iff₀ h0]
    have := mul_le_mul_of_nonneg_left hlρ hm0.le
    have : 0 ≤ (m : ℝ) * ρ := by positivity
    linarith
  have hLε : L ≤ Real.log (6 * m * ρ / ε) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_left (by positivity) hε0 hl.le
  set κ := l ^ 2 / (2000 * ρ ^ 2) with hκdef
  have hκ : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by
    rw [hκdef, div_le_one (by positivity)]
    linarith [pow_le_pow_left₀ h0.le hlρ 2, sq_nonneg ρ]
  set G := Real.log m + 2 * L with hGdef
  have hL0 : 0 ≤ L := le_trans hlogm hlogmL
  have hG0 : 0 ≤ G := by linarith
  refine ⟨⌊G / κ⌋₊ + 1, ?_, ?_⟩
  · have hN1 : G / κ < ((⌊G / κ⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast; exact Nat.lt_floor_add_one _
    have hκN : G < ((⌊G / κ⌋₊ + 1 : ℕ) : ℝ) * κ := (div_lt_iff₀ hκ).mp hN1
    set N := ⌊G / κ⌋₊ + 1
    have hpow : (1 - κ) ^ N ≤ Real.exp (N * (-κ)) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-κ)]) N
    have hPhi := Phi_le A b d hα.le x
    have hpw0 : 0 ≤ (1 - κ) ^ N := pow_nonneg (by linarith) N
    calc Phi A b d α x * (1 - κ) ^ N ≤ m * Real.exp (α * l) * Real.exp (N * (-κ)) :=
          mul_le_mul hPhi hpow hpw0 (by positivity)
      _ = Real.exp (Real.log m + α * l + N * (-κ)) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log hm0]
      _ < Real.exp (α * (l / 2)) := by
          apply Real.exp_lt_exp.mpr
          linarith
  · have hfl : ((⌊G / κ⌋₊ : ℕ) : ℝ) ≤ G / κ := Nat.floor_le (by positivity)
    push_cast
    set q := ρ ^ 2 / l ^ 2 with hq
    have hq1 : 1 ≤ q := by
      rw [hq, one_le_div (by positivity)]; exact pow_le_pow_left₀ h0.le hlρ 2
    have hGk : G / κ = 2000 * G * q := by rw [hκdef, hq]; field_simp
    have hR : (6000 * Real.log (6 * m * ρ / ε) + 2) * ρ ^ 2 / l ^ 2 =
        (6000 * Real.log (6 * m * ρ / ε) + 2) * q := by rw [hq]; ring
    rw [hR]
    have : G * q ≤ 3 * Real.log (6 * m * ρ / ε) * q :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith

lemma betweenPhase (hε0 : 0 < ε) (hd : ∀ i, 0 < d i) (hconv : Convex ℝ P)
    (hW : IsWidthBound A b d P ρ) (hO : IsMinOracle A P O) :
    ∀ (K : ℕ) (s : RunState n), Inv A b d P ρ ε s → s.phase = Phase.between →
      s.cs.tag ≠ Tag.g2 → ε < lam A b d s.cs.x → lam A b d s.cs.x ≤ ε * 2 ^ K →
      ∃ j, (∃ o, ((runStep A b d ρ O ε)^[j] s).phase = Phase.done o) ∧
        ((((runStep A b d ρ O ε)^[j] s).cs.calls : ℕ) : ℝ) ≤ (s.cs.calls : ℝ) +
          (6000 * Real.log (6 * m * ρ / ε) + 2) * ρ ^ 2 *
            (4 / ε ^ 2 - 4 / (3 * (lam A b d s.cs.x) ^ 2)) := by
  intro K
  induction K with
  | zero =>
    intro s _ _ _ hl hK
    simp only [pow_zero, mul_one] at hK
    linarith
  | succ K ih =>
    intro s hI hp hg hl hK
    obtain ⟨⟨x, tag, c, e⟩, l0, ph⟩ := s
    obtain rfl : ph = Phase.between := hp
    have hx : x ∈ P := hI.1
    simp only at hg hl hK ⊢
    set l := lam A b d x with hldef
    have hlρ : l ≤ ρ := lam_le_rho A b d hd hW hx
    have h0 : 0 < l := lt_trans hε0 hl
    have hρ : 0 < ρ := lt_of_lt_of_le h0 hlρ
    set s1 : RunState n := ⟨⟨x, Tag.running, c, e⟩, l, Phase.inCall⟩ with hs1def
    have hs1 : runStep A b d ρ O ε ⟨⟨x, tag, c, e⟩, l0, Phase.between⟩ = s1 := by
      rw [step_between, if_neg (show ¬ lam A b d x ≤ ε from not_le.mpr hl), if_neg hg]
    have hI1 : Inv A b d P ρ ε s1 := hs1 ▸ inv_step hε0 hd hconv hW hO _ hI
    obtain ⟨N, hNpot, hNb⟩ := Nexists (A := A) (b := b) (d := d) (m := m) hε0 hl hlρ
    obtain ⟨j, hj, hph, hcalls, htg⟩ := callPhase hε0 hd hconv hW hO N s1 hI1 rfl hNpot
    have hI2 := inv_iter hε0 hd hconv hW hO j s1 hI1
    have hc2 : ((((runStep A b d ρ O ε)^[j] s1).cs.calls : ℕ) : ℝ) ≤ (c : ℝ) + ((N : ℝ) + 1) := by
      have h' : ((runStep A b d ρ O ε)^[j] s1).cs.calls ≤ c + (N + 1) := by
        have hs1c : s1.cs.calls = c := rfl
        have := hcalls; omega
      exact_mod_cast h'
    set c2 := 6000 * Real.log (6 * m * ρ / ε) + 2 with hc2def
    have hlog0 : 0 ≤ Real.log (6 * m * ρ / ε) := by
      apply Real.log_nonneg
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.pos m
      rw [le_div_iff₀ hε0]
      have := mul_le_mul_of_nonneg_right hm1 hρ.le; linarith
    have hc20 : 0 ≤ c2 * ρ ^ 2 := by positivity
    have hB1 : c2 * ρ ^ 2 / l ^ 2 ≤ c2 * ρ ^ 2 * (4 / ε ^ 2 - 4 / (3 * l ^ 2)) := by
      have hinv : 1 / l ^ 2 ≤ 1 / ε ^ 2 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hε0.le hl.le 2)
      have : 1 / l ^ 2 ≤ 4 / ε ^ 2 - 4 / (3 * l ^ 2) := by
        have e1 : 4 / ε ^ 2 = 4 * (1 / ε ^ 2) := by ring
        have e2 : 4 / (3 * l ^ 2) = 4 / 3 * (1 / l ^ 2) := by field_simp
        have : 0 ≤ 1 / l ^ 2 := by positivity
        rw [e1, e2]; linarith
      have := mul_le_mul_of_nonneg_left this hc20
      rw [div_eq_mul_one_div (c2 * ρ ^ 2)]
      exact this
    have hNb' : (N : ℝ) + 1 ≤ c2 * ρ ^ 2 / l ^ 2 := by rw [hc2def]; exact hNb
    rcases htg with hg2 | ⟨hh, hl2⟩
    · obtain ⟨⟨o, ho⟩, hcs⟩ := finish_step (A := A) (b := b) (d := d) (ρ := ρ) (O := O) (ε := ε)
        _ hph (Or.inl hg2)
      refine ⟨1 + j + 1, ⟨o, ?_⟩, ?_⟩
      · rw [iter_comp, hs1, Function.iterate_one]; exact ho
      · rw [iter_comp, hs1, Function.iterate_one, hcs]
        linarith
    · by_cases hsmall : lam A b d ((runStep A b d ρ O ε)^[j] s1).cs.x ≤ ε
      · obtain ⟨⟨o, ho⟩, hcs⟩ := finish_step (A := A) (b := b) (d := d) (ρ := ρ) (O := O)
          (ε := ε) _ hph (Or.inr hsmall)
        refine ⟨1 + j + 1, ⟨o, ?_⟩, ?_⟩
        · rw [iter_comp, hs1, Function.iterate_one]; exact ho
        · rw [iter_comp, hs1, Function.iterate_one, hcs]
          linarith
      · have hl2' : ε < lam A b d ((runStep A b d ρ O ε)^[j] s1).cs.x := not_le.mp hsmall
        have hK2 : lam A b d ((runStep A b d ρ O ε)^[j] s1).cs.x ≤ ε * 2 ^ K := by
          rw [pow_succ] at hK
          simp only [hs1def] at hl2
          linarith
        obtain ⟨j', ⟨o, ho⟩, hc'⟩ := ih _ hI2 hph (by rw [hh]; simp) hl2' hK2
        refine ⟨j' + j + 1, ⟨o, ?_⟩, ?_⟩
        · rw [iter_comp, hs1]; exact ho
        · rw [iter_comp, hs1]
          set l2 := lam A b d ((runStep A b d ρ O ε)^[j] s1).cs.x
          have hl2s : l2 < l / 2 := by simpa [hs1def] using hl2
          have hl2pos : 0 < l2 := lt_trans hε0 hl2'
          have hq : 4 / l ^ 2 ≤ 1 / l2 ^ 2 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have := mul_pos (sub_pos.2 hl2s) (by linarith : 0 < l / 2 + l2); linarith
          have hbud : c2 * ρ ^ 2 / l ^ 2 + c2 * ρ ^ 2 * (4 / ε ^ 2 - 4 / (3 * l2 ^ 2)) ≤
              c2 * ρ ^ 2 * (4 / ε ^ 2 - 4 / (3 * l ^ 2)) := by
            have e1 : 4 / (3 * l2 ^ 2) = 4 / 3 * (1 / l2 ^ 2) := by field_simp
            have e2 : 4 / (3 * l ^ 2) = 1 / 3 * (4 / l ^ 2) := by field_simp
            have e3 : c2 * ρ ^ 2 / l ^ 2 = c2 * ρ ^ 2 * (1 / 4 * (4 / l ^ 2)) := by field_simp
            rw [e1, e2, e3]
            have : 0 ≤ c2 * ρ ^ 2 * (4 / 3 * (1 / l2 ^ 2) - 4 / 3 * (4 / l ^ 2)) :=
              mul_nonneg hc20 (by linarith)
            have : 0 ≤ c2 * ρ ^ 2 * (4 / l ^ 2) := mul_nonneg hc20 (by positivity)
            linarith
          linarith

theorem main :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m n : ℕ) [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
        (P : Set (Fin n → ℝ)) (ρ : ℝ) (O : (Fin m → ℝ) → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (ε : ℝ),
        (∀ i, 0 < d i) → Convex ℝ P → IsWidthBound A b d P ρ → IsMinOracle A P O → x₀ ∈ P →
        0 < ε → ε < 1 →
        ∃ k : ℕ,
          (∃ o, (run A b d ρ O ε x₀ k).phase = Phase.done o) ∧
          (∀ x, (run A b d ρ O ε x₀ k).phase = Phase.done (Output.approx x) →
            IsApprox A b d P ε x) ∧
          ((run A b d ρ O ε x₀ k).phase = Phase.done Output.infeasible →
            ¬ ∃ z, IsExact A b P z) ∧
          ((run A b d ρ O ε x₀ k).cs.calls : ℝ) ≤
            C * ρ ^ 2 / ε ^ 2 * (1 + Real.log (max 1 (m * ρ / ε))) ∧
          (run A b d ρ O ε x₀ k).cs.evals ≤ (run A b d ρ O ε x₀ k).cs.calls + 1 := by
  refine ⟨120008, by norm_num, ?_⟩
  intro m n _ A b d P ρ O x₀ ε hd hconv hW hO hx₀ hε0 hε1
  set s0 : RunState n := ⟨⟨x₀, Tag.running, 0, 1⟩, 0, Phase.between⟩ with hs0
  have hrun : ∀ k, run A b d ρ O ε x₀ k = (runStep A b d ρ O ε)^[k] s0 := fun k => rfl
  have hI0 : Inv A b d P ρ ε s0 :=
    ⟨hx₀, le_refl _, by simp [s0], by simp [s0], by simp [s0], by simp [s0]⟩
  set ℓ := Real.log (max 1 ((m : ℝ) * ρ / ε)) with hℓdef
  have hℓ : 0 ≤ ℓ := Real.log_nonneg (le_max_left _ _)
  have hbound0 : 0 ≤ 120008 * ρ ^ 2 / ε ^ 2 * (1 + ℓ) := by positivity
  have key : ∃ k, (∃ o, ((runStep A b d ρ O ε)^[k] s0).phase = Phase.done o) ∧
      ((((runStep A b d ρ O ε)^[k] s0).cs.calls : ℕ) : ℝ) ≤
        120008 * ρ ^ 2 / ε ^ 2 * (1 + ℓ) := by
    by_cases hsm : lam A b d x₀ ≤ ε
    · obtain ⟨ho, hc⟩ := finish_step (A := A) (b := b) (d := d) (ρ := ρ) (O := O) (ε := ε)
        s0 rfl (Or.inr hsm)
      refine ⟨1, by rw [Function.iterate_one]; exact ho, ?_⟩
      rw [Function.iterate_one, hc]
      simpa [s0] using hbound0
    · have hl : ε < lam A b d x₀ := not_le.mp hsm
      obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (lam A b d x₀ / ε) (by norm_num : (1 : ℝ) < 2)
      have hK' : lam A b d x₀ ≤ ε * 2 ^ K := by
        rw [div_lt_iff₀ hε0] at hK; linarith
      obtain ⟨j, hdone, hc⟩ := betweenPhase hε0 hd hconv hW hO K s0 hI0 rfl (by simp [s0]) hl hK'
      refine ⟨j, hdone, hc.trans ?_⟩
      have hlρ : lam A b d x₀ ≤ ρ := lam_le_rho A b d hd hW hx₀
      have hρ : 0 < ρ := by linarith
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.pos m
      have hlog0 : 0 ≤ Real.log (6 * m * ρ / ε) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ hε0]
        have := mul_le_mul_of_nonneg_right hm1 hρ.le; linarith
      have hsplit : Real.log (6 * m * ρ / ε) = Real.log 6 + Real.log (m * ρ / ε) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
      have h6 : Real.log 6 ≤ 5 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6); linarith
      have hmx : Real.log (m * ρ / ε) ≤ ℓ :=
        Real.log_le_log (by positivity) (le_max_right _ _)
      have hc2 : 6000 * Real.log (6 * m * ρ / ε) + 2 ≤ 30002 * (1 + ℓ) := by linarith
      have hq0 : 0 ≤ ρ ^ 2 / ε ^ 2 := by positivity
      have hsub : 4 / ε ^ 2 - 4 / (3 * (lam A b d x₀) ^ 2) ≤ 4 / ε ^ 2 := by
        have : 0 ≤ 4 / (3 * (lam A b d x₀) ^ 2) := by positivity
        linarith
      have hcs0 : ((s0.cs.calls : ℕ) : ℝ) = 0 := by simp [s0]
      rw [hcs0, zero_add]
      have hc20 : 0 ≤ (6000 * Real.log (6 * m * ρ / ε) + 2) * ρ ^ 2 := by positivity
      calc (6000 * Real.log (6 * m * ρ / ε) + 2) * ρ ^ 2 *
            (4 / ε ^ 2 - 4 / (3 * (lam A b d x₀) ^ 2))
          ≤ (6000 * Real.log (6 * m * ρ / ε) + 2) * ρ ^ 2 * (4 / ε ^ 2) :=
            mul_le_mul_of_nonneg_left hsub hc20
        _ = 4 * (6000 * Real.log (6 * m * ρ / ε) + 2) * (ρ ^ 2 / ε ^ 2) := by ring
        _ ≤ 4 * (30002 * (1 + ℓ)) * (ρ ^ 2 / ε ^ 2) := by gcongr
        _ = 120008 * ρ ^ 2 / ε ^ 2 * (1 + ℓ) := by ring
  obtain ⟨k, hdone, hcalls⟩ := key
  have hI := inv_iter hε0 hd hconv hW hO k s0 hI0
  refine ⟨k, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun]; exact hdone
  · rw [hrun]; exact hI.2.2.2.2.1
  · rw [hrun]; exact hI.2.2.2.2.2
  · rw [hrun]; exact hcalls
  · rw [hrun]; exact hI.2.1

end Driver2

end PSTProof

open PlotkinShmoysTardos in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m n : ℕ) [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
        (P : Set (Fin n → ℝ)) (ρ : ℝ) (O : (Fin m → ℝ) → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (ε : ℝ),
        (∀ i, 0 < d i) → Convex ℝ P → IsWidthBound A b d P ρ → IsMinOracle A P O → x₀ ∈ P →
        0 < ε → ε < 1 →
        ∃ k : ℕ,
          (∃ o, (run A b d ρ O ε x₀ k).phase = Phase.done o) ∧
          (∀ x, (run A b d ρ O ε x₀ k).phase = Phase.done (Output.approx x) →
            IsApprox A b d P ε x) ∧
          ((run A b d ρ O ε x₀ k).phase = Phase.done Output.infeasible →
            ¬ ∃ z, IsExact A b P z) ∧
          ((run A b d ρ O ε x₀ k).cs.calls : ℝ) ≤
            C * ρ ^ 2 / ε ^ 2 * (1 + Real.log (max 1 (m * ρ / ε))) ∧
          (run A b d ρ O ε x₀ k).cs.evals ≤ (run A b d ρ O ε x₀ k).cs.calls + 1 := by
  exact PSTProof.main
