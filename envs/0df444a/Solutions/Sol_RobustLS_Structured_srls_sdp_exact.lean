-- Prove2me | solution 1 for RobustLS.Structured.srls_sdp_exact
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:35:59.28836+00:00
-- url     : https://prove2.me/submissions/e86d744d-b32b-4f72-8d73-00198ca851e5

import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

theorem aux_srls_resid {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (δ : Fin p → ℝ) :
    structMatrix A0 A δ *ᵥ x - structVector b0 b δ = (A0 *ᵥ x - b0) + Mx A b x *ᵥ δ := by
  ext k
  simp only [structMatrix, structVector, Mx, Pi.add_apply, Pi.sub_apply, add_mulVec]
  simp [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply]
  have h1 : ∑ j, (∑ i, δ i * A i k j) * x j = ∑ i, (∑ j, A i k j * x j) * δ i := by
    simp only [Finset.sum_mul]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  have h2 : ∑ i, (∑ j, A i k j * x j - b i k) * δ i =
      ∑ i, (∑ j, A i k j * x j) * δ i - ∑ i, δ i * b i k := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
  rw [h1, h2]; ring

theorem aux_srls_eucNorm_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) : eucNorm v ^ 2 = v ⬝ᵥ v := by
  unfold eucNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [dotProduct, sq]

theorem aux_srls_eucNorm_le_one {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    eucNorm v ≤ 1 ↔ v ⬝ᵥ v ≤ 1 := by
  have h0 : 0 ≤ eucNorm v := Real.sqrt_nonneg _
  rw [← aux_srls_eucNorm_sq]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

theorem aux_srls_eucNorm_eq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    eucNorm v = Real.sqrt (v ⬝ᵥ v) := by
  unfold eucNorm; simp [dotProduct, sq]

theorem aux_srls_dot_self_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem aux_srls_poly {a b c : ℝ} (h : ∀ ε : ℝ, 0 < ε → a ≤ ε * (b + c * ε)) : a ≤ 0 := by
  by_contra ha
  replace ha : 0 < a := not_le.1 ha
  set K := |b| + |c| + 1 with hK
  have hKpos : 0 < K := by positivity
  set ε := min 1 (a / (2 * K)) with hε
  have hε0 : 0 < ε := lt_min one_pos (div_pos ha (by positivity))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ a / (2 * K) := min_le_right _ _
  have h1 := h ε hε0
  have hb : b ≤ |b| := le_abs_self b
  have hc : c * ε ≤ |c| := by
    calc c * ε ≤ |c| * ε := mul_le_mul_of_nonneg_right (le_abs_self c) hε0.le
      _ ≤ |c| := by nlinarith [abs_nonneg c]
  have h2 : ε * (b + c * ε) ≤ ε * K := by
    apply mul_le_mul_of_nonneg_left _ hε0.le; linarith
  have h3 : ε * K ≤ a / 2 := by
    calc ε * K ≤ a / (2 * K) * K := mul_le_mul_of_nonneg_right hε2 hKpos.le
      _ = a / 2 := by field_simp
  linarith

theorem aux_srls_kkt {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ) (r : Fin n → ℝ) :
    ∃ (d : Fin p → ℝ) (τ : ℝ), d ⬝ᵥ d ≤ 1 ∧ τ * (d ⬝ᵥ d) = τ ∧
      (∀ δ : Fin p → ℝ, δ ⬝ᵥ δ ≤ 1 →
        (r + M *ᵥ δ) ⬝ᵥ (r + M *ᵥ δ) ≤ (r + M *ᵥ d) ⬝ᵥ (r + M *ᵥ d)) ∧
      (∀ e, (r + M *ᵥ d) ⬝ᵥ (M *ᵥ e) = τ * (d ⬝ᵥ e)) ∧
      (∀ e, (M *ᵥ e) ⬝ᵥ (M *ᵥ e) ≤ τ * (e ⬝ᵥ e)) := by
  classical
  set K : Set (Fin p → ℝ) := {δ | δ ⬝ᵥ δ ≤ 1} with hK
  have hcont : Continuous fun δ : Fin p → ℝ => δ ⬝ᵥ δ := by fun_prop
  have hKc : IsCompact K := by
    apply (isCompact_closedBall (0 : Fin p → ℝ) 1).of_isClosed_subset
    · exact isClosed_le hcont continuous_const
    · intro δ hδ
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have hi : δ i ^ 2 ≤ δ ⬝ᵥ δ := by
        simp only [dotProduct]
        have := Finset.single_le_sum (f := fun j => δ j * δ j)
          (fun j _ => mul_self_nonneg (δ j)) (Finset.mem_univ i)
        simpa [sq] using this
      have h1 : δ i ^ 2 ≤ 1 := le_trans hi hδ
      rw [Real.norm_eq_abs]
      exact (sq_le_one_iff_abs_le_one _).1 h1
  have hfc : Continuous fun δ : Fin p → ℝ => (r + M *ᵥ δ) ⬝ᵥ (r + M *ᵥ δ) := by fun_prop
  obtain ⟨d, hdK, hdmax⟩ := hKc.exists_isMaxOn ⟨0, by simp [hK]⟩ hfc.continuousOn
  have hd : d ⬝ᵥ d ≤ 1 := hdK
  have hmax : ∀ δ : Fin p → ℝ, δ ⬝ᵥ δ ≤ 1 →
      (r + M *ᵥ δ) ⬝ᵥ (r + M *ᵥ δ) ≤ (r + M *ᵥ d) ⬝ᵥ (r + M *ᵥ d) :=
    fun δ hδ => hdmax hδ
  set v := r + M *ᵥ d with hv
  have hexp : ∀ e, (r + M *ᵥ (d + e)) ⬝ᵥ (r + M *ᵥ (d + e)) =
      v ⬝ᵥ v + 2 * (v ⬝ᵥ (M *ᵥ e)) + (M *ᵥ e) ⬝ᵥ (M *ᵥ e) := by
    intro e
    rw [mulVec_add, ← add_assoc, ← hv]
    simp only [add_dotProduct, dotProduct_add, dotProduct_comm (M *ᵥ e) v]
    ring
  have hnorm : ∀ e, (d + e) ⬝ᵥ (d + e) = d ⬝ᵥ d + 2 * (d ⬝ᵥ e) + e ⬝ᵥ e := by
    intro e; simp only [add_dotProduct, dotProduct_add, dotProduct_comm e d]; ring
  have hmax' : ∀ e, d ⬝ᵥ d + 2 * (d ⬝ᵥ e) + e ⬝ᵥ e ≤ 1 →
      2 * (v ⬝ᵥ (M *ᵥ e)) + (M *ᵥ e) ⬝ᵥ (M *ᵥ e) ≤ 0 := by
    intro e he
    have := hmax (d + e) (by rw [hnorm]; exact he)
    rw [hexp] at this; linarith
  have hmax'' : ∀ (s : ℝ) e, d ⬝ᵥ d + 2 * s * (d ⬝ᵥ e) + s * s * (e ⬝ᵥ e) ≤ 1 →
      2 * s * (v ⬝ᵥ (M *ᵥ e)) + s * s * ((M *ᵥ e) ⬝ᵥ (M *ᵥ e)) ≤ 0 := by
    intro s e he
    have := hmax' (s • e) (by
      simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]; linarith)
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at this
    linarith
  have hNnn : ∀ e, 0 ≤ (M *ᵥ e) ⬝ᵥ (M *ᵥ e) := fun e => aux_srls_dot_self_nonneg _
  rcases hd.lt_or_eq with hlt | heq
  · have key : ∀ e, ∃ s : ℝ, 0 < s ∧ d ⬝ᵥ d + 2 * s * (d ⬝ᵥ e) + s * s * (e ⬝ᵥ e) ≤ 1 := by
      intro e
      have hD0 : 0 ≤ d ⬝ᵥ d := aux_srls_dot_self_nonneg d
      have hq : 0 ≤ e ⬝ᵥ e := aux_srls_dot_self_nonneg e
      have hden : 0 < 2 * |d ⬝ᵥ e| + e ⬝ᵥ e + 1 := by positivity
      refine ⟨(1 - d ⬝ᵥ d) / (2 * |d ⬝ᵥ e| + e ⬝ᵥ e + 1), div_pos (by linarith) hden, ?_⟩
      set s := (1 - d ⬝ᵥ d) / (2 * |d ⬝ᵥ e| + e ⬝ᵥ e + 1) with hs
      have hs0 : 0 < s := div_pos (by linarith) hden
      have hs1 : s * (2 * |d ⬝ᵥ e| + e ⬝ᵥ e + 1) = 1 - d ⬝ᵥ d := by
        rw [hs]; field_simp
      have hsle : s ≤ 1 := by nlinarith [abs_nonneg (d ⬝ᵥ e)]
      have ha1 : s * (d ⬝ᵥ e) ≤ s * |d ⬝ᵥ e| := mul_le_mul_of_nonneg_left (le_abs_self _) hs0.le
      have ha2 : s * (s * (e ⬝ᵥ e)) ≤ 1 * (s * (e ⬝ᵥ e)) :=
        mul_le_mul_of_nonneg_right hsle (mul_nonneg hs0.le hq)
      nlinarith
    have hL0 : ∀ e, v ⬝ᵥ (M *ᵥ e) ≤ 0 := by
      intro e
      obtain ⟨s, hs, hse⟩ := key e
      have h1 := hmax'' s e hse
      have hN := hNnn e
      have h2 : 0 ≤ s * s * ((M *ᵥ e) ⬝ᵥ (M *ᵥ e)) := mul_nonneg (mul_nonneg hs.le hs.le) hN
      by_contra hc
      have h3 : 0 < s * (v ⬝ᵥ (M *ᵥ e)) := mul_pos hs (not_le.1 hc)
      linarith
    have hL : ∀ e, v ⬝ᵥ (M *ᵥ e) = 0 := by
      intro e
      have h1 := hL0 e
      have h2 := hL0 (-e)
      rw [mulVec_neg, dotProduct_neg] at h2
      linarith
    refine ⟨d, 0, hd, by ring, hmax, ?_, ?_⟩
    · intro e; rw [hL e]; ring
    · intro e
      obtain ⟨s, hs, hse⟩ := key e
      have h1 := hmax'' s e hse
      rw [hL e] at h1
      have h2 : s * s * ((M *ᵥ e) ⬝ᵥ (M *ᵥ e)) ≤ 0 := by linarith
      have hss : 0 < s * s := mul_pos hs hs
      rw [zero_mul]
      by_contra hc
      have := mul_pos hss (not_le.1 hc)
      linarith
  · set τ := v ⬝ᵥ (M *ᵥ d) with hτ
    have hfo : ∀ e, d ⬝ᵥ e < 0 → v ⬝ᵥ (M *ᵥ e) ≤ 0 := by
      intro e he
      have hq : 0 ≤ e ⬝ᵥ e := aux_srls_dot_self_nonneg e
      set s := -2 * (d ⬝ᵥ e) / (e ⬝ᵥ e + 1) with hs
      have hs0 : 0 < s := div_pos (by linarith) (by linarith)
      have hsq : s * (e ⬝ᵥ e + 1) = -2 * (d ⬝ᵥ e) := by rw [hs]; field_simp
      have hsq' : s * s * (e ⬝ᵥ e) = s * (-2 * (d ⬝ᵥ e) - s) := by
        rw [mul_assoc, (by linarith : s * (e ⬝ᵥ e) = -2 * (d ⬝ᵥ e) - s)]
      have hse : d ⬝ᵥ d + 2 * s * (d ⬝ᵥ e) + s * s * (e ⬝ᵥ e) ≤ 1 := by
        rw [heq, hsq']; nlinarith
      have h1 := hmax'' s e hse
      have h2 : 0 ≤ s * s * ((M *ᵥ e) ⬝ᵥ (M *ᵥ e)) := mul_nonneg (mul_nonneg hs0.le hs0.le) (hNnn e)
      by_contra hc
      have h3 : 0 < s * (v ⬝ᵥ (M *ᵥ e)) := mul_pos hs0 (not_le.1 hc)
      linarith
    have hτ0 : 0 ≤ τ := by
      have := hfo (-d) (by rw [dotProduct_neg, heq]; norm_num)
      rw [mulVec_neg, dotProduct_neg] at this; linarith
    have hLrep : ∀ e, v ⬝ᵥ (M *ᵥ e) = τ * (d ⬝ᵥ e) := by
      intro e
      set e' := e - (d ⬝ᵥ e) • d with he'
      have hde' : d ⬝ᵥ e' = 0 := by
        rw [he', dotProduct_sub, dotProduct_smul, heq, smul_eq_mul]; ring
      have hLe' : v ⬝ᵥ (M *ᵥ e') = 0 := by
        have hc : ∀ c : ℝ, 0 < c → |v ⬝ᵥ (M *ᵥ e')| ≤ c * τ := by
          intro c hc
          have h1 := hfo (e' - c • d) (by
            rw [dotProduct_sub, dotProduct_smul, hde', heq, smul_eq_mul]; linarith)
          have h2 := hfo (-e' - c • d) (by
            rw [dotProduct_sub, dotProduct_neg, dotProduct_smul, hde', heq, smul_eq_mul]; linarith)
          rw [mulVec_sub, dotProduct_sub, mulVec_smul, dotProduct_smul, smul_eq_mul] at h1 h2
          rw [mulVec_neg, dotProduct_neg] at h2
          rw [abs_le]; constructor <;> linarith
        by_contra hne
        have hpos : 0 < |v ⬝ᵥ (M *ᵥ e')| := abs_pos.2 hne
        have h1 := hc (|v ⬝ᵥ (M *ᵥ e')| / (τ + 1)) (div_pos hpos (by linarith))
        have h2 : |v ⬝ᵥ (M *ᵥ e')| / (τ + 1) * τ < |v ⬝ᵥ (M *ᵥ e')| := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
        linarith
      have hsplit : e = e' + (d ⬝ᵥ e) • d := by rw [he']; abel
      calc v ⬝ᵥ (M *ᵥ e) = v ⬝ᵥ (M *ᵥ (e' + (d ⬝ᵥ e) • d)) := by rw [← hsplit]
        _ = τ * (d ⬝ᵥ e) := by
          rw [mulVec_add, dotProduct_add, hLe', mulVec_smul, dotProduct_smul, smul_eq_mul, ← hτ]
          ring
    have hso1 : ∀ w, d ⬝ᵥ w ≠ 0 → (M *ᵥ w) ⬝ᵥ (M *ᵥ w) ≤ τ * (w ⬝ᵥ w) := by
      intro w hw
      have hq : 0 < w ⬝ᵥ w := by
        rcases (aux_srls_dot_self_nonneg w).lt_or_eq with h | h
        · exact h
        · exfalso; apply hw
          have : w = 0 := dotProduct_self_eq_zero.1 h.symm
          simp [this]
      set c := -2 * (d ⬝ᵥ w) / (w ⬝ᵥ w) with hc
      have hcq : c * (w ⬝ᵥ w) = -2 * (d ⬝ᵥ w) := by rw [hc]; field_simp
      have hc0 : c ≠ 0 := by
        intro h0; rw [h0] at hcq; apply hw; linarith
      have hcc' : c * c * (w ⬝ᵥ w) = c * (-2 * (d ⬝ᵥ w)) := by rw [mul_assoc, hcq]
      have hse : d ⬝ᵥ d + 2 * c * (d ⬝ᵥ w) + c * c * (w ⬝ᵥ w) ≤ 1 := by
        rw [heq, hcc']; nlinarith
      have h := hmax'' c w hse
      rw [hLrep w] at h
      have h3 : 2 * c * (τ * (d ⬝ᵥ w)) = -(τ * (c * c * (w ⬝ᵥ w))) := by
        rw [hcc']; ring
      have h4 : c * c * ((M *ᵥ w) ⬝ᵥ (M *ᵥ w) - τ * (w ⬝ᵥ w)) ≤ 0 := by nlinarith
      have hcc : 0 < c * c := mul_self_pos.2 hc0
      by_contra hcon
      have := mul_pos hcc (sub_pos.2 (not_le.1 hcon))
      linarith
    have hso : ∀ w, (M *ᵥ w) ⬝ᵥ (M *ᵥ w) ≤ τ * (w ⬝ᵥ w) := by
      intro w
      by_cases hw : d ⬝ᵥ w = 0
      · have key : ∀ ε : ℝ, 0 < ε → (M *ᵥ w) ⬝ᵥ (M *ᵥ w) - τ * (w ⬝ᵥ w) ≤
            ε * (-2 * ((M *ᵥ w) ⬝ᵥ (M *ᵥ d)) + (τ - (M *ᵥ d) ⬝ᵥ (M *ᵥ d)) * ε) := by
          intro ε hε
          have h := hso1 (w + ε • d) (by
            rw [dotProduct_add, hw, dotProduct_smul, heq, smul_eq_mul]; simp; exact hε.ne')
          rw [mulVec_add, mulVec_smul] at h
          simp only [add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct,
            smul_eq_mul] at h
          rw [dotProduct_comm w d, hw, heq, dotProduct_comm (M *ᵥ d) (M *ᵥ w)] at h
          nlinarith
        have := aux_srls_poly key
        linarith
      · exact hso1 w hw
    exact ⟨d, τ, hd, by rw [heq, mul_one], hmax, hLrep, hso⟩

theorem aux_srls_herm {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (lam τ : ℝ) (x : Fin m → ℝ) : (sdp32Matrix A0 A b0 b lam τ x).IsHermitian := by
  ext i j
  rcases i with ((_ | i) | i) <;> rcases j with ((_ | j) | j) <;>
    simp [sdp32Matrix, Matrix.one_apply, eq_comm]

theorem aux_srls_quad {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (lam τ : ℝ) (x : Fin m → ℝ) (t : ℝ) (δ : Fin p → ℝ) (w : Fin n → ℝ) :
    star (Sum.elim (Sum.elim (fun _ : Unit => t) δ) w) ⬝ᵥ
      (sdp32Matrix A0 A b0 b lam τ x *ᵥ Sum.elim (Sum.elim (fun _ : Unit => t) δ) w) =
    (lam - τ) * t ^ 2 + τ * (δ ⬝ᵥ δ) +
      2 * (w ⬝ᵥ (t • (A0 *ᵥ x - b0) + Mx A b x *ᵥ δ)) + w ⬝ᵥ w := by
  rw [star_trivial]
  simp [sdp32Matrix, dotProduct, mulVec, Fintype.sum_sum_type, Matrix.one_apply,
    Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  have e1 : ∑ a, ∑ i, δ a * (Mx A b x i a * w i) = ∑ a, ∑ i, w a * (Mx A b x a i * δ i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  have e2 : ∑ i, t * ((∑ j, A0 i j * x j - b0 i) * w i) =
      ∑ i, w i * ((∑ j, A0 i j * x j - b0 i) * t) := by
    apply Finset.sum_congr rfl; intro i _; ring
  have e3 : ∑ i, δ i * (τ * δ i) = ∑ i, τ * (δ i * δ i) := by
    apply Finset.sum_congr rfl; intro i _; ring
  have e4 : ∑ i, 2 * (w i * (t * (∑ j, A0 i j * x j - b0 i))) =
      2 * ∑ i, w i * ((∑ j, A0 i j * x j - b0 i) * t) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have e5 : ∑ a, ∑ i, 2 * (w a * (Mx A b x a i * δ i)) =
      2 * ∑ a, ∑ i, w a * (Mx A b x a i * δ i) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
  rw [e1, e2, e3, e4, e5]
  ring

theorem aux_srls_rS {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) :
    ∃ (d : Fin p → ℝ) (τ : ℝ), d ⬝ᵥ d ≤ 1 ∧ τ * (d ⬝ᵥ d) = τ ∧
      rS A0 A b0 b 1 x ^ 2 =
        ((A0 *ᵥ x - b0) + Mx A b x *ᵥ d) ⬝ᵥ ((A0 *ᵥ x - b0) + Mx A b x *ᵥ d) ∧
      0 ≤ rS A0 A b0 b 1 x ∧
      (∀ e, ((A0 *ᵥ x - b0) + Mx A b x *ᵥ d) ⬝ᵥ (Mx A b x *ᵥ e) = τ * (d ⬝ᵥ e)) ∧
      (∀ e, (Mx A b x *ᵥ e) ⬝ᵥ (Mx A b x *ᵥ e) ≤ τ * (e ⬝ᵥ e)) := by
  obtain ⟨d, τ, hd, hτ, hmax, hL, hN⟩ := aux_srls_kkt (Mx A b x) (A0 *ᵥ x - b0)
  have hres : ∀ δ, structuredResidual A0 A b0 b x δ =
      Real.sqrt (((A0 *ᵥ x - b0) + Mx A b x *ᵥ δ) ⬝ᵥ ((A0 *ᵥ x - b0) + Mx A b x *ᵥ δ)) := by
    intro δ; unfold structuredResidual; rw [aux_srls_resid, aux_srls_eucNorm_eq]
  have hrS : rS A0 A b0 b 1 x =
      Real.sqrt (((A0 *ᵥ x - b0) + Mx A b x *ᵥ d) ⬝ᵥ ((A0 *ᵥ x - b0) + Mx A b x *ᵥ d)) := by
    unfold rS
    apply IsGreatest.csSup_eq
    refine ⟨⟨d, (aux_srls_eucNorm_le_one d).2 hd, (hres d).symm⟩, ?_⟩
    rintro _ ⟨δ, hδ, rfl⟩
    rw [hres]
    exact Real.sqrt_le_sqrt (hmax δ ((aux_srls_eucNorm_le_one δ).1 hδ))
  refine ⟨d, τ, hd, hτ, ?_, ?_, hL, hN⟩
  · rw [hrS, Real.sq_sqrt (aux_srls_dot_self_nonneg _)]
  · rw [hrS]; exact Real.sqrt_nonneg _

theorem aux_srls_alg {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ) (r : Fin n → ℝ)
    (d : Fin p → ℝ) (τ lam : ℝ) (hτ : τ * (d ⬝ᵥ d) = τ)
    (hlam : (r + M *ᵥ d) ⬝ᵥ (r + M *ᵥ d) ≤ lam)
    (hL : ∀ e, (r + M *ᵥ d) ⬝ᵥ (M *ᵥ e) = τ * (d ⬝ᵥ e))
    (hN : ∀ e, (M *ᵥ e) ⬝ᵥ (M *ᵥ e) ≤ τ * (e ⬝ᵥ e)) (t : ℝ) (e : Fin p → ℝ)
    (w : Fin n → ℝ) :
    0 ≤ (lam - τ) * t ^ 2 + τ * ((t • d + e) ⬝ᵥ (t • d + e)) +
      2 * (w ⬝ᵥ (t • r + M *ᵥ (t • d + e))) + w ⬝ᵥ w := by
  set v := r + M *ᵥ d with hv
  have hu : t • r + M *ᵥ (t • d + e) = t • v + M *ᵥ e := by
    rw [mulVec_add, mulVec_smul, hv, smul_add]; abel
  rw [hu]
  have h1 : (t • d + e) ⬝ᵥ (t • d + e) = t ^ 2 * (d ⬝ᵥ d) + 2 * t * (d ⬝ᵥ e) + e ⬝ᵥ e := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm e d]
    ring
  have h2 : w ⬝ᵥ (t • v + M *ᵥ e) = t * (w ⬝ᵥ v) + w ⬝ᵥ (M *ᵥ e) := by
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hsq := aux_srls_dot_self_nonneg (w + (t • v + M *ᵥ e))
  have h3 : (w + (t • v + M *ᵥ e)) ⬝ᵥ (w + (t • v + M *ᵥ e)) =
      w ⬝ᵥ w + 2 * (t * (w ⬝ᵥ v) + w ⬝ᵥ (M *ᵥ e)) +
        (t ^ 2 * (v ⬝ᵥ v) + 2 * t * (v ⬝ᵥ (M *ᵥ e)) + (M *ᵥ e) ⬝ᵥ (M *ᵥ e)) := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm v w, dotProduct_comm (M *ᵥ e) w, dotProduct_comm (M *ᵥ e) v]
    ring
  rw [h3] at hsq
  rw [h1, h2]
  have hLe := hL e
  have hNe := hN e
  have h4 : τ * (d ⬝ᵥ d) * t ^ 2 = τ * t ^ 2 := by rw [hτ]
  have h5 : 0 ≤ t ^ 2 * (lam - v ⬝ᵥ v) := mul_nonneg (sq_nonneg t) (sub_nonneg.2 hlam)
  rw [hLe] at hsq
  nlinarith

end RobustLS.Structured

open RobustLS.Structured

theorem solution {n m p : ℕ} (hp : 1 ≤ p) (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ) :
    (∀ (x : Fin m → ℝ) (lam : ℝ),
        (∃ τ : ℝ, SDP32Feasible A0 A b0 b lam τ x) ↔ rS A0 A b0 b 1 x ^ 2 ≤ lam) ∧
      ∀ (lam τ : ℝ) (x : Fin m → ℝ),
        SDP32Optimal A0 A b0 b lam τ x ↔
          IsSRLSSolution A0 A b0 b 1 x ∧ lam = rS A0 A b0 b 1 x ^ 2 ∧
            SDP32Feasible A0 A b0 b lam τ x := by
  have partA : ∀ (x : Fin m → ℝ) (lam : ℝ),
      (∃ τ : ℝ, SDP32Feasible A0 A b0 b lam τ x) ↔ rS A0 A b0 b 1 x ^ 2 ≤ lam := by
    intro x lam
    obtain ⟨d, τ, hd, hτ, hrS2, hrS0, hL, hN⟩ := aux_srls_rS A0 A b0 b x
    constructor
    · rintro ⟨τ', hF⟩
      have hQ := hF.dotProduct_mulVec_nonneg
      have hτ'0 : 0 ≤ τ' := by
        have := hQ (Sum.elim (Sum.elim (fun _ => 0) (Pi.single ⟨0, hp⟩ 1)) 0)
        rw [aux_srls_quad] at this
        simpa using this
      have := hQ (Sum.elim (Sum.elim (fun _ => 1) d) (-((A0 *ᵥ x - b0) + Mx A b x *ᵥ d)))
      rw [aux_srls_quad] at this
      simp only [one_smul, neg_dotProduct, dotProduct_neg, neg_neg, one_pow, mul_one] at this
      rw [hrS2]
      nlinarith [mul_nonneg hτ'0 (sub_nonneg.2 hd)]
    · intro hlam
      refine ⟨τ, ?_⟩
      apply PosSemidef.of_dotProduct_mulVec_nonneg (aux_srls_herm A0 A b0 b lam τ x)
      intro z
      have hz : z = Sum.elim (Sum.elim (fun _ => z (Sum.inl (Sum.inl ())))
          (fun j => z (Sum.inl (Sum.inr j)))) (fun k => z (Sum.inr k)) := by
        funext i; rcases i with ((_ | i) | i) <;> rfl
      rw [hz, aux_srls_quad]
      have hδ : (fun j => z (Sum.inl (Sum.inr j))) =
          z (Sum.inl (Sum.inl ())) • d + ((fun j => z (Sum.inl (Sum.inr j))) -
            z (Sum.inl (Sum.inl ())) • d) := by abel
      rw [hδ]
      exact aux_srls_alg (Mx A b x) (A0 *ᵥ x - b0) d τ lam hτ (hrS2 ▸ hlam) hL hN _ _ _
  refine ⟨partA, ?_⟩
  intro lam τ x
  constructor
  · rintro ⟨hF, hopt⟩
    have h1 : rS A0 A b0 b 1 x ^ 2 ≤ lam := (partA x lam).1 ⟨τ, hF⟩
    obtain ⟨τ', hτ'⟩ := (partA x (rS A0 A b0 b 1 x ^ 2)).2 le_rfl
    have h2 := hopt _ _ _ hτ'
    refine ⟨?_, le_antisymm h2 h1, hF⟩
    intro x'
    obtain ⟨τ'', h⟩ := (partA x' (rS A0 A b0 b 1 x' ^ 2)).2 le_rfl
    have h3 := hopt _ _ _ h
    obtain ⟨_, _, _, _, _, h0', _, _⟩ := aux_srls_rS A0 A b0 b x'
    obtain ⟨_, _, _, _, _, h0, _, _⟩ := aux_srls_rS A0 A b0 b x
    nlinarith
  · rintro ⟨hsrls, hlam, hF⟩
    refine ⟨hF, ?_⟩
    intro lam' τ' x' hF'
    have h1 := (partA x' lam').1 ⟨τ', hF'⟩
    have h2 := hsrls x'
    obtain ⟨_, _, _, _, _, h0, _, _⟩ := aux_srls_rS A0 A b0 b x
    rw [hlam]
    nlinarith
