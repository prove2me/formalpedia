-- Prove2me | solution 1 for OpaqueQueue.Equilibrium.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T20:05:16.638838+00:00
-- url     : https://prove2.me/submissions/030849d9-21e4-406c-b053-c899fecfc9d1

import Mathlib
import Definitions.Def_OpaqueQueue_Equilibrium_Model

set_option autoImplicit false

namespace OQ03bae388
open OpaqueQueue.Equilibrium Filter Topology Set

noncomputable def E (P : Params) (n : ℕ) : ℝ := Real.exp (v P n / P.θ)
noncomputable def L (P : Params) (x : ℝ) (n : ℕ) : ℝ :=
  Real.log (x * Real.exp (v P n / P.θ) + 1 - x)
noncomputable def T (P : Params) (q : ℝ) : ℝ := ∑' k, weight P q k * phi P q k
noncomputable def S (P : Params) (q : ℝ) : ℝ := ∑' k, weight P q k
noncomputable def D (P : Params) (s b : ℝ) (k : ℕ) : ℝ :=
  s ^ k * ∏ i ∈ Finset.range k, min 1 (E P i / (1 - b))

def Good (P : Params) (q : ℝ) : Prop :=
  Summable (weight P q) ∧ (∀ y ∈ Icc (0:ℝ) 1, Summable fun k => weight P q k * L P y k) ∧
    (∀ x : ℝ, 0 ≤ x → x < 1 → Summable fun k => weight P q k * phi P x k)

lemma jp_eq (P : Params) (q : ℝ) (n : ℕ) :
    joinProb P q n = q * E P n / (1 - q + q * E P n) := rfl
lemma phi_eq (P : Params) (x : ℝ) (n : ℕ) :
    phi P x n = (E P n - 1) / (x * E P n + 1 - x) := rfl
lemma L_eq (P : Params) (x : ℝ) (n : ℕ) : L P x n = Real.log (x * E P n + 1 - x) := rfl

variable {P : Params}

lemma E_pos (n : ℕ) : 0 < E P n := Real.exp_pos _

lemma rho_pos (hS : P.Standing) : 0 < rho P := div_pos hS.1 hS.2.1

lemma E_eq (n : ℕ) :
    E P n = Real.exp ((P.R - P.p) / P.θ) * (Real.exp (-(P.C / P.mu) / P.θ)) ^ n := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  unfold E v
  congr 1
  ring

lemma c_lt_one (hS : P.Standing) : Real.exp (-(P.C / P.mu) / P.θ) < 1 := by
  obtain ⟨_, hmu, hC, _, hθ⟩ := hS
  have h0 : 0 < P.C / P.mu / P.θ := by positivity
  have h1 : -(P.C / P.mu) / P.θ < 0 := by rw [neg_div]; linarith
  calc _ < Real.exp 0 := Real.exp_lt_exp.2 h1
    _ = 1 := Real.exp_zero

lemma E_tendsto (hS : P.Standing) : Tendsto (E P) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le (c_lt_one hS)).const_mul
    (Real.exp ((P.R - P.p) / P.θ))
  rw [mul_zero] at h
  exact h.congr (fun n => (E_eq n).symm)

lemma E_anti (hS : P.Standing) {m n : ℕ} (h : m ≤ n) : E P n ≤ E P m := by
  rw [E_eq, E_eq]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact pow_le_pow_of_le_one (Real.exp_pos _).le (c_lt_one hS).le h

lemma E0_gt (hS : P.Standing) : 1 < E P 0 := by
  obtain ⟨_, _, _, hpR, hθ⟩ := hS
  have hv : v P 0 = P.R - P.p := by simp [v]
  unfold E
  rw [hv]
  calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ < _ := Real.exp_lt_exp.2 (div_pos (sub_pos.2 hpR) hθ)

lemma den_pos {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (n : ℕ) : 0 < x * E P n + 1 - x := by
  have hE := E_pos (P := P) n
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst h; norm_num
  · have := mul_pos h hE
    linarith [hx.2]

lemma jp_nonneg {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (n : ℕ) : 0 ≤ joinProb P q n := by
  rw [jp_eq]; have := den_pos (P := P) hq n
  exact div_nonneg (mul_nonneg hq.1 (E_pos n).le) (by linarith)

lemma jp_le_one {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (n : ℕ) : joinProb P q n ≤ 1 := by
  rw [jp_eq]; have := den_pos (P := P) hq n
  rw [div_le_one (by linarith)]; linarith [hq.2]

lemma jp_pos {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (hq0 : 0 < q) (n : ℕ) : 0 < joinProb P q n := by
  rw [jp_eq]; have := den_pos (P := P) hq n
  exact div_pos (mul_pos hq0 (E_pos n)) (by linarith)

lemma jp_le_m {q b : ℝ} (hq : q ∈ Icc (0:ℝ) b) (hb : b < 1) (n : ℕ) :
    joinProb P q n ≤ E P n / (1 - b) := by
  rw [jp_eq]
  have hE := E_pos (P := P) n
  have h1 : 0 < 1 - b := by linarith
  have hqE := mul_nonneg hq.1 hE.le
  have hq1 : q * E P n ≤ E P n := by
    have : q * E P n ≤ 1 * E P n := mul_le_mul_of_nonneg_right (by linarith [hq.2]) hE.le
    linarith
  calc q * E P n / (1 - q + q * E P n) ≤ q * E P n / (1 - b) :=
        div_le_div_of_nonneg_left hqE h1 (by linarith [hq.2])
    _ ≤ E P n / (1 - b) := div_le_div_of_nonneg_right hq1 h1.le

lemma jp_one (n : ℕ) : joinProb P 1 n = 1 := by
  rw [jp_eq]
  have h := (E_pos (P := P) n).ne'
  rw [show (1:ℝ) - 1 + 1 * E P n = E P n by ring, one_mul, div_self h]

lemma jp_zero (n : ℕ) : joinProb P 0 n = 0 := by simp [jp_eq]

lemma jp_strict {q1 q2 : ℝ} (h0 : 0 < q1) (h12 : q1 < q2) (h2 : q2 ≤ 1) (n : ℕ) :
    joinProb P q1 n < joinProb P q2 n := by
  have hq1 : q1 ∈ Icc (0:ℝ) 1 := ⟨h0.le, by linarith⟩
  have hq2 : q2 ∈ Icc (0:ℝ) 1 := ⟨by linarith, h2⟩
  have d1 := den_pos (P := P) hq1 n
  have d2 := den_pos (P := P) hq2 n
  have hE := E_pos (P := P) n
  rw [jp_eq, jp_eq, div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_lt_mul_of_pos_right h12 hE]

lemma jp_sub {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (n : ℕ) :
    joinProb P q n = q + q * (1 - q) * phi P q n := by
  rw [jp_eq, phi_eq]
  have hd := den_pos (P := P) hq n
  have hd' : (1 - q + q * E P n) ≠ 0 := by intro h; linarith
  field_simp
  ring

lemma weight_zero (q : ℝ) : weight P q 0 = 1 := by simp [weight]

lemma weight_succ (q : ℝ) (k : ℕ) :
    weight P q (k + 1) = weight P q k * (rho P * joinProb P q k) := by
  simp only [weight, pow_succ, Finset.prod_range_succ]; ring

lemma weight_one' (q : ℝ) : weight P q 1 = rho P * joinProb P q 0 := by
  have := weight_succ (P := P) q 0
  simpa [weight_zero] using this

lemma weight_nonneg (hS : P.Standing) {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (k : ℕ) :
    0 ≤ weight P q k := by
  unfold weight
  exact mul_nonneg (pow_nonneg (rho_pos hS).le _) (Finset.prod_nonneg fun i _ => jp_nonneg hq i)

lemma weight_pos (hS : P.Standing) {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (hq0 : 0 < q) (k : ℕ) :
    0 < weight P q k := by
  unfold weight
  exact mul_pos (pow_pos (rho_pos hS) _) (Finset.prod_pos fun i _ => jp_pos hq hq0 i)

lemma weight_one (k : ℕ) : weight P 1 k = rho P ^ k := by simp [weight, jp_one]

lemma weight_zero_at {n : ℕ} (hn : n ≠ 0) : weight P 0 n = 0 := by
  unfold weight
  rw [Finset.prod_eq_zero (Finset.mem_range.2 (Nat.pos_of_ne_zero hn)) (jp_zero 0), mul_zero]

lemma m_pos {b : ℝ} (hb : b < 1) (i : ℕ) : 0 < min 1 (E P i / (1 - b)) :=
  lt_min one_pos (div_pos (E_pos i) (by linarith))

lemma D_pos {s b : ℝ} (hs : 0 < s) (hb : b < 1) (k : ℕ) : 0 < D P s b k :=
  mul_pos (pow_pos hs k) (Finset.prod_pos fun i _ => m_pos hb i)

lemma D_summable (hS : P.Standing) {s b : ℝ} (hs : 0 < s) (hb : b < 1) :
    Summable (D P s b) := by
  refine summable_of_ratio_test_tendsto_lt_one (l := 0) zero_lt_one
    (Eventually.of_forall fun n => (D_pos (P := P) hs hb n).ne') ?_
  have h1 : ∀ n, ‖D P s b (n+1)‖ / ‖D P s b n‖ = s * min 1 (E P n / (1 - b)) := by
    intro n
    rw [Real.norm_of_nonneg (D_pos (P := P) hs hb _).le, Real.norm_of_nonneg (D_pos (P := P) hs hb _).le]
    have := (D_pos (P := P) hs hb n).ne'
    rw [div_eq_iff this]
    simp only [D, pow_succ, Finset.prod_range_succ]; ring
  simp_rw [h1]
  have h2 : Tendsto (fun n => min 1 (E P n / (1 - b))) atTop (𝓝 0) := by
    have h3 : Tendsto (fun n => E P n / (1 - b)) atTop (𝓝 0) := by
      simpa using (E_tendsto hS).div_const (1 - b)
    have h4 := (tendsto_const_nhds (x := (1:ℝ))).min h3
    rwa [min_eq_right zero_le_one] at h4
  simpa using h2.const_mul s

lemma weight_le_D (hS : P.Standing) {q b : ℝ} (hq : q ∈ Icc (0:ℝ) b) (hb : b < 1) (k : ℕ) :
    weight P q k ≤ D P (rho P) b k := by
  have hq' : q ∈ Icc (0:ℝ) 1 := ⟨hq.1, by linarith [hq.2]⟩
  unfold weight D
  exact mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun i _ => jp_nonneg hq' i)
      (fun i _ => le_min (jp_le_one hq' i) (jp_le_m hq hb i))) (pow_nonneg (rho_pos hS).le _)

lemma D_two (hS : P.Standing) {b : ℝ} (hb : b < 1) (k : ℕ) :
    D P (rho P) b k * ((k:ℝ) + 1) ≤ D P (2 * rho P) b k := by
  have h : (k + 1 : ℕ) ≤ 2 ^ k := Nat.lt_two_pow_self
  have h' : ((k:ℝ) + 1) ≤ (2:ℝ) ^ k := by exact_mod_cast h
  have hD := (D_pos (P := P) (rho_pos hS) hb k).le
  have e : D P (2 * rho P) b k = (2:ℝ) ^ k * D P (rho P) b k := by
    simp only [D, mul_pow]; ring
  rw [e]
  nlinarith

lemma phi_bound (hS : P.Standing) {x b : ℝ} (hx : x ∈ Icc (0:ℝ) b) (hb : b < 1) (k : ℕ) :
    |phi P x k| ≤ (E P 0 + 1) / (1 - b) := by
  have hx' : x ∈ Icc (0:ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
  have hd := den_pos (P := P) hx' k
  have hE := E_pos (P := P) k
  have hE0 := E_anti (P := P) hS (Nat.zero_le k)
  have h1 : 0 < 1 - b := by linarith
  have hdge : 1 - b ≤ x * E P k + 1 - x := by nlinarith [mul_nonneg hx.1 hE.le, hx.2]
  rw [phi_eq, abs_div, abs_of_pos hd]
  have habs : |E P k - 1| ≤ E P 0 + 1 := abs_le.2 ⟨by linarith, by linarith⟩
  calc |E P k - 1| / (x * E P k + 1 - x) ≤ (E P 0 + 1) / (x * E P k + 1 - x) :=
        div_le_div_of_nonneg_right habs hd.le
    _ ≤ (E P 0 + 1) / (1 - b) :=
        div_le_div_of_nonneg_left (by linarith [E0_gt hS]) h1 hdge

lemma L_bound (hS : P.Standing) {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) (k : ℕ) :
    |L P y k| ≤ (P.R - P.p) / P.θ + P.C / P.mu / P.θ * k := by
  obtain ⟨hlam, hmu, hC, hpR, hθ⟩ := hS
  have hE := E_pos (P := P) k
  have hz := den_pos (P := P) hy k
  have hlogE : Real.log (E P k) = (P.R - P.p) / P.θ - P.C / P.mu / P.θ * k := by
    unfold E v; rw [Real.log_exp]; ring
  have hA : 0 ≤ (P.R - P.p) / P.θ := div_nonneg (sub_nonneg.2 hpR.le) hθ.le
  have hB : 0 ≤ P.C / P.mu / P.θ * (k:ℝ) := by positivity
  rw [L_eq]
  rcases le_total 1 (E P k) with h | h
  · have h1 : 1 ≤ y * E P k + 1 - y := by nlinarith [mul_nonneg hy.1 (sub_nonneg.2 h)]
    have h2 : y * E P k + 1 - y ≤ E P k := by
      nlinarith [mul_nonneg (sub_nonneg.2 hy.2) (sub_nonneg.2 h)]
    have hl0 : 0 ≤ Real.log (y * E P k + 1 - y) := Real.log_nonneg h1
    have hl1 : Real.log (y * E P k + 1 - y) ≤ Real.log (E P k) := Real.log_le_log hz h2
    rw [abs_of_nonneg hl0]; linarith
  · have h1 : y * E P k + 1 - y ≤ 1 := by nlinarith [mul_nonneg hy.1 (sub_nonneg.2 h)]
    have h2 : E P k ≤ y * E P k + 1 - y := by
      nlinarith [mul_nonneg (sub_nonneg.2 hy.2) (sub_nonneg.2 h)]
    have hl0 : Real.log (y * E P k + 1 - y) ≤ 0 := Real.log_nonpos hz.le h1
    have hl1 : Real.log (E P k) ≤ Real.log (y * E P k + 1 - y) := Real.log_le_log hE h2
    rw [abs_of_nonpos hl0]; linarith

lemma term_bound (hS : P.Standing) {q x b : ℝ} (hq : q ∈ Icc (0:ℝ) b) (hx : x ∈ Icc (0:ℝ) b)
    (hb : b < 1) (k : ℕ) :
    ‖weight P q k * phi P x k‖ ≤ D P (rho P) b k * ((E P 0 + 1) / (1 - b)) := by
  have hq' : q ∈ Icc (0:ℝ) 1 := ⟨hq.1, by linarith [hq.2]⟩
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (weight_nonneg hS hq' k)]
  exact mul_le_mul (weight_le_D hS hq hb k) (phi_bound hS hx hb k) (abs_nonneg _)
    (D_pos (P := P) (rho_pos hS) hb k).le

lemma summ_w_lt (hS : P.Standing) {q b : ℝ} (hq : q ∈ Icc (0:ℝ) b) (hb : b < 1) :
    Summable (weight P q) := by
  have hq' : q ∈ Icc (0:ℝ) 1 := ⟨hq.1, by linarith [hq.2]⟩
  exact Summable.of_nonneg_of_le (weight_nonneg hS hq') (weight_le_D hS hq hb)
    (D_summable hS (rho_pos hS) hb)

lemma summ_wphi_lt (hS : P.Standing) {q x b : ℝ} (hq : q ∈ Icc (0:ℝ) b) (hx : x ∈ Icc (0:ℝ) b)
    (hb : b < 1) : Summable (fun k => weight P q k * phi P x k) :=
  Summable.of_norm_bounded ((D_summable hS (rho_pos hS) hb).mul_right _)
    (term_bound hS hq hx hb)

lemma summ_wL_lt (hS : P.Standing) {q b y : ℝ} (hq : q ∈ Icc (0:ℝ) b) (hb : b < 1)
    (hy : y ∈ Icc (0:ℝ) 1) : Summable (fun k => weight P q k * L P y k) := by
  have hq' : q ∈ Icc (0:ℝ) 1 := ⟨hq.1, by linarith [hq.2]⟩
  obtain ⟨hlam, hmu, hC, hpR, hθ⟩ := hS
  have hA : 0 ≤ (P.R - P.p) / P.θ := div_nonneg (sub_nonneg.2 hpR.le) hθ.le
  have hB : 0 ≤ P.C / P.mu / P.θ := by positivity
  have hS' : P.Standing := ⟨hlam, hmu, hC, hpR, hθ⟩
  have h2 : 0 < 2 * rho P := by linarith [rho_pos hS']
  refine Summable.of_norm_bounded ((D_summable hS' h2 hb).mul_left
    ((P.R - P.p) / P.θ + P.C / P.mu / P.θ)) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (weight_nonneg hS' hq' k)]
  have hw := weight_le_D hS' hq hb k
  have hw0 := weight_nonneg hS' hq' k
  have hL := L_bound hS' hy k
  have hDt := D_two hS' hb k
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hD0 := (D_pos (P := P) (rho_pos hS') hb k).le
  have e1 : (P.R - P.p) / P.θ + P.C / P.mu / P.θ * k ≤
      ((P.R - P.p) / P.θ + P.C / P.mu / P.θ) * ((k:ℝ) + 1) := by nlinarith
  calc weight P q k * |L P y k|
      ≤ D P (rho P) b k * (((P.R - P.p) / P.θ + P.C / P.mu / P.θ) * ((k:ℝ) + 1)) :=
        mul_le_mul hw (hL.trans e1) (abs_nonneg _) hD0
    _ = ((P.R - P.p) / P.θ + P.C / P.mu / P.θ) * (D P (rho P) b k * ((k:ℝ) + 1)) := by ring
    _ ≤ ((P.R - P.p) / P.θ + P.C / P.mu / P.θ) * D P (2 * rho P) b k :=
        mul_le_mul_of_nonneg_left hDt (by positivity)

lemma good_lt (hS : P.Standing) {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (hq1 : q < 1) : Good P q :=
  ⟨summ_w_lt hS ⟨hq.1, le_rfl⟩ hq1, fun y hy => summ_wL_lt hS ⟨hq.1, le_rfl⟩ hq1 hy,
    fun x hx0 hx1 => summ_wphi_lt hS (b := max q x) ⟨hq.1, le_max_left _ _⟩
      ⟨hx0, le_max_right _ _⟩ (max_lt hq1 hx1)⟩

lemma good_one (hS : P.Standing) (hρ : rho P < 1) : Good P 1 := by
  have hr := rho_pos hS
  have hw : weight P 1 = fun k => rho P ^ k := funext weight_one
  have hg := summable_geometric_of_lt_one hr.le hρ
  have hnorm : ‖rho P‖ < 1 := by rw [Real.norm_of_nonneg hr.le]; exact hρ
  refine ⟨by rw [hw]; exact hg, fun y hy => ?_, fun x hx0 hx1 => ?_⟩
  · obtain ⟨hlam, hmu, hC, hpR, hθ⟩ := hS
    have hA : 0 ≤ (P.R - P.p) / P.θ := div_nonneg (sub_nonneg.2 hpR.le) hθ.le
    have hB : 0 ≤ P.C / P.mu / P.θ := by positivity
    refine Summable.of_norm_bounded ((hg.mul_left ((P.R - P.p) / P.θ)).add
      ((summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).mul_left (P.C / P.mu / P.θ)))
      (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, weight_one, abs_of_nonneg (pow_nonneg hr.le _)]
    have hL := L_bound ⟨hlam, hmu, hC, hpR, hθ⟩ hy k
    have hp := pow_nonneg hr.le k
    calc rho P ^ k * |L P y k| ≤ rho P ^ k * ((P.R - P.p) / P.θ + P.C / P.mu / P.θ * k) :=
          mul_le_mul_of_nonneg_left hL hp
      _ = (P.R - P.p) / P.θ * rho P ^ k + P.C / P.mu / P.θ * ((k:ℝ) ^ 1 * rho P ^ k) := by ring
  · have hx : x ∈ Icc (0:ℝ) x := ⟨hx0, le_rfl⟩
    refine Summable.of_norm_bounded (hg.mul_right ((E P 0 + 1) / (1 - x))) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, weight_one, abs_of_nonneg (pow_nonneg hr.le _)]
    exact mul_le_mul_of_nonneg_left (phi_bound hS hx hx1 k) (pow_nonneg hr.le _)

lemma S_pos (hS : P.Standing) {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (hG : Good P q) : 0 < S P q := by
  have h := Summable.le_tsum hG.1 0 (fun j _ => weight_nonneg hS hq j)
  rw [weight_zero] at h
  unfold S; linarith

lemma obj_eq (q y : ℝ) :
    obj P (stat P q) y = P.θ * ((∑' k, weight P q k * L P y k) / S P q) := by
  simp only [obj, stat, S, L]
  rw [← tsum_div_const]
  congr 1
  apply tsum_congr
  intro k
  ring

lemma tangent {x y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) (hx : x ∈ Icc (0:ℝ) 1) (k : ℕ) :
    L P y k ≤ L P x k + (y - x) * phi P x k := by
  have hz := den_pos (P := P) hy k
  have hw := den_pos (P := P) hx k
  rw [L_eq, L_eq, phi_eq]
  have h := Real.log_le_sub_one_of_pos (div_pos hz hw)
  rw [Real.log_div hz.ne' hw.ne'] at h
  have e : (y * E P k + 1 - y) / (x * E P k + 1 - x) - 1 =
      (y - x) * ((E P k - 1) / (x * E P k + 1 - x)) := by
    rw [div_sub_one hw.ne', mul_div_assoc']; congr 1; ring
  linarith

lemma opt_of_T (hS : P.Standing) {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (hq1 : q < 1) (hT : T P q = 0) :
    IsOptimal P (stat P q) q := by
  refine ⟨hq, fun y hy => ?_⟩
  have hG := good_lt hS hq hq1
  rw [obj_eq, obj_eq]
  have hSp := S_pos hS hq hG
  have hθ := hS.2.2.2.2
  apply mul_le_mul_of_nonneg_left _ hθ.le
  apply div_le_div_of_nonneg_right _ hSp.le
  have key : ∀ k, weight P q k * L P y k ≤
      weight P q k * L P q k + (y - q) * (weight P q k * phi P q k) := fun k => by
    have ht := tangent (P := P) hy hq k
    have hw := weight_nonneg hS hq k
    calc weight P q k * L P y k ≤ weight P q k * (L P q k + (y - q) * phi P q k) :=
          mul_le_mul_of_nonneg_left ht hw
      _ = weight P q k * L P q k + (y - q) * (weight P q k * phi P q k) := by ring
  have hs2 := (hG.2.2 q hq.1 hq1).mul_left (y - q)
  calc ∑' k, weight P q k * L P y k
      ≤ ∑' k, (weight P q k * L P q k + (y - q) * (weight P q k * phi P q k)) :=
        Summable.tsum_le_tsum key (hG.2.1 y hy) ((hG.2.1 q hq).add hs2)
    _ = ∑' k, weight P q k * L P q k := by
        rw [Summable.tsum_add (hG.2.1 q hq) hs2, tsum_mul_left]
        unfold T at hT; rw [hT]; ring

lemma consist_iff (hS : P.Standing) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (q = ∑' n, joinProb P q n * stat P q n) ↔ T P q = 0 := by
  have hq : q ∈ Icc (0:ℝ) 1 := ⟨hq0.le, hq1.le⟩
  have hG := good_lt hS hq hq1
  have hSp := S_pos hS hq hG
  have hsum : ∑' n, joinProb P q n * stat P q n = q + q * (1 - q) / S P q * T P q := by
    have e : ∀ n, joinProb P q n * stat P q n =
        q / S P q * weight P q n + q * (1 - q) / S P q * (weight P q n * phi P q n) := by
      intro n
      rw [jp_sub hq n]
      show (q + q * (1 - q) * phi P q n) * (weight P q n / S P q) = _
      field_simp
    rw [tsum_congr e, Summable.tsum_add (hG.1.mul_left _) ((hG.2.2 q hq0.le hq1).mul_left _),
      tsum_mul_left, tsum_mul_left]
    show q / S P q * S P q + q * (1 - q) / S P q * T P q = _
    rw [div_mul_cancel₀ q hSp.ne']
  have hc : 0 < q * (1 - q) / S P q := div_pos (mul_pos hq0 (by linarith)) hSp
  rw [hsum]
  constructor
  · intro h
    have h2 : q * (1 - q) / S P q * T P q = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hc.ne'
    · exact h3
  · intro h; rw [h]; ring

lemma not_eq_zero (hS : P.Standing) : ¬ IsEquilibrium P 0 := by
  rintro ⟨_, _, hO⟩
  have h := hO.2 1 ⟨zero_le_one, le_rfl⟩
  rw [obj_eq, obj_eq] at h
  have hsingle : ∀ y : ℝ, ∑' k, weight P 0 k * L P y k = L P y 0 := fun y => by
    rw [tsum_eq_single 0 (fun k hk => by rw [weight_zero_at hk, zero_mul]), weight_zero, one_mul]
  have hS0 : S P 0 = 1 := by
    unfold S
    rw [tsum_eq_single 0 (fun k hk => weight_zero_at hk), weight_zero]
  rw [hsingle, hsingle, hS0, div_one, div_one] at h
  have h1 : L P 1 0 = Real.log (E P 0) := by
    rw [L_eq]; congr 1; ring
  have h0 : L P 0 0 = 0 := by simp [L_eq]
  rw [h1, h0, mul_zero] at h
  have := Real.log_pos (E0_gt hS)
  have := mul_pos hS.2.2.2.2 this
  linarith

lemma phi_nonneg {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) {k : ℕ} (h : 1 ≤ E P k) : 0 ≤ phi P x k := by
  rw [phi_eq]; exact div_nonneg (by linarith) (den_pos hx k).le

lemma phi_nonpos {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) {k : ℕ} (h : E P k ≤ 1) : phi P x k ≤ 0 := by
  rw [phi_eq]; exact div_nonpos_iff.2 (Or.inr ⟨by linarith, (den_pos hx k).le⟩)

lemma phi_anti (hS : P.Standing) {x1 x2 : ℝ} (hx1 : x1 ∈ Icc (0:ℝ) 1) (hx2 : x2 ∈ Icc (0:ℝ) 1)
    (h : x1 ≤ x2) (k : ℕ) : phi P x2 k ≤ phi P x1 k := by
  have d1 := den_pos (P := P) hx1 k
  have d2 := den_pos (P := P) hx2 k
  rw [phi_eq, phi_eq, div_le_div_iff₀ d2 d1]
  nlinarith [mul_nonneg (sub_nonneg.2 h) (sq_nonneg (E P k - 1))]

lemma cross (hS : P.Standing) {q1 q2 : ℝ} (h0 : 0 < q1) (h12 : q1 < q2) (h2 : q2 ≤ 1)
    (hG2 : Good P q2) (hT : T P q1 = 0) : ∑' k, weight P q2 k * phi P q1 k < 0 := by
  classical
  have hq1 : q1 ∈ Icc (0:ℝ) 1 := ⟨h0.le, by linarith⟩
  have hq2 : q2 ∈ Icc (0:ℝ) 1 := ⟨by linarith, h2⟩
  have hq11 : q1 < 1 := by linarith
  have hG1 := good_lt hS hq1 hq11
  have hex : ∃ k, E P k < 1 :=
    ((E_tendsto hS).eventually (eventually_lt_nhds one_pos)).exists
  have hN1 : ∀ k < Nat.find hex, 1 ≤ E P k := fun k hk => not_lt.1 (Nat.find_min hex hk)
  have hN2 : ∀ k, Nat.find hex ≤ k → E P k ≤ 1 :=
    fun k hk => ((E_anti hS hk).trans_lt (Nat.find_spec hex)).le
  have hNpos : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso
      have := Nat.find_spec hex
      rw [h] at this
      linarith [E0_gt hS]
    · exact h
  set N := Nat.find hex with hNdef
  have hw1pos : ∀ k, 0 < weight P q1 k := weight_pos hS hq1 h0
  set w : ℕ → ℝ := fun k => weight P q2 k / weight P q1 k with hwdef
  have hwmono : Monotone w := monotone_nat_of_le_succ fun k => by
    simp only [hwdef]
    rw [weight_succ, weight_succ]
    have a := hw1pos k
    have b := weight_nonneg hS hq2 k
    have r := rho_pos hS
    have j1 := jp_pos (P := P) hq1 h0 k
    have j12 := (jp_strict (P := P) h0 h12 h2 k).le
    rw [div_le_div_iff₀ a (mul_pos a (mul_pos r j1))]
    have hm : weight P q2 k * weight P q1 k * rho P * joinProb P q1 k ≤
        weight P q2 k * weight P q1 k * rho P * joinProb P q2 k :=
      mul_le_mul_of_nonneg_left j12 (by positivity)
    calc weight P q2 k * (weight P q1 k * (rho P * joinProb P q1 k))
        = weight P q2 k * weight P q1 k * rho P * joinProb P q1 k := by ring
      _ ≤ weight P q2 k * weight P q1 k * rho P * joinProb P q2 k := hm
      _ = weight P q2 k * (rho P * joinProb P q2 k) * weight P q1 k := by ring
  have hw0 : w 0 = 1 := by simp [hwdef, weight_zero]
  have hwN : 1 < w N := by
    have h1 : w 1 ≤ w N := hwmono hNpos
    have hw1 : 1 < w 1 := by
      simp only [hwdef]
      rw [one_lt_div (hw1pos 1), weight_one', weight_one']
      exact mul_lt_mul_of_pos_left (jp_strict h0 h12 h2 0) (rho_pos hS)
    linarith
  have hrel : ∀ k, weight P q2 k = weight P q1 k * w k := fun k => by
    simp only [hwdef]; field_simp [(hw1pos k).ne']
  have hle : ∀ k, weight P q2 k * phi P q1 k ≤ weight P q1 k * phi P q1 k * w N := fun k => by
    rw [hrel k]
    by_cases hk : k < N
    · have hp := phi_nonneg hq1 (hN1 k hk)
      have := mul_le_mul_of_nonneg_left (hwmono hk.le) (mul_nonneg (hw1pos k).le hp)
      calc weight P q1 k * w k * phi P q1 k = weight P q1 k * phi P q1 k * w k := by ring
        _ ≤ _ := this
    · have hp := phi_nonpos hq1 (hN2 k (not_lt.1 hk))
      have := mul_le_mul_of_nonpos_left (hwmono (not_lt.1 hk))
        (mul_nonpos_iff.2 (Or.inl ⟨(hw1pos k).le, hp⟩))
      calc weight P q1 k * w k * phi P q1 k = weight P q1 k * phi P q1 k * w k := by ring
        _ ≤ _ := this
  have hlt : weight P q2 0 * phi P q1 0 < weight P q1 0 * phi P q1 0 * w N := by
    simp only [weight_zero, one_mul]
    have hp : 0 < phi P q1 0 := by
      rw [phi_eq]; exact div_pos (by linarith [E0_gt hS]) (den_pos hq1 0)
    exact lt_mul_of_one_lt_right hp hwN
  calc ∑' k, weight P q2 k * phi P q1 k < ∑' k, weight P q1 k * phi P q1 k * w N :=
        Summable.tsum_lt_tsum (i := 0) hle hlt (hG2.2.2 q1 h0.le hq11)
          ((hG1.2.2 q1 h0.le hq11).mul_right (w N))
    _ = T P q1 * w N := tsum_mul_right
    _ = 0 := by rw [hT, zero_mul]

lemma slope (hS : P.Standing) {q x : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (hG : Good P q)
    (hO : IsOptimal P (stat P q) q) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ (q - x) * ∑' k, weight P q k * phi P x k := by
  have hx : x ∈ Icc (0:ℝ) 1 := ⟨hx0, hx1.le⟩
  have h := hO.2 x hx
  rw [obj_eq, obj_eq] at h
  have hSp := S_pos hS hq hG
  have hθ := hS.2.2.2.2
  have h' : ∑' k, weight P q k * L P x k ≤ ∑' k, weight P q k * L P q k := by
    have h1 := le_of_mul_le_mul_left h hθ
    have h2 := mul_le_mul_of_nonneg_right h1 hSp.le
    rwa [div_mul_cancel₀ _ hSp.ne', div_mul_cancel₀ _ hSp.ne'] at h2
  have key : ∀ k, weight P q k * L P q k ≤
      weight P q k * L P x k + (q - x) * (weight P q k * phi P x k) := fun k => by
    have ht := tangent (P := P) hq hx k
    have hw := weight_nonneg hS hq k
    calc weight P q k * L P q k ≤ weight P q k * (L P x k + (q - x) * phi P x k) :=
          mul_le_mul_of_nonneg_left ht hw
      _ = weight P q k * L P x k + (q - x) * (weight P q k * phi P x k) := by ring
  have hs2 := (hG.2.2 x hx0 hx1).mul_left (q - x)
  have := Summable.tsum_le_tsum key (hG.2.1 q hq) ((hG.2.1 x hx).add hs2)
  rw [Summable.tsum_add (hG.2.1 x hx) hs2, tsum_mul_left] at this
  linarith

lemma term_contAt (hS : P.Standing) {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (k : ℕ) :
    ContinuousAt (fun q => weight P q k * phi P q k) q := by
  have hjp : ∀ i, ContinuousAt (fun q => joinProb P q i) q := fun i => by
    simp only [jp_eq]
    exact ContinuousAt.div (by fun_prop) (by fun_prop)
      (show 0 < 1 - q + q * E P i by have := den_pos (P := P) hq i; linarith).ne'
  have hw : ∀ k, ContinuousAt (fun q => weight P q k) q := by
    intro k
    induction k with
    | zero => simp only [weight_zero]; exact continuousAt_const
    | succ n ih =>
      simp only [weight_succ]
      exact ih.mul (continuousAt_const.mul (hjp n))
  have hphi : ContinuousAt (fun q => phi P q k) q := by
    simp only [phi_eq]
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (den_pos hq k).ne'
  exact (hw k).mul hphi

lemma T_contOn (hS : P.Standing) {b : ℝ} (hb : b < 1) : ContinuousOn (T P) (Icc 0 b) := by
  show ContinuousOn (fun q => ∑' k, weight P q k * phi P q k) (Icc 0 b)
  refine continuousOn_tsum (u := fun k => D P (rho P) b k * ((E P 0 + 1) / (1 - b)))
    (fun k q hq => (term_contAt hS ⟨hq.1, by linarith [hq.2]⟩ k).continuousWithinAt)
    ((D_summable hS (rho_pos hS) hb).mul_right _) (fun k q hq => term_bound hS hq hq hb k)

lemma T_zero : T P 0 = E P 0 - 1 := by
  unfold T
  rw [tsum_eq_single 0 (fun k hk => by rw [weight_zero_at hk, zero_mul]), weight_zero, phi_eq]
  simp

lemma claim (hS : P.Standing) (h1 : ¬ IsEquilibrium P 1) :
    ∃ M, (∀ k, M ≤ k → E P k ≤ 1) ∧
      ∑ k ∈ Finset.range M, weight P 1 k * phi P 1 k < 0 := by
  obtain ⟨N1, hN1⟩ : ∃ N1, ∀ k, N1 ≤ k → E P k ≤ 1 / 2 :=
    eventually_atTop.1 ((E_tendsto hS).eventually (eventually_le_nhds (by norm_num)))
  have h01 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  by_cases hρ : rho P < 1
  · have hG := good_one hS hρ
    have hSp := S_pos hS h01 hG
    have hadm : Admissible P 1 := ⟨h01, hG.1⟩
    have hcons : (1:ℝ) = ∑' n, joinProb P 1 n * stat P 1 n := by
      simp only [jp_one, one_mul]
      show (1:ℝ) = ∑' n, weight P 1 n / S P 1
      rw [tsum_div_const]
      exact (div_self hSp.ne').symm
    have hnopt : ¬ IsOptimal P (stat P 1) 1 := fun h => h1 ⟨hadm, hcons, h⟩
    obtain ⟨y, hy, hlt⟩ : ∃ y ∈ Icc (0:ℝ) 1, obj P (stat P 1) 1 < obj P (stat P 1) y := by
      by_contra hc
      push_neg at hc
      exact hnopt ⟨h01, hc⟩
    rw [obj_eq, obj_eq] at hlt
    have hlt' : ∑' k, weight P 1 k * L P 1 k < ∑' k, weight P 1 k * L P y k := by
      have h2 := lt_of_mul_lt_mul_left hlt hS.2.2.2.2.le
      have h3 := mul_lt_mul_of_pos_right h2 hSp
      rwa [div_mul_cancel₀ _ hSp.ne', div_mul_cancel₀ _ hSp.ne'] at h3
    have hGsum : Summable (fun k => weight P 1 k * (L P y k - L P 1 k)) := by
      have := (hG.2.1 y hy).sub (hG.2.1 1 h01)
      simpa [mul_sub] using this
    have hGpos : 0 < ∑' k, weight P 1 k * (L P y k - L P 1 k) := by
      simp only [mul_sub]
      rw [Summable.tsum_sub (hG.2.1 y hy) (hG.2.1 1 h01)]
      linarith
    have ht := hGsum.hasSum.tendsto_sum_nat
    obtain ⟨M, hM⟩ := eventually_atTop.1
      ((ht.eventually (eventually_gt_nhds hGpos)).and (eventually_ge_atTop N1))
    have hMp := hM M le_rfl
    refine ⟨M, fun k hk => (hN1 k (le_trans hMp.2 hk)).trans (by norm_num), ?_⟩
    have hb : ∑ k ∈ Finset.range M, weight P 1 k * (L P y k - L P 1 k) ≤
        (y - 1) * ∑ k ∈ Finset.range M, weight P 1 k * phi P 1 k := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      have ht := tangent (P := P) hy h01 k
      have hw := weight_nonneg hS h01 k
      calc weight P 1 k * (L P y k - L P 1 k) ≤ weight P 1 k * ((y - 1) * phi P 1 k) :=
            mul_le_mul_of_nonneg_left (by linarith) hw
        _ = (y - 1) * (weight P 1 k * phi P 1 k) := by ring
    have h0 := hMp.1
    by_contra hc
    push_neg at hc
    have : (y - 1) * ∑ k ∈ Finset.range M, weight P 1 k * phi P 1 k ≤ 0 :=
      mul_nonpos_iff.2 (Or.inr ⟨by linarith [hy.2], hc⟩)
    linarith
  · push_neg at hρ
    have hterm : ∀ k, N1 ≤ k → weight P 1 k * phi P 1 k ≤ -1 := by
      intro k hk
      have hE := E_pos (P := P) k
      have hEk := hN1 k hk
      rw [weight_one, phi_eq]
      have e : (1:ℝ) * E P k + 1 - 1 = E P k := by ring
      rw [e]
      have hp : (E P k - 1) / E P k ≤ -1 := by rw [div_le_iff₀ hE]; linarith
      have hr : 1 ≤ rho P ^ k := one_le_pow₀ hρ
      have hn : (E P k - 1) / E P k ≤ 0 := by linarith
      have := mul_le_mul_of_nonpos_right hr hn
      linarith
    set A := ∑ k ∈ Finset.range N1, weight P 1 k * phi P 1 k with hA
    refine ⟨N1 + (⌈A⌉₊ + 1), fun k hk => (hN1 k (by omega)).trans (by norm_num), ?_⟩
    rw [Finset.sum_range_add]
    have hs : ∑ x ∈ Finset.range (⌈A⌉₊ + 1), weight P 1 (N1 + x) * phi P 1 (N1 + x) ≤
        ∑ x ∈ Finset.range (⌈A⌉₊ + 1), (-1:ℝ) :=
      Finset.sum_le_sum fun x _ => hterm _ (by omega)
    have hs2 : ∑ x ∈ Finset.range (⌈A⌉₊ + 1), (-1:ℝ) = -((⌈A⌉₊ : ℝ) + 1) := by simp
    have hc : A ≤ ⌈A⌉₊ := Nat.le_ceil A
    rw [← hA]
    linarith

lemma find_q0 (hS : P.Standing) (h1 : ¬ IsEquilibrium P 1) :
    ∃ q0, 0 < q0 ∧ q0 < 1 ∧ T P q0 < 0 := by
  obtain ⟨M, hM1, hM2⟩ := claim hS h1
  have h01 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have ht : Tendsto (fun q => ∑ k ∈ Finset.range M, weight P q k * phi P q k) (𝓝[<] (1:ℝ))
      (𝓝 (∑ k ∈ Finset.range M, weight P 1 k * phi P 1 k)) :=
    tendsto_finset_sum _ fun k _ =>
      ((term_contAt hS h01 k).tendsto).mono_left nhdsWithin_le_nhds
  have ev1 := ht.eventually (eventually_lt_nhds hM2)
  have ev2 : ∀ᶠ q in 𝓝[<] (1:ℝ), q ∈ Ioo (0:ℝ) 1 := Ioo_mem_nhdsLT one_pos
  obtain ⟨q0, hF, hq0⟩ := (ev1.and ev2).exists
  refine ⟨q0, hq0.1, hq0.2, lt_of_le_of_lt ?_ hF⟩
  have hq : q0 ∈ Icc (0:ℝ) 1 := ⟨hq0.1.le, hq0.2.le⟩
  have hsum := (good_lt hS hq hq0.2).2.2 q0 hq0.1.le hq0.2
  unfold T
  rw [← hsum.sum_add_tsum_nat_add M]
  have : ∑' i, weight P q0 (i + M) * phi P q0 (i + M) ≤ 0 :=
    tsum_nonpos fun i => mul_nonpos_iff.2
      (Or.inl ⟨weight_nonneg hS hq _, phi_nonpos hq (hM1 _ (by omega))⟩)
  linarith

lemma exists_eq (hS : P.Standing) : ∃ q, IsEquilibrium P q := by
  by_cases h1 : IsEquilibrium P 1
  · exact ⟨1, h1⟩
  obtain ⟨q0, h0, h01, hT0⟩ := find_q0 hS h1
  have hcont := T_contOn hS h01
  have hT0' : 0 < T P 0 := by rw [T_zero]; linarith [E0_gt hS]
  obtain ⟨q, hq, hTq⟩ := intermediate_value_Icc' h0.le hcont ⟨hT0.le, hT0'.le⟩
  have hqpos : 0 < q := by
    rcases eq_or_lt_of_le hq.1 with h | h
    · rw [← h] at hTq; linarith
    · exact h
  have hq1 : q < 1 := lt_of_le_of_lt hq.2 h01
  have hqI : q ∈ Icc (0:ℝ) 1 := ⟨hqpos.le, hq1.le⟩
  exact ⟨q, ⟨⟨hqI, (good_lt hS hqI hq1).1⟩, (consist_iff hS hqpos hq1).2 hTq,
    opt_of_T hS hqI hq1 hTq⟩⟩

lemma eq_class (hS : P.Standing) {q : ℝ} (h : IsEquilibrium P q) :
    q ∈ Icc (0:ℝ) 1 ∧ 0 < q ∧ Good P q ∧ (q < 1 → T P q = 0) := by
  have hq := h.1.1
  have hpos : 0 < q := by
    rcases eq_or_lt_of_le hq.1 with h0 | h0
    · exfalso; rw [← h0] at h; exact not_eq_zero hS h
    · exact h0
  have hG : Good P q := by
    rcases lt_or_eq_of_le hq.2 with h1 | h1
    · exact good_lt hS hq h1
    · subst h1
      have hs := h.1.2
      rw [show weight P 1 = fun k => rho P ^ k from funext weight_one] at hs
      have hn := summable_geometric_iff_norm_lt_one.1 hs
      rw [Real.norm_of_nonneg (rho_pos hS).le] at hn
      exact good_one hS hn
  exact ⟨hq, hpos, hG, fun h1 => (consist_iff hS hpos h1).1 h.2.1⟩

lemma no_lt (hS : P.Standing) {q1 q2 : ℝ} (h1 : IsEquilibrium P q1) (h2 : IsEquilibrium P q2)
    (h12 : q1 < q2) : False := by
  obtain ⟨hq1, hp1, hG1, hT1⟩ := eq_class hS h1
  obtain ⟨hq2, hp2, hG2, hT2⟩ := eq_class hS h2
  have hq11 : q1 < 1 := lt_of_lt_of_le h12 hq2.2
  have hneg := cross hS hp1 h12 hq2.2 hG2 (hT1 hq11)
  have hsl := slope hS hq2 hG2 h2.2.2 hp1.le hq11
  have := mul_neg_of_pos_of_neg (sub_pos.2 h12) hneg
  linarith

end OQ03bae388

open OpaqueQueue.Equilibrium in
theorem solution (P : Params) (hS : P.Standing) : ∃! q : ℝ, IsEquilibrium P q := by
  obtain ⟨q, hq⟩ := OQ03bae388.exists_eq hS
  refine ⟨q, hq, fun q' hq' => ?_⟩
  rcases lt_trichotomy q' q with h | h | h
  · exact (OQ03bae388.no_lt hS hq' hq h).elim
  · exact h
  · exact (OQ03bae388.no_lt hS hq hq' h).elim
