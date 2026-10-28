-- Prove2me | solution 1 for RamanujanLostNotebook.PartII.entry_14_2_1_a
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T18:15:44.98098+00:00
-- url     : https://prove2.me/submissions/51c43bc3-cb64-4c7a-ac62-ca04571805d8

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch14_ch14LambertTerm
import Definitions.Def_RamanujanLostNotebook_PartII_ch14_ch14P
import Definitions.Def_RamanujanLostNotebook_PartII_ch14_ch14T
import Definitions.Def_RamanujanLostNotebook_PartII_ch14_ch14TTerm
import Definitions.Def_RamanujanLostNotebook_PartII_shared_eulerF
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPochInf
import Theorems.Thm_QseriesFormalization_PartI_Ch04_eulerPentagonalInfiniteProduct_eq_tsum_prime

namespace S99R1421

open RamanujanLostNotebook.PartII

/-- exponents -/
def ea (n : ℕ) : ℕ := (n + 1) * (3 * n + 2) / 2
def eb (n : ℕ) : ℕ := (n + 1) * (3 * n + 4) / 2

lemma two_ea (n : ℕ) : 2 * ea n = (n + 1) * (3 * n + 2) := by
  obtain ⟨k, hk⟩ : Even ((n + 1) * (3 * n + 2)) := by
    rw [show (n + 1) * (3 * n + 2) = 3 * (n * (n + 1)) + 2 * (n + 1) by ring]
    exact ((Nat.even_mul_succ_self n).mul_left 3).add (even_two_mul _)
  unfold ea; rw [hk]; omega

lemma two_eb (n : ℕ) : 2 * eb n = (n + 1) * (3 * n + 4) := by
  obtain ⟨k, hk⟩ : Even ((n + 1) * (3 * n + 4)) := by
    rw [show (n + 1) * (3 * n + 4) = 3 * (n * (n + 1)) + 4 * (n + 1) by ring]
    exact ((Nat.even_mul_succ_self n).mul_left 3).add
      ⟨2 * (n + 1), by ring⟩
  unfold eb; rw [hk]; omega

lemma ea_ge (n : ℕ) : n + 1 ≤ ea n := by
  have := two_ea n; nlinarith

lemma eb_ge (n : ℕ) : n + 1 ≤ eb n := by
  have := two_eb n; nlinarith

/-- paired pentagonal term -/
noncomputable def F (n : ℕ) (w : ℂ) : ℂ := (-1 : ℂ) ^ (n + 1) * (w ^ ea n + w ^ eb n)

lemma F_bound {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1) (n : ℕ) (w : ℂ) (hw : ‖w‖ ≤ ρ) :
    ‖F n w‖ ≤ 2 * ρ ^ (n + 1) := by
  unfold F
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have h1 : ‖w ^ ea n‖ ≤ ρ ^ (n + 1) := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hw _).trans (pow_le_pow_of_le_one hρ0 hρ (ea_ge n))
  have h2 : ‖w ^ eb n‖ ≤ ρ ^ (n + 1) := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hw _).trans (pow_le_pow_of_le_one hρ0 hρ (eb_ge n))
  linarith [norm_add_le (w ^ ea n) (w ^ eb n)]

lemma summable_F {q : ℂ} (hq : ‖q‖ < 1) : Summable (fun n => F n q) := by
  refine Summable.of_norm_bounded (g := fun n => 2 * ‖q‖ ^ (n + 1)) ?_ ?_
  · exact ((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_left _).comp_injective
      (add_left_injective 1) |>.congr (fun n => rfl)
  · intro n; exact F_bound (norm_nonneg _) hq.le n q le_rfl

lemma hasSum_deriv_F {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => deriv (F n) q) (deriv (fun w => ∑' n, F n w) q) := by
  set ρ : ℝ := (1 + ‖q‖) / 2
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by simp only [ρ]; linarith
  refine Complex.hasSum_deriv_of_summable_norm (U := Metric.ball 0 ρ) (u := fun n => 2 * ρ ^ (n + 1))
    ?_ (fun n => by unfold F; fun_prop) Metric.isOpen_ball ?_ ?_
  · exact ((summable_geometric_of_lt_one hρ0 hρ1).mul_left _).comp_injective
      (add_left_injective 1) |>.congr (fun n => rfl)
  · intro n w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact F_bound hρ0 hρ1.le n w hw.le
  · rw [Metric.mem_ball, dist_zero_right]; simp only [ρ]; linarith

lemma q_deriv_F (n : ℕ) (q : ℂ) :
    q * deriv (F n) q = (-1 : ℂ) ^ (n + 1) * ((ea n : ℂ) * q ^ ea n + (eb n : ℂ) * q ^ eb n) := by
  have hd : deriv (F n) q = (-1 : ℂ) ^ (n + 1) *
      ((ea n : ℂ) * q ^ (ea n - 1) + (eb n : ℂ) * q ^ (eb n - 1)) := by
    unfold F
    have : HasDerivAt (fun w : ℂ => (-1 : ℂ) ^ (n + 1) * (w ^ ea n + w ^ eb n))
        ((-1 : ℂ) ^ (n + 1) * ((ea n : ℂ) * q ^ (ea n - 1) + (eb n : ℂ) * q ^ (eb n - 1))) q :=
      ((hasDerivAt_pow (ea n) q).add (hasDerivAt_pow (eb n) q)).const_mul _
    exact this.deriv
  rw [hd]
  have ha : q * q ^ (ea n - 1) = q ^ ea n := by
    rw [← pow_succ']; congr 1; have := ea_ge n; omega
  have hb : q * q ^ (eb n - 1) = q ^ eb n := by
    rw [← pow_succ']; congr 1; have := eb_ge n; omega
  linear_combination ((-1 : ℂ) ^ (n + 1) * (ea n : ℂ)) * ha + ((-1 : ℂ) ^ (n + 1) * (eb n : ℂ)) * hb

lemma TTerm_eq (n : ℕ) (q : ℂ) :
    ch14TTerm 1 q n = F n q + 24 * (q * deriv (F n) q) := by
  rw [q_deriv_F]
  unfold ch14TTerm F
  have e1 : (n + 1) * (3 * (n + 1) - 1) / 2 = ea n := by
    unfold ea; congr 2
  have e2 : (n + 1) * (3 * (n + 1) + 1) / 2 = eb n := by
    unfold eb; congr 1
  have c1 : ((6 * (n + 1) - 1 : ℕ) : ℂ) = 6 * n + 5 := by
    rw [show 6 * (n + 1) - 1 = 6 * n + 5 by omega]; push_cast; ring
  have c2 : ((6 * (n + 1) + 1 : ℕ) : ℂ) = 6 * n + 7 := by push_cast; ring
  have a2 : (2 : ℂ) * ea n = (n + 1) * (3 * n + 2) := by exact_mod_cast two_ea n
  have b2 : (2 : ℂ) * eb n = (n + 1) * (3 * n + 4) := by exact_mod_cast two_eb n
  simp only [e1, e2, c1, c2]
  linear_combination (-12 * (-1 : ℂ) ^ (n + 1) * q ^ ea n) * a2 +
    (-12 * (-1 : ℂ) ^ (n + 1) * q ^ eb n) * b2

/-- the product -/
noncomputable def P (w : ℂ) : ℂ := ∏' n : ℕ, (1 - w ^ (n + 1))

lemma P_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : P q ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -q ^ (n + 1)) ?_ ?_
  · simpa [P, sub_eq_add_neg] using h
  · intro i
    rw [← sub_eq_add_neg, sub_ne_zero]
    intro h1
    have : ‖q ^ (i + 1)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
    rw [← h1] at this; simp at this
  · simpa using (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hq)

lemma P_eq_G {q : ℂ} (hq : ‖q‖ < 1) : P q = 1 + ∑' n, F n q := by
  have h := QseriesFormalization.PartI.Ch04.eulerPentagonalInfiniteProduct_eq_tsum_prime q hq
  have hP : QseriesFormalization.PartI.Ch04.eulerPentagonalInfiniteProduct q = P q := rfl
  rw [hP] at h
  set f : ℤ → ℂ := fun j => (-1 : ℂ) ^ j * q ^ (j * (3 * j + 1) / 2) with hf
  have hs : Summable f := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at h
    exact P_ne_zero hq h
  have h1 := hs.hasSum.nat_add_neg
  have h2 := (hasSum_nat_add_iff' 1).mpr h1
  rw [← h] at h2
  have hf0 : f 0 = 1 := by simp [hf]
  have hterm : ∀ n : ℕ, f ((n + 1 : ℕ) : ℤ) + f (-((n + 1 : ℕ) : ℤ)) = F n q := by
    intro n
    simp only [hf, F]
    have x1 : ((n + 1 : ℕ) : ℤ) * (3 * ((n + 1 : ℕ) : ℤ) + 1) / 2 = ((eb n : ℕ) : ℤ) := by
      unfold eb; push_cast; congr 1
    have x2 : (-((n + 1 : ℕ) : ℤ)) * (3 * (-((n + 1 : ℕ) : ℤ)) + 1) / 2 = ((ea n : ℕ) : ℤ) := by
      unfold ea; push_cast; congr 1
    rw [x1, x2, zpow_natCast, zpow_natCast, zpow_neg, zpow_natCast]
    have : ((-1 : ℂ) ^ (n + 1))⁻¹ = (-1 : ℂ) ^ (n + 1) := by
      rw [← inv_pow, inv_neg, inv_one]
    rw [this]; simp only [zpow_natCast]; ring
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, neg_zero, hf0] at h2
  simp only [hterm] at h2
  rw [h2.tsum_eq]; ring

lemma logDeriv_term (i : ℕ) (q : ℂ) :
    q * logDeriv (fun x : ℂ => 1 - x ^ (i + 1)) q = -ch14LambertTerm 1 q i := by
  rw [logDeriv_apply]
  have : deriv (fun x : ℂ => 1 - x ^ (i + 1)) q = -(((i + 1 : ℕ) : ℂ) * q ^ i) := by
    have := ((hasDerivAt_pow (i + 1) q).const_sub 1)
    simpa using this.deriv
  rw [this]
  unfold ch14LambertTerm
  rw [pow_succ q i]
  ring

lemma q_deriv_P {q : ℂ} (hq : ‖q‖ < 1) :
    q * deriv P q = -(P q * ∑' n, ch14LambertTerm 1 q n) := by
  have hball : q ∈ Metric.ball (0 : ℂ) 1 := by simpa using hq
  have hne : ∀ i : ℕ, 1 - q ^ (i + 1) ≠ 0 := by
    intro i h1
    rw [sub_eq_zero] at h1
    have : ‖q ^ (i + 1)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
    rw [← h1] at this; simp at this
  have hsumL : Summable (fun n => ch14LambertTerm 1 q n) := by
    have h0 := summable_norm_pow_mul_geometric_div_one_sub (𝕜 := ℂ) 1 hq
    have := (summable_nat_add_iff 1).mpr h0
    refine this.congr (fun n => ?_)
    simp only [ch14LambertTerm]
  have hm : Summable fun i : ℕ => logDeriv (fun x : ℂ => 1 - x ^ (i + 1)) q := by
    by_cases hq0 : q = 0
    · subst hq0
      refine summable_of_ne_finset_zero (s := {0}) (fun i hi => ?_)
      have hi' : i ≠ 0 := by simpa using hi
      rw [logDeriv_apply]
      have : deriv (fun x : ℂ => 1 - x ^ (i + 1)) 0 = -(((i + 1 : ℕ) : ℂ) * 0 ^ i) := by
        have := ((hasDerivAt_pow (i + 1) (0 : ℂ)).const_sub 1)
        simpa using this.deriv
      rw [this, zero_pow hi']; simp
    · have := (hsumL.neg).mul_left q⁻¹
      refine this.congr (fun i => ?_)
      rw [← logDeriv_term i q, ← mul_assoc, inv_mul_cancel₀ hq0, one_mul]
  have hlog := logDeriv_tprod_eq_tsum Metric.isOpen_ball hball
    (f := fun i x => 1 - x ^ (i + 1)) hne (fun i => by fun_prop) hm
    ModularForm.multipliableLocallyUniformlyOn_one_sub_pow (P_ne_zero hq)
  have hPq := P_ne_zero hq
  have hd : deriv P q = P q * logDeriv P q := by
    rw [logDeriv_apply]; field_simp
  rw [hd]
  change q * (P q * logDeriv (fun x => ∏' i, (1 - x ^ (i + 1))) q) = _
  rw [hlog, mul_left_comm, ← tsum_mul_left]
  simp only [logDeriv_term, tsum_neg]
  ring

lemma main {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (ch14TTerm 1 q) ∧ ch14T 1 q = P q * ch14P q := by
  have hF := summable_F hq
  have hD := hasSum_deriv_F hq
  have hS2 : Summable (fun n => 24 * (q * deriv (F n) q)) :=
    (hD.summable.mul_left q).mul_left 24
  have hfun : ch14TTerm 1 q = fun n => F n q + 24 * (q * deriv (F n) q) :=
    funext (fun n => TTerm_eq n q)
  refine ⟨hfun ▸ hF.add hS2, ?_⟩
  have hev : P =ᶠ[nhds q] (fun w => 1 + ∑' n, F n w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show q ∈ Metric.ball (0 : ℂ) 1 by simpa using hq)]
      with w hw
    exact P_eq_G (by simpa using hw)
  have hderiv : deriv P q = ∑' n, deriv (F n) q := by
    rw [hev.deriv_eq, deriv_const_add, hD.tsum_eq]
  have key := q_deriv_P hq
  rw [hderiv] at key
  unfold ch14T ch14P
  rw [hfun, hF.tsum_add hS2, tsum_mul_left, tsum_mul_left, key, P_eq_G hq]
  ring

end S99R1421

theorem solution (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (RamanujanLostNotebook.PartII.ch14TTerm 1 q) ∧
      RamanujanLostNotebook.PartII.eulerF q ≠ 0 ∧
      RamanujanLostNotebook.PartII.ch14T 1 q / RamanujanLostNotebook.PartII.eulerF q =
        RamanujanLostNotebook.PartII.ch14P q := by
  have hE : RamanujanLostNotebook.PartII.eulerF q = S99R1421.P q := by
    unfold RamanujanLostNotebook.PartII.eulerF RamanujanLostNotebook.PartII.qPochInf S99R1421.P
    congr 1; ext k; rw [pow_succ']
  obtain ⟨h1, h2⟩ := S99R1421.main hq
  have hne := S99R1421.P_ne_zero hq
  refine ⟨h1, hE ▸ hne, ?_⟩
  rw [hE, h2]; field_simp
