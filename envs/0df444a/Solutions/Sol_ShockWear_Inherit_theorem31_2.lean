-- Prove2me | solution 1 for ShockWear.Inherit.theorem31_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:56:31.938177+00:00
-- url     : https://prove2.me/submissions/4e227ca0-9acb-41a0-ad99-aa655a719925

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model



namespace ShockWear.Inherit

open ShockWear.CumDamage

lemma g21_pw_nonneg (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t) (k : ℕ) : 0 ≤ poisW lam t k := by
  unfold poisW
  have : 0 ≤ lam * t := mul_nonneg hlam ht
  positivity

lemma g21_pw_summable (lam t : ℝ) : Summable (fun k => poisW lam t k) := by
  unfold poisW
  have := (Real.summable_pow_div_factorial (lam * t)).mul_left (Real.exp (-(lam * t)))
  refine this.congr (fun k => ?_)
  ring

lemma g21_pw_add (lam t x : ℝ) (n : ℕ) :
    poisW lam (t + x) n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, poisW lam t p.1 * poisW lam x p.2 := by
  unfold poisW
  have h1 : (lam * (t + x)) = lam * t + lam * x := by ring
  rw [h1, (Commute.all (lam * t) (lam * x)).add_pow', Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  obtain ⟨i, j⟩ := p
  simp only at hp ⊢
  subst hp
  have hc : ((i + j).choose i : ℝ) * (i.factorial : ℝ) * (j.factorial : ℝ) = ((i + j).factorial : ℝ) := by
    have := Nat.add_choose_mul_factorial_mul_factorial i j
    rw [Nat.choose_symm_add]
    exact_mod_cast this
  have hi : (i.factorial : ℝ) ≠ 0 := by positivity
  have hj : (j.factorial : ℝ) ≠ 0 := by positivity
  have hij : ((i + j).factorial : ℝ) ≠ 0 := by positivity
  rw [neg_add, Real.exp_add]
  rw [nsmul_eq_mul]
  rw [← hc]
  have hch : ((i + j).choose i : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right i j)).ne'
  field_simp

/-- support of a cross-log-concave sequence is an interval -/
lemma g21_lc_pos (q : ℕ → ℝ) (hnn : ∀ k, 0 ≤ q k)
    (hpf : ∀ j k, j ≤ k → q (k + 1) * q j ≤ q (j + 1) * q k)
    (a c : ℕ) (ha : 0 < q a) (hc : 0 < q c) : ∀ m, a ≤ m → m ≤ c → 0 < q m := by
  intro m ham hmc
  induction m, ham using Nat.le_induction with
  | base => exact ha
  | succ m hm ih =>
    have h := hpf m (c - 1) (by omega)
    have hc1 : c - 1 + 1 = c := by omega
    rw [hc1] at h
    have h0 : 0 < q c * q m := mul_pos hc (ih (by omega))
    have h2 : 0 < q (m + 1) * q (c - 1) := lt_of_lt_of_le h0 h
    rcases (hnn (m + 1)).lt_or_eq with h3 | h3
    · exact h3
    · rw [← h3] at h2; simp at h2

lemma g21_lc_gen (q : ℕ → ℝ) (hnn : ∀ k, 0 ≤ q k)
    (hpf : ∀ j k, j ≤ k → q (k + 1) * q j ≤ q (j + 1) * q k)
    (a b : ℕ) (hab : a ≤ b) (j : ℕ) : q (b + j) * q a ≤ q (a + j) * q b := by
  rcases (hnn a).lt_or_eq with ha | ha
  swap
  · rw [← ha]; simp only [mul_zero]; exact mul_nonneg (hnn _) (hnn _)
  rcases (hnn (b + j)).lt_or_eq with hb | hb
  swap
  · rw [← hb]; simp only [zero_mul]; exact mul_nonneg (hnn _) (hnn _)
  have hpos := g21_lc_pos q hnn hpf a (b + j) ha hb
  have key : ∀ i, i ≤ j → q (b + i) * q a ≤ q (a + i) * q b := by
    intro i
    induction i with
    | zero => intro _; simp [mul_comm]
    | succ i ih =>
      intro hi
      have IH := ih (by omega)
      have h1 := hpf (a + i) (b + i) (by omega)
      have pa : 0 < q (a + i) := hpos _ (by omega) (by omega)
      have pb : 0 < q (b + i) := hpos _ (by omega) (by omega)
      have e1 : b + (i + 1) = b + i + 1 := by omega
      have e2 : a + (i + 1) = a + i + 1 := by omega
      rw [e1, e2]
      have hm := mul_le_mul h1 IH (mul_nonneg (hnn _) (hnn _)) (mul_nonneg (hnn _) (hnn _))
      have hp : 0 < q (a + i) * q (b + i) := mul_pos pa pb
      have h3 : (q (b + i + 1) * q a) * (q (a + i) * q (b + i))
          ≤ (q (a + i + 1) * q b) * (q (a + i) * q (b + i)) := by linear_combination hm
      exact le_of_mul_le_mul_right h3 hp
  exact key j le_rfl

lemma g21_pow_cross (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (a b : ℕ) (hab : a ≤ b) :
    v ^ a * u ^ b ≤ u ^ a * v ^ b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, pow_add]
  have hv : 0 ≤ v := hu.trans huv
  have h1 : u ^ d ≤ v ^ d := pow_le_pow_left₀ hu huv d
  have h2 : 0 ≤ v ^ a * u ^ a := by positivity
  calc v ^ a * (u ^ a * u ^ d) = (v ^ a * u ^ a) * u ^ d := by ring
    _ ≤ (v ^ a * u ^ a) * v ^ d := mul_le_mul_of_nonneg_left h1 h2
    _ = u ^ a * (v ^ a * v ^ d) := by ring

lemma g21_w_cross (lam s t : ℝ) (hlam : 0 ≤ lam) (hs : 0 ≤ s) (hst : s ≤ t) (a b : ℕ) (hab : a ≤ b) :
    poisW lam t a * poisW lam s b ≤ poisW lam s a * poisW lam t b := by
  unfold poisW
  have hc := g21_pow_cross (lam * s) (lam * t) (mul_nonneg hlam hs)
    (mul_le_mul_of_nonneg_left hst hlam) a b hab
  have hC : 0 ≤ Real.exp (-(lam * t)) * Real.exp (-(lam * s)) / ((a.factorial : ℝ) * (b.factorial : ℝ)) := by
    positivity
  calc Real.exp (-(lam * t)) * (lam * t) ^ a / (a.factorial : ℝ) *
        (Real.exp (-(lam * s)) * (lam * s) ^ b / (b.factorial : ℝ))
      = (Real.exp (-(lam * t)) * Real.exp (-(lam * s)) / ((a.factorial : ℝ) * (b.factorial : ℝ))) *
          ((lam * t) ^ a * (lam * s) ^ b) := by ring
    _ ≤ (Real.exp (-(lam * t)) * Real.exp (-(lam * s)) / ((a.factorial : ℝ) * (b.factorial : ℝ))) *
          ((lam * s) ^ a * (lam * t) ^ b) := mul_le_mul_of_nonneg_left hc hC
    _ = Real.exp (-(lam * s)) * (lam * s) ^ a / (a.factorial : ℝ) *
        (Real.exp (-(lam * t)) * (lam * t) ^ b / (b.factorial : ℝ)) := by ring

lemma g21_norm_summable {f : ℕ → ℝ} (hf : Summable f) : Summable (fun k => ‖f k‖) := by
  simpa only [Real.norm_eq_abs] using hf.abs

lemma g21_term_summable (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t) (r : ℕ → ℝ)
    (hr0 : ∀ k, 0 ≤ r k) (hr1 : ∀ k, r k ≤ 1) : Summable (fun k => r k * poisW lam t k) :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (hr0 k) (g21_pw_nonneg lam t hlam ht k))
    (fun k => by simpa using mul_le_mul_of_nonneg_right (hr1 k) (g21_pw_nonneg lam t hlam ht k))
    (g21_pw_summable lam t)

/-- The shifted series -/
noncomputable def g21H (lam : ℝ) (q : ℕ → ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  ∑' i, q (j + i) * poisW lam t i

lemma g21_symm_le (A B : ℕ × ℕ → ℝ) (hA : Summable A) (hB : Summable B)
    (hpt : ∀ z : ℕ × ℕ, A z + A z.swap ≤ B z + B z.swap) : ∑' z, A z ≤ ∑' z, B z := by
  have hAs : ∑' z, A z = ∑' z : ℕ × ℕ, A z.swap := ((Equiv.prodComm ℕ ℕ).tsum_eq A).symm
  have hBs : ∑' z, B z = ∑' z : ℕ × ℕ, B z.swap := ((Equiv.prodComm ℕ ℕ).tsum_eq B).symm
  have hA2 : ∑' z : ℕ × ℕ, (A z + A z.swap) = 2 * ∑' z, A z := by
    rw [hA.tsum_add hA.prod_symm, ← hAs]; ring
  have hB2 : ∑' z : ℕ × ℕ, (B z + B z.swap) = 2 * ∑' z, B z := by
    rw [hB.tsum_add hB.prod_symm, ← hBs]; ring
  have hle : ∑' z : ℕ × ℕ, (A z + A z.swap) ≤ ∑' z : ℕ × ℕ, (B z + B z.swap) :=
    Summable.tsum_le_tsum hpt (hA.add hA.prod_symm) (hB.add hB.prod_symm)
  linarith

lemma g21_pt (lam : ℝ) (hlam : 0 ≤ lam) (q : ℕ → ℝ) (hnn : ∀ k, 0 ≤ q k)
    (hpf : ∀ j k, j ≤ k → q (k + 1) * q j ≤ q (j + 1) * q k)
    (j : ℕ) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (a b : ℕ) :
    q (j + a) * poisW lam t a * (q b * poisW lam s b) +
        q (j + b) * poisW lam t b * (q a * poisW lam s a) ≤
    q (j + a) * poisW lam s a * (q b * poisW lam t b) +
        q (j + b) * poisW lam s b * (q a * poisW lam t a) := by
  have hid : (q (j + a) * poisW lam s a * (q b * poisW lam t b) +
      q (j + b) * poisW lam s b * (q a * poisW lam t a)) -
      (q (j + a) * poisW lam t a * (q b * poisW lam s b) +
      q (j + b) * poisW lam t b * (q a * poisW lam s a)) =
      (q (j + a) * q b - q (j + b) * q a) *
        (poisW lam s a * poisW lam t b - poisW lam t a * poisW lam s b) := by ring
  have hprod : 0 ≤ (q (j + a) * q b - q (j + b) * q a) *
        (poisW lam s a * poisW lam t b - poisW lam t a * poisW lam s b) := by
    rcases le_total a b with hab | hab
    · have h1 := g21_lc_gen q hnn hpf a b hab j
      have h2 := g21_w_cross lam s t hlam hs hst a b hab
      rw [add_comm b j, add_comm a j] at h1
      exact mul_nonneg (by linarith) (by linarith)
    · have h1 := g21_lc_gen q hnn hpf b a hab j
      have h2 := g21_w_cross lam s t hlam hs hst b a hab
      rw [add_comm b j, add_comm a j] at h1
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  linarith

lemma g21_H_cross (lam : ℝ) (hlam : 0 ≤ lam) (q : ℕ → ℝ) (hnn : ∀ k, 0 ≤ q k)
    (hq1 : ∀ k, q k ≤ 1)
    (hpf : ∀ j k, j ≤ k → q (k + 1) * q j ≤ q (j + 1) * q k)
    (j : ℕ) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    g21H lam q j t * (∑' b, q b * poisW lam s b) ≤ g21H lam q j s * (∑' b, q b * poisW lam t b) := by
  have ht : 0 ≤ t := hs.trans hst
  unfold g21H
  have hr0 : ∀ k, 0 ≤ q (j + k) := fun k => hnn _
  have hr1 : ∀ k, q (j + k) ≤ 1 := fun k => hq1 _
  have sf1 := g21_term_summable lam t hlam ht (fun k => q (j + k)) hr0 hr1
  have sg1 := g21_term_summable lam s hlam hs _ hnn hq1
  have sf2 := g21_term_summable lam s hlam hs (fun k => q (j + k)) hr0 hr1
  have sg2 := g21_term_summable lam t hlam ht _ hnn hq1
  have e1 : (∑' i, q (j + i) * poisW lam t i) * (∑' b, q b * poisW lam s b) =
      ∑' z : ℕ × ℕ, (q (j + z.1) * poisW lam t z.1) * (q z.2 * poisW lam s z.2) :=
    tsum_mul_tsum_of_summable_norm (g21_norm_summable sf1) (g21_norm_summable sg1)
  have e2 : (∑' i, q (j + i) * poisW lam s i) * (∑' b, q b * poisW lam t b) =
      ∑' z : ℕ × ℕ, (q (j + z.1) * poisW lam s z.1) * (q z.2 * poisW lam t z.2) :=
    tsum_mul_tsum_of_summable_norm (g21_norm_summable sf2) (g21_norm_summable sg2)
  have m1 : Summable (fun z : ℕ × ℕ => (q (j + z.1) * poisW lam t z.1) * (q z.2 * poisW lam s z.2)) :=
    summable_mul_of_summable_norm (f := fun i => q (j + i) * poisW lam t i)
      (g := fun b => q b * poisW lam s b) (g21_norm_summable sf1) (g21_norm_summable sg1)
  have m2 : Summable (fun z : ℕ × ℕ => (q (j + z.1) * poisW lam s z.1) * (q z.2 * poisW lam t z.2)) :=
    summable_mul_of_summable_norm (f := fun i => q (j + i) * poisW lam s i)
      (g := fun b => q b * poisW lam t b) (g21_norm_summable sf2) (g21_norm_summable sg2)
  rw [e1, e2]
  refine g21_symm_le _ _ m1 m2 ?_
  rintro ⟨a, b⟩
  exact g21_pt lam hlam q hnn hpf j s t hs hst a b

lemma g21_shift (lam : ℝ) (hlam : 0 ≤ lam) (q : ℕ → ℝ) (hnn : ∀ k, 0 ≤ q k)
    (hq1 : ∀ k, q k ≤ 1) (x t : ℝ) (hx : 0 ≤ x) (ht : 0 ≤ t) :
    ∑' n, q n * poisW lam (x + t) n = ∑' j, poisW lam x j * g21H lam q j t := by
  set g : ℕ × ℕ → ℝ := fun p => q (p.1 + p.2) * (poisW lam x p.1 * poisW lam t p.2) with hg
  have hprodS : Summable (fun p : ℕ × ℕ => poisW lam x p.1 * poisW lam t p.2) :=
    summable_mul_of_summable_norm (g21_norm_summable (g21_pw_summable lam x))
      (g21_norm_summable (g21_pw_summable lam t))
  have hgS : Summable g := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hprodS
    · exact mul_nonneg (hnn _) (mul_nonneg (g21_pw_nonneg lam x hlam hx _) (g21_pw_nonneg lam t hlam ht _))
    · have := mul_nonneg (g21_pw_nonneg lam x hlam hx p.1) (g21_pw_nonneg lam t hlam ht p.2)
      simpa [hg] using mul_le_mul_of_nonneg_right (hq1 (p.1 + p.2)) this
  have h1 : ∑' n, q n * poisW lam (x + t) n =
      ∑' n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, g kl := by
    congr 1; ext n
    rw [g21_pw_add, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [hg, hp]
  have h2 : ∑' n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, g kl = ∑' p, g p := by
    conv_lhs => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
    rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq g]
    exact (((Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).summable_iff.mpr hgS).tsum_sigma'
      (fun n ↦ (hasSum_fintype _).summable)).symm
  rw [h1, h2, hgS.tsum_prod]
  congr 1; ext j
  unfold g21H
  rw [← tsum_mul_left]
  congr 1; ext i
  simp only [hg]; ring

lemma g21_H_le (lam : ℝ) (hlam : 0 ≤ lam) (q : ℕ → ℝ) (hnn : ∀ k, 0 ≤ q k)
    (hq1 : ∀ k, q k ≤ 1) (j : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ g21H lam q j t ∧ g21H lam q j t ≤ ∑' i, poisW lam t i := by
  unfold g21H
  constructor
  · exact tsum_nonneg (fun i => mul_nonneg (hnn _) (g21_pw_nonneg lam t hlam ht i))
  · refine Summable.tsum_le_tsum (fun i => ?_)
      (g21_term_summable lam t hlam ht _ (fun k => hnn _) (fun k => hq1 _)) (g21_pw_summable lam t)
    simpa using mul_le_mul_of_nonneg_right (hq1 (j + i)) (g21_pw_nonneg lam t hlam ht i)

/-- The core PF₂ inequality for a Poisson mixture of a cross-log-concave sequence. -/
theorem g21_core (lam : ℝ) (hlam : 0 ≤ lam) (q : ℕ → ℝ) (hnn : ∀ k, 0 ≤ q k)
    (hq1 : ∀ k, q k ≤ 1)
    (hpf : ∀ j k, j ≤ k → q (k + 1) * q j ≤ q (j + 1) * q k)
    (x s t : ℝ) (hx : 0 ≤ x) (hs : 0 ≤ s) (hst : s ≤ t) :
    (∑' n, q n * poisW lam (x + t) n) * (∑' n, q n * poisW lam s n) ≤
      (∑' n, q n * poisW lam (x + s) n) * (∑' n, q n * poisW lam t n) := by
  have ht : 0 ≤ t := hs.trans hst
  rw [g21_shift lam hlam q hnn hq1 x t hx ht, g21_shift lam hlam q hnn hq1 x s hx hs,
    ← tsum_mul_right, ← tsum_mul_right]
  set S := ∑' n, q n * poisW lam s n
  set T := ∑' n, q n * poisW lam t n
  have hS0 : 0 ≤ S := tsum_nonneg (fun i => mul_nonneg (hnn _) (g21_pw_nonneg lam s hlam hs i))
  have hT0 : 0 ≤ T := tsum_nonneg (fun i => mul_nonneg (hnn _) (g21_pw_nonneg lam t hlam ht i))
  have sumL : Summable (fun j => poisW lam x j * g21H lam q j t * S) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
      (((g21_pw_summable lam x).mul_right (∑' i, poisW lam t i)).mul_right S)
    · exact mul_nonneg (mul_nonneg (g21_pw_nonneg lam x hlam hx j)
        (g21_H_le lam hlam q hnn hq1 j t ht).1) hS0
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (g21_H_le lam hlam q hnn hq1 j t ht).2 (g21_pw_nonneg lam x hlam hx j)) hS0
  have sumR : Summable (fun j => poisW lam x j * g21H lam q j s * T) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
      (((g21_pw_summable lam x).mul_right (∑' i, poisW lam s i)).mul_right T)
    · exact mul_nonneg (mul_nonneg (g21_pw_nonneg lam x hlam hx j)
        (g21_H_le lam hlam q hnn hq1 j s hs).1) hT0
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (g21_H_le lam hlam q hnn hq1 j s hs).2 (g21_pw_nonneg lam x hlam hx j)) hT0
  refine Summable.tsum_le_tsum (fun j => ?_) sumL sumR
  have := g21_H_cross lam hlam q hnn hq1 hpf j s t hs hst
  have hw := g21_pw_nonneg lam x hlam hx j
  calc poisW lam x j * g21H lam q j t * S = poisW lam x j * (g21H lam q j t * S) := by ring
    _ ≤ poisW lam x j * (g21H lam q j s * T) := mul_le_mul_of_nonneg_left this hw
    _ = poisW lam x j * g21H lam q j s * T := by ring


theorem theorem31_2_core (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 = 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hpf : IsPF2SeqFrom 0 P) :
    IsIHR (ShockWear.CumDamage.shockSurv lam P) := by
  intro x hx s t hs hst
  have ht : 0 ≤ t := hs.trans hst
  have hP1 : ∀ k, P k ≤ 1 := fun k => hP0 ▸ hanti (Nat.zero_le k)
  have hpf' : ∀ j k, j ≤ k → P (k + 1) * P j ≤ P (j + 1) * P k :=
    fun j k hjk => hpf j k (Nat.zero_le j) hjk
  unfold shockSurv
  rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
  exact g21_core lam hlam.le P hnn hP1 hpf' x s t hx.le hs hst

theorem theorem31_1_core (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 = 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hpf : IsPF2SeqFrom 1 (failProb P)) :
    IsPF2Dens (shockDens lam P) := by
  intro x hx s t hs hst
  have hP1 : ∀ k, P k ≤ 1 := fun k => hP0 ▸ hanti (Nat.zero_le k)
  set q : ℕ → ℝ := fun k => failProb P (k + 1) with hq
  have hq0 : ∀ k, 0 ≤ q k := fun k => by
    simp only [hq, failProb]; linarith [hanti (Nat.le_succ k)]
  have hq1 : ∀ k, q k ≤ 1 := fun k => by
    simp only [hq, failProb]; linarith [hP1 k, hnn (k + 1)]
  have hpf' : ∀ j k, j ≤ k → q (k + 1) * q j ≤ q (j + 1) * q k :=
    fun j k hjk => hpf (j + 1) (k + 1) (by omega) (by omega)
  have key := g21_core lam hlam.le q hq0 hq1 hpf' x s t hx.le hs.le hst
  unfold shockDens
  have hl2 : 0 ≤ lam * lam := by positivity
  calc lam * (∑' k, failProb P (k + 1) * poisW lam (x + t) k) *
        (lam * ∑' k, failProb P (k + 1) * poisW lam s k)
      = (lam * lam) * ((∑' n, q n * poisW lam (x + t) n) * (∑' n, q n * poisW lam s n)) := by
        simp only [hq]; ring
    _ ≤ (lam * lam) * ((∑' n, q n * poisW lam (x + s) n) * (∑' n, q n * poisW lam t n)) :=
        mul_le_mul_of_nonneg_left key hl2
    _ = lam * (∑' k, failProb P (k + 1) * poisW lam (x + s) k) *
        (lam * ∑' k, failProb P (k + 1) * poisW lam t k) := by
        simp only [hq]; ring

end ShockWear.Inherit

open ShockWear.Inherit


theorem solution (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 = 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hpf : IsPF2SeqFrom 0 P) :
    IsIHR (ShockWear.CumDamage.shockSurv lam P) := by
  exact theorem31_2_core lam hlam P hP0 hanti hnn hpf
