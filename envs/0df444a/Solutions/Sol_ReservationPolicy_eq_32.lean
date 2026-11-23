-- Prove2me | solution 1 for ReservationPolicy.eq_32
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T01:27:56.21664+00:00
-- url     : https://prove2.me/submissions/2d7af092-c2de-4ccc-8596-7df6235e51b7

import Mathlib
import Definitions.Def_ReservationPolicy_Params_Valid
import Definitions.Def_ReservationPolicy_IsInvestCandidate
import Definitions.Def_ReservationPolicy_InvestOptimal
import Definitions.Def_ReservationPolicy_Params_kappaStar
import Definitions.Def_ReservationPolicy_Params_dStar

set_option autoImplicit false

open MeasureTheory ReservationPolicy

namespace ReservationPolicy.Eq11Proof

theorem set_eq (m d : ℝ) : {ε : ℝ | d < m + ε} = Set.Ioi (d - m) := by
  ext ε; simp only [Set.mem_setOf_eq, Set.mem_Ioi]; constructor <;> intro h <;> linarith

theorem admitProb_formula (m d : ℝ) :
    admitProb m d = (1 / 2) * (volume (Set.Ioi (d - m) ∩ Set.Icc (-1 : ℝ) 1)).toReal := by
  unfold admitProb noise
  rw [set_eq, Measure.real, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioi,
    smul_eq_mul, ENNReal.toReal_mul]
  norm_num

theorem admitProb_eq (m d : ℝ) (h1 : d - m < 1) (h2 : -1 < d - m) :
    admitProb m d = (1 + m - d) / 2 := by
  rw [admitProb_formula]
  have : Set.Ioi (d - m) ∩ Set.Icc (-1 : ℝ) 1 = Set.Ioc (d - m) 1 := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨h, -, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨h, by linarith, h'⟩
  rw [this, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  ring

theorem admitProb_range (m d : ℝ) (h0 : 0 < admitProb m d) (h1 : admitProb m d < 1) :
    d - m < 1 ∧ -1 < d - m := by
  rw [admitProb_formula] at h0 h1
  constructor
  · by_contra hc
    push Not at hc
    have : Set.Ioi (d - m) ∩ Set.Icc (-1 : ℝ) 1 = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h _; linarith
    rw [this] at h0
    simp at h0
  · by_contra hc
    push Not at hc
    have hsub : Set.Ioc (-1 : ℝ) 1 ⊆ Set.Ioi (d - m) ∩ Set.Icc (-1 : ℝ) 1 := by
      intro x hx
      exact ⟨by simp only [Set.mem_Ioi]; linarith [hx.1], le_of_lt hx.1, hx.2⟩
    have hsup : Set.Ioi (d - m) ∩ Set.Icc (-1 : ℝ) 1 ⊆ Set.Icc (-1 : ℝ) 1 := Set.inter_subset_right
    have e1 := measure_mono (μ := volume) hsub
    have e2 := measure_mono (μ := volume) hsup
    rw [Real.volume_Ioc] at e1
    rw [Real.volume_Icc] at e2
    have hfin : volume (Set.Ioi (d - m) ∩ Set.Icc (-1 : ℝ) 1) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top e2
    have e3 := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).mpr e1
    rw [ENNReal.toReal_ofReal (by norm_num)] at e3
    norm_num at e3
    linarith

theorem admittedMean_eq (m d : ℝ) (h1 : d - m < 1) (h2 : -1 < d - m) :
    admittedMean m d = (m + d + 1) / 2 := by
  unfold admittedMean
  rw [admitProb_eq m d h1 h2, set_eq]
  unfold noise
  rw [Measure.restrict_smul, integral_smul_measure, Measure.restrict_restrict measurableSet_Ioi]
  have : Set.Ioi (d - m) ∩ Set.Icc (-1 : ℝ) 1 = Set.Ioc (d - m) 1 := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨h, -, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨h, by linarith, h'⟩
  rw [this, ← intervalIntegral.integral_of_le (by linarith)]
  rw [intervalIntegral.integral_add intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    intervalIntegral.integral_const, integral_id]
  have hne : (1 + m - d) ≠ 0 := by linarith
  simp only [smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  field_simp
  ring

theorem generic (k s d C : ℝ) (hk : 1 / 4 < k) (hs0 : 0 < s) (hs1 : s ≤ 1) (m : ℝ → ℝ)
    (hm : ∀ e, m e = s * e) (pay : ℝ → ℝ → ℝ)
    (hpay : ∀ r e, pay r e = admitProb (m e) d * r - k * e ^ 2 - C)
    (S : Set ℝ) (hS : ∀ e, e ∈ S ↔ 0 ≤ e ∧ 0 < admitProb (m e) d ∧ admitProb (m e) d < 1)
    (e r : ℝ) :
    (e ∈ S ∧ (∀ e' ∈ S, pay r e' ≤ pay r e) ∧ r = admittedMean (m e) d) ↔
      (e ∈ S ∧ e = (1 + d) * s / (8 * k - s ^ 2) ∧ r = (1 + d + s * e) / 2) := by
  have hkpos : 0 < k := by linarith
  have hden : 0 < 8 * k - s ^ 2 := by nlinarith
  have hS' : ∀ e, e ∈ S ↔ 0 ≤ e ∧ d - s * e < 1 ∧ -1 < d - s * e := by
    intro e
    rw [hS, hm]
    constructor
    · rintro ⟨h0, h1, h2⟩
      exact ⟨h0, admitProb_range _ _ h1 h2⟩
    · rintro ⟨h0, h1, h2⟩
      rw [admitProb_eq _ _ h1 h2]
      exact ⟨h0, by linarith, by linarith⟩
  have hpayS : ∀ r e, e ∈ S → pay r e = (1 + s * e - d) / 2 * r - k * e ^ 2 - C := by
    intro r e he
    obtain ⟨_, h1, h2⟩ := (hS' e).mp he
    rw [hpay, hm, admitProb_eq _ _ h1 h2]
  constructor
  · rintro ⟨he, hopt, hr⟩
    obtain ⟨he0, h1, h2⟩ := (hS' e).mp he
    rw [hm, admittedMean_eq _ _ h1 h2] at hr
    have hse : 0 ≤ s * e := mul_nonneg hs0.le he0
    have hrpos : 0 < r := by rw [hr]; linarith
    have hstat : e = s * r / (4 * k) := by
      by_contra hne
      set δ := s * r / (4 * k) - e with hδ
      have hδne : δ ≠ 0 := by intro h; apply hne; linarith
      set η := min (1 - (d - s * e)) (d - s * e + 1) with hη
      have hηpos : 0 < η := lt_min (by linarith) (by linarith)
      have hη1 : η ≤ 1 - (d - s * e) := min_le_left _ _
      have hη2 : η ≤ d - s * e + 1 := min_le_right _ _
      have hA : 0 ≤ s * |δ| := mul_nonneg hs0.le (abs_nonneg δ)
      set t := min 1 (η / (2 * (s * |δ| + 1))) with ht
      have ht0 : 0 < t := lt_min one_pos (div_pos hηpos (by positivity))
      have ht1 : t ≤ 1 := min_le_left _ _
      have ht2 : t ≤ η / (2 * (s * |δ| + 1)) := min_le_right _ _
      have htη : t * (s * |δ|) < η := by
        have e1 : t * (s * |δ|) ≤ η / (2 * (s * |δ| + 1)) * (s * |δ|) :=
          mul_le_mul_of_nonneg_right ht2 hA
        have e2 : η / (2 * (s * |δ| + 1)) * (s * |δ|) < η := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
        linarith
      have hb : |s * (t * δ)| < η := by
        rw [abs_mul, abs_mul, abs_of_pos hs0, abs_of_pos ht0]
        nlinarith
      obtain ⟨hb1, hb2⟩ := abs_lt.mp hb
      have hmem : e + t * δ ∈ S := by
        rw [hS']
        refine ⟨?_, ?_, ?_⟩
        · have hsplit : e + t * δ = (1 - t) * e + t * (s * r / (4 * k)) := by rw [hδ]; ring
          rw [hsplit]
          apply add_nonneg
          · exact mul_nonneg (by linarith) he0
          · exact mul_nonneg ht0.le (by positivity)
        · nlinarith
        · nlinarith
      have hgain := hopt _ hmem
      rw [hpayS r _ hmem, hpayS r e he] at hgain
      have hdiff : (1 + s * (e + t * δ) - d) / 2 * r - k * (e + t * δ) ^ 2 - C -
          ((1 + s * e - d) / 2 * r - k * e ^ 2 - C) = k * t * δ ^ 2 * (2 - t) := by
        rw [hδ]
        field_simp
        ring
      have h2t : 0 < 2 - t := by linarith
      have hδ2 : 0 < δ ^ 2 := by positivity
      have hpos : 0 < k * t * δ ^ 2 * (2 - t) := by positivity
      linarith
    refine ⟨he, ?_, by rw [hr]; ring⟩
    have h4 : 4 * k * e = s * r := by rw [hstat]; field_simp
    have hr2 : 2 * r = s * e + d + 1 := by rw [hr]; ring
    rw [eq_div_iff hden.ne']
    linear_combination 2 * h4 + s * hr2
  · rintro ⟨he, he1, hr⟩
    obtain ⟨he0, h1, h2⟩ := (hS' e).mp he
    refine ⟨he, fun e' he' => ?_, by rw [hm, admittedMean_eq _ _ h1 h2, hr]; ring⟩
    rw [hpayS r e' he', hpayS r e he]
    have hkey : s * r = 4 * k * e := by
      rw [hr]
      have : e * (8 * k - s ^ 2) = (1 + d) * s := by rw [he1]; field_simp
      linear_combination (s / 2) * 0 + (-1 / 2) * this
    have hsq : (1 + s * e - d) / 2 * r - k * e ^ 2 - C -
        ((1 + s * e' - d) / 2 * r - k * e' ^ 2 - C) = k * (e' - e) ^ 2 := by
      linear_combination ((e - e') / 2) * hkey
    have : 0 ≤ k * (e' - e) ^ 2 := by positivity
    linarith

end ReservationPolicy.Eq11Proof

open ReservationPolicy.Eq11Proof in
theorem ReservationPolicy.Eq11Proof.eq11 (P : Params) (hP : P.Valid) (d : ℝ) :
    (∀ e r, InvestGroup P e d r ↔
      e ∈ investEfforts d ∧ e = (1 + d) / (8 * P.k - 1) ∧ r = (1 + d + e) / 2) ∧
    (∀ e r, PlainGroup P e d r ↔
      e ∈ plainEfforts P d ∧ e = (1 + d) * P.ϕ / (8 * P.k - P.ϕ ^ 2) ∧
        r = (1 + d + P.ϕ * e) / 2) := by
  obtain ⟨hk, hϕ0, hϕ1, -⟩ := hP
  constructor
  · intro e r
    have G := generic P.k 1 d P.κ hk one_pos le_rfl (fun e => e) (fun e => (one_mul e).symm)
      (fun r e => payoffInvest P d r e) (fun r e => rfl) (investEfforts d) (fun e => Iff.rfl) e r
    simp only [one_mul, mul_one, one_pow] at G
    exact G
  · intro e r
    have G := generic P.k P.ϕ d 0 hk hϕ0 hϕ1.le (fun e => P.ϕ * e) (fun e => rfl)
      (fun r e => payoffPlain P d r e) (fun r e => by simp [payoffPlain]) (plainEfforts P d)
      (fun e => Iff.rfl) e r
    beta_reduce at G
    exact G

open ReservationPolicy.Eq11Proof in
theorem ReservationPolicy.Eq11Proof.D_pos (P : Params) (hP : P.Valid) :
    0 < (8 * P.k - P.ϕ ^ 2) * (8 * P.k - 1 - P.α) - P.ϕ ^ 2 * (1 - P.α) * (8 * P.k - 1) := by
  obtain ⟨hk, hϕ0, hϕ1, hα0, hα1, -⟩ := hP
  have e : (8 * P.k - P.ϕ ^ 2) * (8 * P.k - 1 - P.α) - P.ϕ ^ 2 * (1 - P.α) * (8 * P.k - 1) =
      (8 * P.k - 2) * (8 * P.k - P.ϕ ^ 2) + 8 * P.k * (1 - P.ϕ ^ 2) * (1 - P.α) := by ring
  rw [e]
  have h1 : 0 < 8 * P.k - 2 := by linarith
  have h2 : 0 < 8 * P.k - P.ϕ ^ 2 := by nlinarith
  have h3 : 0 < 1 - P.ϕ ^ 2 := by nlinarith
  have h4 : 0 < 1 - P.α := by linarith
  have h5 : 0 < 8 * P.k := by linarith
  positivity

open ReservationPolicy.Eq11Proof in
theorem ReservationPolicy.Eq11Proof.eq2627 (P : Params) (hP : P.Valid) (b : Benchmark) (hb : IsInvestCandidate P b) :
    b.d = P.dStar ∧
    b.ex = 2 * (1 - P.z) * (8 * P.k - P.ϕ ^ 2) /
      ((8 * P.k - P.ϕ ^ 2) * (8 * P.k - 1 - P.α) - P.ϕ ^ 2 * (1 - P.α) * (8 * P.k - 1)) ∧
    b.ey = 2 * (1 - P.z) * (8 * P.k - 1) * P.ϕ /
      ((8 * P.k - P.ϕ ^ 2) * (8 * P.k - 1 - P.α) - P.ϕ ^ 2 * (1 - P.α) * (8 * P.k - 1)) := by
  have hD := D_pos P hP
  have hP' := hP
  obtain ⟨hk, hϕ0, hϕ1, hα0, hα1, -⟩ := hP'
  obtain ⟨hI, hPl, hz⟩ := hb
  obtain ⟨hexS, hex, -⟩ := ((eq11 P hP b.d).1 b.ex b.rx).mp hI
  obtain ⟨heyS, hey, -⟩ := ((eq11 P hP b.d).2 b.ey b.ry).mp hPl
  obtain ⟨-, hx0, hx1⟩ := hexS
  obtain ⟨-, hy0, hy1⟩ := heyS
  obtain ⟨hxa, hxb⟩ := admitProb_range _ _ hx0 hx1
  obtain ⟨hya, hyb⟩ := admitProb_range _ _ hy0 hy1
  have hrx : b.rhoX = (1 + b.ex - b.d) / 2 := admitProb_eq _ _ hxa hxb
  have hry : b.rhoY P = (1 + P.ϕ * b.ey - b.d) / 2 := admitProb_eq _ _ hya hyb
  have ha : (0 : ℝ) < 8 * P.k - 1 := by linarith
  have hc : (0 : ℝ) < 8 * P.k - P.ϕ ^ 2 := by nlinarith
  have hz2 : 2 * P.z * (8 * P.k - 1) * (8 * P.k - P.ϕ ^ 2) =
      P.α * (8 * P.k - P.ϕ ^ 2) * ((8 * P.k - 1) + (1 + b.d) - (8 * P.k - 1) * b.d) +
      (1 - P.α) * (8 * P.k - 1) * ((8 * P.k - P.ϕ ^ 2) + P.ϕ ^ 2 * (1 + b.d) -
        (8 * P.k - P.ϕ ^ 2) * b.d) := by
    rw [hz, hrx, hry, hex, hey]
    field_simp
  have hd : b.d = P.dStar := by
    unfold Params.dStar
    rw [eq_div_iff hD.ne']
    linear_combination hz2
  have haN := ha.ne'
  have hcN := hc.ne'
  have hDN := hD.ne'
  refine ⟨hd, ?_, ?_⟩
  · rw [hex, hd]
    unfold Params.dStar
    set D := (8 * P.k - P.ϕ ^ 2) * (8 * P.k - 1 - P.α) - P.ϕ ^ 2 * (1 - P.α) * (8 * P.k - 1)
      with hDdef
    rw [div_eq_div_iff haN hDN, add_mul, div_mul_cancel₀ _ hDN, one_mul, hDdef]
    ring
  · rw [hey, hd]
    unfold Params.dStar
    set D := (8 * P.k - P.ϕ ^ 2) * (8 * P.k - 1 - P.α) - P.ϕ ^ 2 * (1 - P.α) * (8 * P.k - 1)
      with hDdef
    set Nn := (8 * P.k - P.ϕ ^ 2) * ((8 * P.k - 1) * (1 - 2 * P.z) + P.α) +
      P.ϕ ^ 2 * (1 - P.α) * (8 * P.k - 1) with hNdef
    rw [div_eq_div_iff hcN hDN,
      show (1 + Nn / D) * P.ϕ * D = P.ϕ * ((1 + Nn / D) * D) by ring,
      add_mul, div_mul_cancel₀ _ hDN, one_mul, hDdef, hNdef]
    ring

open ReservationPolicy.Eq11Proof in
theorem ReservationPolicy.Eq11Proof.cand_rho (P : Params) (hP : P.Valid) (b : Benchmark)
    (hb : IsInvestCandidate P b) :
    b.rhoX = (1 + b.ex - b.d) / 2 ∧ b.rhoY P = (1 + P.ϕ * b.ey - b.d) / 2 := by
  obtain ⟨hI, hPl, -⟩ := hb
  obtain ⟨⟨-, hx0, hx1⟩, -, -⟩ := ((eq11 P hP b.d).1 b.ex b.rx).mp hI
  obtain ⟨⟨-, hy0, hy1⟩, -, -⟩ := ((eq11 P hP b.d).2 b.ey b.ry).mp hPl
  obtain ⟨hxa, hxb⟩ := admitProb_range _ _ hx0 hx1
  obtain ⟨hya, hyb⟩ := admitProb_range _ _ hy0 hy1
  exact ⟨admitProb_eq _ _ hxa hxb, admitProb_eq _ _ hya hyb⟩

open ReservationPolicy.Eq11Proof in
theorem solution (P : Params) (hP : P.Valid) (b : Benchmark) (hb : IsInvestCandidate P b) :
    (P.κ ≤ P.kappaStar → InvestOptimal P b.d b.rx b.ex) ∧
    (P.ϕ * b.rx / (4 * P.k) ∈ plainEfforts P b.d →
      InvestOptimal P b.d b.rx b.ex → P.κ ≤ P.kappaStar) ∧
    (b.d < 1 → P.ϕ * b.rx / (4 * P.k) ∈ plainEfforts P b.d) := by
  have hD := D_pos P hP
  have hP' := hP
  obtain ⟨hk, hϕ0, hϕ1, hα0, hα1, -, -, -⟩ := hP'
  obtain ⟨hd, hex2, -⟩ := eq2627 P hP b hb
  obtain ⟨hI, -, -⟩ := hb
  obtain ⟨⟨hex0, hx0, hx1⟩, hex, hrx⟩ := ((eq11 P hP b.d).1 b.ex b.rx).mp hI
  obtain ⟨hxa, hxb⟩ := admitProb_range _ _ hx0 hx1
  have ha : (0 : ℝ) < 8 * P.k - 1 := by linarith
  have hkpos : (0 : ℝ) < P.k := by linarith
  have hrx4 : b.rx = 4 * P.k * b.ex := by
    rw [hrx, hex]
    field_simp
    ring
  have hestar : P.ϕ * b.rx / (4 * P.k) = P.ϕ * b.ex := by
    rw [hrx4]
    field_simp
  have hκstar : P.kappaStar = (1 - P.ϕ ^ 2) * b.rx ^ 2 / (16 * P.k) := by
    rw [hrx4, hex2]
    unfold Params.kappaStar
    set D'' := P.ϕ ^ 2 + 4 * P.k * (8 * P.k - 1 - P.α - (2 - P.α) * P.ϕ ^ 2) with hD''
    have hDD : (8 * P.k - P.ϕ ^ 2) * (8 * P.k - 1 - P.α) - P.ϕ ^ 2 * (1 - P.α) * (8 * P.k - 1) =
        2 * D'' := by rw [hD'']; ring
    have hD''N : D'' ≠ 0 := by intro h; rw [h] at hDD; linarith
    rw [hDD]
    field_simp
    ring
  have hinv : payoffInvest P b.d b.rx b.ex =
      (1 - b.d) * b.rx / 2 + b.rx ^ 2 / (16 * P.k) - P.κ := by
    unfold payoffInvest
    rw [admitProb_eq _ _ hxa hxb, hrx4]
    field_simp
    ring
  have hplain : ∀ e' ∈ plainEfforts P b.d, payoffPlain P b.d b.rx e' =
      (1 - b.d) * b.rx / 2 + P.ϕ ^ 2 * b.rx ^ 2 / (16 * P.k) -
        P.k * (e' - P.ϕ * b.rx / (4 * P.k)) ^ 2 := by
    intro e' he'
    obtain ⟨-, h0, h1⟩ := he'
    obtain ⟨ha', hb'⟩ := admitProb_range _ _ h0 h1
    unfold payoffPlain
    rw [admitProb_eq _ _ ha' hb']
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro hκle e' he'
    rw [hplain e' he', hinv]
    rw [hκstar] at hκle
    have h1 : 0 ≤ P.k * (e' - P.ϕ * b.rx / (4 * P.k)) ^ 2 := by positivity
    have h2 : (1 - P.ϕ ^ 2) * b.rx ^ 2 / (16 * P.k) =
        b.rx ^ 2 / (16 * P.k) - P.ϕ ^ 2 * b.rx ^ 2 / (16 * P.k) := by ring
    linarith
  · intro hmem hopt
    have h := hopt _ hmem
    rw [hplain _ hmem, hinv, sub_self] at h
    rw [hκstar]
    have h2 : (1 - P.ϕ ^ 2) * b.rx ^ 2 / (16 * P.k) =
        b.rx ^ 2 / (16 * P.k) - P.ϕ ^ 2 * b.rx ^ 2 / (16 * P.k) := by ring
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero] at h
    linarith
  · intro hd1
    rw [hestar]
    have hϕe : 0 ≤ P.ϕ * b.ex := mul_nonneg hϕ0.le hex0
    have hlt : P.ϕ * b.ex ≤ b.ex := by nlinarith
    have hr1 : b.d - P.ϕ * b.ex < 1 := by linarith
    have hr2 : -1 < b.d - P.ϕ * b.ex := by linarith
    refine ⟨hϕe, ?_, ?_⟩
    · have hr1' : b.d - P.ϕ * (P.ϕ * b.ex) < 1 := by nlinarith
      have hr2' : -1 < b.d - P.ϕ * (P.ϕ * b.ex) := by nlinarith
      rw [admitProb_eq _ _ hr1' hr2']
      linarith
    · have hr1' : b.d - P.ϕ * (P.ϕ * b.ex) < 1 := by nlinarith
      have hr2' : -1 < b.d - P.ϕ * (P.ϕ * b.ex) := by nlinarith
      rw [admitProb_eq _ _ hr1' hr2']
      nlinarith
