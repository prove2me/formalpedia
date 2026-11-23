-- Prove2me | solution 1 for ReservationPolicy.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T01:07:24.889114+00:00
-- url     : https://prove2.me/submissions/d4678f32-3b22-4357-b0d2-58856aa703d5

import Mathlib
import Definitions.Def_ReservationPolicy_Params_Valid
import Definitions.Def_ReservationPolicy_IsInvestCandidate
import Definitions.Def_ReservationPolicy_IsPolicyEq
import Definitions.Def_ReservationPolicy_Params_dStar
import Definitions.Def_ReservationPolicy_Params_dX
import Definitions.Def_ReservationPolicy_Params_dY
import Definitions.Def_ReservationPolicy_welfare

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
theorem ReservationPolicy.Eq11Proof.eq5152 (P : Params) (hP : P.Valid) (b : Benchmark) (hb : IsInvestCandidate P b)
    (s : ℝ) (o : PolicyOutcome) (ho : IsPolicyEq P b s o) :
    o.dx = P.dX s ∧ o.dy = P.dY s := by
  have hP' := hP
  obtain ⟨hk, hϕ0, hϕ1, hα0, hα1, -⟩ := hP'
  obtain ⟨hd, -, -⟩ := eq2627 P hP b hb
  obtain ⟨hrxB, hryB⟩ := cand_rho P hP b hb
  obtain ⟨hIB, hPlB, -⟩ := hb
  obtain ⟨-, hexB, -⟩ := ((eq11 P hP b.d).1 b.ex b.rx).mp hIB
  obtain ⟨-, heyB, -⟩ := ((eq11 P hP b.d).2 b.ey b.ry).mp hPlB
  obtain ⟨hI, hPl, -, -, hsx, hsy⟩ := ho
  obtain ⟨⟨-, hx0, hx1⟩, hexO, -⟩ := ((eq11 P hP o.dx).1 o.ex o.rx).mp hI
  obtain ⟨⟨-, hy0, hy1⟩, heyO, -⟩ := ((eq11 P hP o.dy).2 o.ey o.ry).mp hPl
  obtain ⟨hxa, hxb⟩ := admitProb_range _ _ hx0 hx1
  obtain ⟨hya, hyb⟩ := admitProb_range _ _ hy0 hy1
  have hrxO : o.rhoX = (1 + o.ex - o.dx) / 2 := admitProb_eq _ _ hxa hxb
  have hryO : o.rhoY P = (1 + P.ϕ * o.ey - o.dy) / 2 := admitProb_eq _ _ hya hyb
  have ha : (8 * P.k - 1) ≠ 0 := by linarith
  have hc : (8 * P.k - P.ϕ ^ 2) ≠ 0 := by nlinarith
  have ha' : -1 + P.k * 8 ≠ 0 := by intro h; apply ha; linarith
  have hc' : -P.ϕ ^ 2 + P.k * 8 ≠ 0 := by intro h; apply hc; linarith
  have hc'' : P.k * 8 - P.ϕ ^ 2 ≠ 0 := by intro h; apply hc; linarith
  have h4a : 0 < 4 * P.k - 1 := by linarith
  have h4c : 0 < 4 * P.k - P.ϕ ^ 2 := by nlinarith
  have hkx : (o.dx - b.d) * (P.α * (4 * P.k - 1)) = s * (8 * P.k - 1) := by
    rw [← hsx, hrxB, hrxO, hexB, hexO]
    have hinv : (8 * P.k - 1) * (8 * P.k - 1)⁻¹ = 1 := mul_inv_cancel₀ ha
    linear_combination (P.α / 2 * (o.dx - b.d)) * hinv
  have hky : (b.d - o.dy) * ((1 - P.α) * (4 * P.k - P.ϕ ^ 2)) = s * (8 * P.k - P.ϕ ^ 2) := by
    rw [← hsy, hryB, hryO, heyB, heyO]
    field_simp
    ring
  have hnx : P.α * (4 * P.k - 1) ≠ 0 := (mul_pos hα0 h4a).ne'
  have hny : (1 - P.α) * (4 * P.k - P.ϕ ^ 2) ≠ 0 := (mul_pos (by linarith) h4c).ne'
  constructor
  · unfold Params.dX
    rw [← hd]
    have : o.dx - b.d = s * (8 * P.k - 1) / (P.α * (4 * P.k - 1)) := by
      rw [eq_div_iff hnx]; exact hkx
    linarith
  · unfold Params.dY
    rw [← hd]
    have : b.d - o.dy = s * (8 * P.k - P.ϕ ^ 2) / ((1 - P.α) * (4 * P.k - P.ϕ ^ 2)) := by
      rw [eq_div_iff hny]; exact hky
    linarith

noncomputable def ReservationPolicy.Eq11Proof.Wf (P : Params) (s : ℝ) : ℝ :=
  P.α * (1 / 4 * (1 - P.dX s + (1 + P.dX s) / (8 * P.k - 1)) *
        (1 + P.dX s + (1 + P.dX s) / (8 * P.k - 1)) -
      P.k * ((1 + P.dX s) / (8 * P.k - 1)) ^ 2 - P.κ) +
    (1 - P.α) * (1 / 4 * (1 - P.dY s + P.ϕ ^ 2 * (1 + P.dY s) / (8 * P.k - P.ϕ ^ 2)) *
        (1 + P.dY s + P.ϕ ^ 2 * (1 + P.dY s) / (8 * P.k - P.ϕ ^ 2)) -
      P.k * (P.ϕ * (1 + P.dY s) / (8 * P.k - P.ϕ ^ 2)) ^ 2)

open ReservationPolicy.Eq11Proof in
theorem ReservationPolicy.Eq11Proof.welfare_eq (P : Params) (hP : P.Valid) (b : Benchmark)
    (hb : IsInvestCandidate P b) (s : ℝ) (o : PolicyOutcome) (ho : IsPolicyEq P b s o) :
    welfare P o = Wf P s := by
  obtain ⟨hdx, hdy⟩ := eq5152 P hP b hb s o ho
  obtain ⟨hI, hPl, -, -, -, -⟩ := ho
  obtain ⟨⟨-, hx0, hx1⟩, hexO, hrxO⟩ := ((eq11 P hP o.dx).1 o.ex o.rx).mp hI
  obtain ⟨⟨-, hy0, hy1⟩, heyO, hryO⟩ := ((eq11 P hP o.dy).2 o.ey o.ry).mp hPl
  obtain ⟨hxa, hxb⟩ := admitProb_range _ _ hx0 hx1
  obtain ⟨hya, hyb⟩ := admitProb_range _ _ hy0 hy1
  unfold welfare payoffInvest payoffPlain Wf
  rw [admitProb_eq _ _ hxa hxb, admitProb_eq _ _ hya hyb, hrxO, hryO, hexO, heyO, hdx, hdy]
  ring

open ReservationPolicy.Eq11Proof in
theorem ReservationPolicy.Eq11Proof.lead_form (P : Params) :
    (Wf P 1 + Wf P (-1) - 2 * Wf P 0) / 2 =
      P.α * ((8 * P.k - 1) / (P.α * (4 * P.k - 1))) ^ 2 *
          (1 / 4 * ((1 / (8 * P.k - 1)) ^ 2 - 1) - P.k * (1 / (8 * P.k - 1)) ^ 2) +
        (1 - P.α) * ((8 * P.k - P.ϕ ^ 2) / ((1 - P.α) * (4 * P.k - P.ϕ ^ 2))) ^ 2 *
          (1 / 4 * ((P.ϕ ^ 2 * (1 / (8 * P.k - P.ϕ ^ 2))) ^ 2 - 1) -
            P.k * P.ϕ ^ 2 * (1 / (8 * P.k - P.ϕ ^ 2)) ^ 2) := by
  simp only [Wf, Params.dX, Params.dY]
  ring

open ReservationPolicy.Eq11Proof in
theorem ReservationPolicy.Eq11Proof.lead_neg (P : Params) (hP : P.Valid) :
    (Wf P 1 + Wf P (-1) - 2 * Wf P 0) / 2 < 0 := by
  obtain ⟨hk, hϕ0, hϕ1, hα0, hα1, -⟩ := hP
  rw [lead_form]
  have ha : 0 < 8 * P.k - 1 := by linarith
  have hc : 0 < 8 * P.k - P.ϕ ^ 2 := by nlinarith
  have hp : 0 < 4 * P.k - 1 := by linarith
  have hq : 0 < 4 * P.k - P.ϕ ^ 2 := by nlinarith
  have h1α : 0 < 1 - P.α := by linarith
  have hx : 1 / 4 * ((1 / (8 * P.k - 1)) ^ 2 - 1) - P.k * (1 / (8 * P.k - 1)) ^ 2 < 0 := by
    have e : 1 / 4 * ((1 / (8 * P.k - 1)) ^ 2 - 1) - P.k * (1 / (8 * P.k - 1)) ^ 2 =
        (1 / 4 - P.k) * (1 / (8 * P.k - 1)) ^ 2 - 1 / 4 := by ring
    rw [e]
    have : 0 < (1 / (8 * P.k - 1)) ^ 2 := by positivity
    nlinarith
  have hy : 1 / 4 * ((P.ϕ ^ 2 * (1 / (8 * P.k - P.ϕ ^ 2))) ^ 2 - 1) -
      P.k * P.ϕ ^ 2 * (1 / (8 * P.k - P.ϕ ^ 2)) ^ 2 < 0 := by
    have e : 1 / 4 * ((P.ϕ ^ 2 * (1 / (8 * P.k - P.ϕ ^ 2))) ^ 2 - 1) -
        P.k * P.ϕ ^ 2 * (1 / (8 * P.k - P.ϕ ^ 2)) ^ 2 =
        (P.ϕ ^ 2 / 4 - P.k) * (P.ϕ ^ 2 * (1 / (8 * P.k - P.ϕ ^ 2)) ^ 2) - 1 / 4 := by ring
    rw [e]
    have : 0 ≤ P.ϕ ^ 2 * (1 / (8 * P.k - P.ϕ ^ 2)) ^ 2 := by positivity
    nlinarith
  have hA : 0 < P.α * ((8 * P.k - 1) / (P.α * (4 * P.k - 1))) ^ 2 := by positivity
  have hB : 0 < (1 - P.α) * ((8 * P.k - P.ϕ ^ 2) / ((1 - P.α) * (4 * P.k - P.ϕ ^ 2))) ^ 2 := by
    positivity
  have t1 := mul_neg_of_pos_of_neg hA hx
  have t2 := mul_neg_of_pos_of_neg hB hy
  linarith

open ReservationPolicy.Eq11Proof in
theorem solution (P : Params) (hP : P.Valid) (b : Benchmark) (hb : IsInvestCandidate P b)
    (s : ℝ) (hs : 0 < s) (o : PolicyOutcome) (ho : IsPolicyEq P b s o) :
    b.ex < o.ex ∧ o.ey < b.ey := by
  have hP' := hP
  obtain ⟨hk, hϕ0, hϕ1, hα0, hα1, -⟩ := hP'
  obtain ⟨hdx, hdy⟩ := eq5152 P hP b hb s o ho
  obtain ⟨hd, -, -⟩ := eq2627 P hP b hb
  obtain ⟨hIB, hPlB, -⟩ := hb
  obtain ⟨-, hexB, -⟩ := ((eq11 P hP b.d).1 b.ex b.rx).mp hIB
  obtain ⟨-, heyB, -⟩ := ((eq11 P hP b.d).2 b.ey b.ry).mp hPlB
  obtain ⟨hI, hPl, -, -, -, -⟩ := ho
  obtain ⟨-, hexO, -⟩ := ((eq11 P hP o.dx).1 o.ex o.rx).mp hI
  obtain ⟨-, heyO, -⟩ := ((eq11 P hP o.dy).2 o.ey o.ry).mp hPl
  have ha : 0 < 8 * P.k - 1 := by linarith
  have hc : 0 < 8 * P.k - P.ϕ ^ 2 := by nlinarith
  have hp : 0 < 4 * P.k - 1 := by linarith
  have hq : 0 < 4 * P.k - P.ϕ ^ 2 := by nlinarith
  have h1α : 0 < 1 - P.α := by linarith
  constructor
  · rw [hexB, hexO, hdx, hd, div_lt_div_iff_of_pos_right ha]
    unfold Params.dX
    have : 0 < s * (8 * P.k - 1) / (P.α * (4 * P.k - 1)) := by positivity
    linarith
  · rw [heyB, heyO, hdy, hd, div_lt_div_iff_of_pos_right hc]
    unfold Params.dY
    have : 0 < s * (8 * P.k - P.ϕ ^ 2) / ((1 - P.α) * (4 * P.k - P.ϕ ^ 2)) := by positivity
    nlinarith
