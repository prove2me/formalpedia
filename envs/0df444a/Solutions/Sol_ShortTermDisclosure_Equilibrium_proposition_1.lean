-- Prove2me | solution 1 for ShortTermDisclosure.Equilibrium.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:35:39.825497+00:00
-- url     : https://prove2.me/submissions/5d3f8487-a463-4bdc-954d-d199ba13890c

import Mathlib
import Definitions.Def_ShortTermDisclosure_Equilibrium_Model
import Theorems.Thm_ShortTermDisclosure_Equilibrium_lemma_1
import Theorems.Thm_ShortTermDisclosure_Equilibrium_disclosure_condition
import Theorems.Thm_ShortTermDisclosure_Equilibrium_upper_fixed_point
import Theorems.Thm_ShortTermDisclosure_Equilibrium_two_tailed_fixed_point

namespace Aux_STD_p1

open ShortTermDisclosure.Equilibrium MeasureTheory

lemma lam_nonneg (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) : 0 ≤ lam η :=
  div_nonneg h0 (by linarith)

lemma lam_le_one (η : ℝ) (h1 : η ≤ 1) : lam η ≤ 1 := by
  unfold lam; rw [div_le_one (by linarith)]; linarith

lemma belief_bounds (P : Params) (hP : P.Standing) (S : Set ℝ) (hS : MeasurableSet S)
    (hsub : S ⊆ Set.Icc P.vlo P.vhi) :
    P.vlo ≤ belief P S ∧ belief P S ≤ P.vhi := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  have iid : IntegrableOn (fun v : ℝ => v) S volume :=
    (continuous_id.integrableOn_Icc).mono_set hsub
  have ilo : IntegrableOn (fun _ : ℝ => P.vlo) S volume :=
    (continuous_const.integrableOn_Icc).mono_set hsub
  have ihi : IntegrableOn (fun _ : ℝ => P.vhi) S volume :=
    (continuous_const.integrableOn_Icc).mono_set hsub
  have hI1 : ∫ v in S, P.vlo ≤ ∫ v in S, v :=
    setIntegral_mono_on ilo iid hS (fun v hv => (hsub hv).1)
  have hI2 : ∫ v in S, v ≤ ∫ v in S, P.vhi :=
    setIntegral_mono_on iid ihi hS (fun v hv => (hsub hv).2)
  rw [setIntegral_const, smul_eq_mul, measureReal_def] at hI1 hI2
  set V := (volume S).toReal with hVd
  set I := ∫ v in S, v with hId
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hL : 0 < P.vhi - P.vlo := by linarith
  have hden : 0 < P.p * (V / (P.vhi - P.vlo)) + (1 - P.p) := by
    have := div_nonneg hV hL.le
    nlinarith
  unfold belief
  simp only []
  rw [← hVd, ← hId]
  constructor
  · rw [le_div_iff₀ hden]
    have e : P.vlo * (P.p * (V / (P.vhi - P.vlo)) + (1 - P.p)) =
        P.p * ((P.vlo * V) / (P.vhi - P.vlo)) + (1 - P.p) * P.vlo := by ring
    rw [e]
    have : P.vlo * V / (P.vhi - P.vlo) ≤ I / (P.vhi - P.vlo) :=
      div_le_div_of_nonneg_right (by linarith) hL.le
    nlinarith
  · rw [div_le_iff₀ hden]
    have e : P.vhi * (P.p * (V / (P.vhi - P.vlo)) + (1 - P.p)) =
        P.p * ((P.vhi * V) / (P.vhi - P.vlo)) + (1 - P.p) * P.vhi := by ring
    rw [e]
    have : I / (P.vhi - P.vlo) ≤ P.vhi * V / (P.vhi - P.vlo) :=
      div_le_div_of_nonneg_right (by linarith) hL.le
    nlinarith

lemma belief_empty (P : Params) (hP : P.Standing) :
    belief P ∅ = (P.vlo + P.vhi) / 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  unfold belief
  simp only [Measure.restrict_empty, integral_zero_measure, measure_empty,
    ENNReal.toReal_zero, zero_div, mul_zero, zero_add]
  have : (1 - P.p) ≠ 0 := by linarith
  field_simp

lemma mgr (P : Params) (hP : P.Standing) (η v N tD tN : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hv : v ∈ Set.Icc P.vlo P.vhi) (hN : N ∈ Set.Icc P.vlo P.vhi)
    (hD : IsSHBestResponse η P.muhi v tD)
    (hND : IsSHBestResponse η P.muhi N tN) :
    managerValue P.muhi tN v ≤ managerValue P.muhi tD v ↔
      ¬ (v < N ∧ (1 + lam η) * N < (1 - lam η) * v + 2 * lam η * P.muhi) := by
  rw [(disclosure_condition P hP η v N tD tN hη0 hη1 hv hN hD hND).2.1]
  have l0 := lam_nonneg η hη0 hη1
  have l1 := lam_le_one η hη1
  set l := lam η
  have hNm : N < P.muhi := lt_of_le_of_lt hN.2 hP.2.2.1
  have e : l * (1 + l) * P.muhi + (1 + l) * ((1 - l) / 2 * v - (1 + l) / 2 * N) =
      (1 + l) / 2 * ((1 - l) * v + 2 * l * P.muhi - (1 + l) * N) := by ring
  rw [e]
  constructor
  · rintro h ⟨hvN, hG⟩
    have : 0 < (1 + l) / 2 * ((1 - l) * v + 2 * l * P.muhi - (1 + l) * N) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  · intro h
    by_cases hvN : N ≤ v
    · apply mul_nonneg (by linarith)
      apply mul_nonneg (by linarith)
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - l) (by linarith : (0:ℝ) ≤ v - N),
        mul_nonneg l0 (by linarith : (0:ℝ) ≤ P.muhi - N)]
    · push_neg at hvN
      have hG : (1 - l) * v + 2 * l * P.muhi ≤ (1 + l) * N := by
        by_contra hc; push_neg at hc; exact h ⟨hvN, hc⟩
      apply mul_nonneg_of_nonpos_of_nonpos (by linarith)
      apply mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)


def ndset (P : Params) (l N : ℝ) : Set ℝ :=
  {v | v ∈ Set.Icc P.vlo P.vhi ∧ v < N ∧ (1 + l) * N < (1 - l) * v + 2 * l * P.muhi}

lemma ndset_sub (P : Params) (l N : ℝ) : ndset P l N ⊆ Set.Icc P.vlo P.vhi :=
  fun _ hv => hv.1

lemma nd_zero (P : Params) (N : ℝ) : ndset P 0 N = ∅ := by
  ext v
  simp only [ndset, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, h1, h2⟩
  linarith

lemma nd_up (P : Params) (l N : ℝ) (hl1 : l ≤ 1) (hNhi : N ≤ P.vhi)
    (hc : (1 + l) * N < (1 - l) * P.vlo + 2 * l * P.muhi) :
    ndset P l N = Set.Ico P.vlo N := by
  ext v
  simp only [ndset, Set.mem_setOf_eq, Set.mem_Ico, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, h2, _⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, by linarith⟩, h2, ?_⟩
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 1 - l)]

lemma v1_mul (l N muhi : ℝ) (hl1 : l < 1) :
    ((1 + l) / (1 - l) * N - 2 * l / (1 - l) * muhi) * (1 - l) =
      (1 + l) * N - 2 * l * muhi := by
  have : (1 - l) ≠ 0 := by linarith
  field_simp

lemma v1_lt_iff (l N muhi x : ℝ) (hl1 : l < 1) :
    (1 + l) / (1 - l) * N - 2 * l / (1 - l) * muhi < x ↔
      (1 + l) * N < (1 - l) * x + 2 * l * muhi := by
  have hw : 0 < 1 - l := by linarith
  rw [← mul_lt_mul_iff_of_pos_right hw, v1_mul l N muhi hl1]
  constructor <;> intro h <;> linarith

lemma le_v1_iff (l N muhi x : ℝ) (hl1 : l < 1) :
    x ≤ (1 + l) / (1 - l) * N - 2 * l / (1 - l) * muhi ↔
      (1 - l) * x + 2 * l * muhi ≤ (1 + l) * N := by
  have hw : 0 < 1 - l := by linarith
  rw [← mul_le_mul_iff_of_pos_right hw, v1_mul l N muhi hl1]
  constructor <;> intro h <;> linarith

lemma v1_lt (l N muhi : ℝ) (hl0 : 0 < l) (hl1 : l < 1) (hN : N < muhi) :
    (1 + l) / (1 - l) * N - 2 * l / (1 - l) * muhi < N := by
  rw [v1_lt_iff l N muhi N hl1]; nlinarith

lemma nd_two (P : Params) (l N : ℝ) (hl1 : l < 1) (hNhi : N ≤ P.vhi)
    (hc : (1 - l) * P.vlo + 2 * l * P.muhi ≤ (1 + l) * N) :
    ndset P l N = Set.Ioo ((1 + l) / (1 - l) * N - 2 * l / (1 - l) * P.muhi) N := by
  have hv1 := (le_v1_iff l N P.muhi P.vlo hl1).2 hc
  ext v
  simp only [ndset, Set.mem_setOf_eq, Set.mem_Ioo, Set.mem_Icc]
  rw [v1_lt_iff l N P.muhi v hl1]
  constructor
  · rintro ⟨_, h2, h3⟩; exact ⟨h3, h2⟩
  · rintro ⟨h3, h2⟩
    have := (v1_lt_iff l N P.muhi v hl1).2 h3
    exact ⟨⟨by linarith, by linarith⟩, h2, h3⟩

lemma upper_root (P : Params) (hP : P.Standing) :
    ∃ Np : ℝ, P.vlo < Np ∧ Np < (P.vhi + P.vlo) / 2 ∧
      P.p / (1 - P.p) * (Np - P.vlo) ^ 2 =
        2 * (P.vhi - P.vlo) * ((P.vhi + P.vlo) / 2 - Np) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  set K := P.p / (1 - P.p) with hK
  have hKpos : 0 < K := div_pos h4 (by linarith)
  set L := P.vhi - P.vlo with hL
  have hLpos : 0 < L := by linarith
  set s := Real.sqrt (L ^ 2 + K * L ^ 2) with hs
  have hs2 : s ^ 2 = L ^ 2 + K * L ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsL : L < s := by nlinarith [mul_pos hKpos (mul_pos hLpos hLpos)]
  have hx : 0 < (s - L) / K := div_pos (by linarith) hKpos
  have key : K * ((s - L) / K) ^ 2 = L ^ 2 - 2 * L * ((s - L) / K) := by
    field_simp
    nlinarith
  refine ⟨P.vlo + (s - L) / K, by linarith, ?_, ?_⟩
  · have : 0 < K * ((s - L) / K) ^ 2 := by positivity
    nlinarith
  · have e1 : P.vlo + (s - L) / K - P.vlo = (s - L) / K := by ring
    rw [e1, key]
    have e2 : (P.vhi + P.vlo) / 2 = P.vlo + L / 2 := by rw [hL]; ring
    rw [e2]; ring

lemma up_unique (K L vlo m N N' : ℝ) (hK : 0 < K) (hL : 0 < L) (hN : vlo < N) (hN' : vlo < N')
    (e1 : K * (N - vlo) ^ 2 = 2 * L * (m - N)) (e2 : K * (N' - vlo) ^ 2 = 2 * L * (m - N')) :
    N = N' := by
  have h : (N - N') * (K * (N + N' - 2 * vlo) + 2 * L) = 0 := by linear_combination e1 - e2
  rcases mul_eq_zero.1 h with h | h
  · linarith
  · nlinarith [mul_pos hK (by linarith : (0:ℝ) < N + N' - 2 * vlo)]

lemma mono_aux (a b c : ℝ) (hb0 : 0 < b) (hab : b ≤ a) (ha2 : a < 2 * c) (hb2 : b < 2 * c) :
    (b - c) * a ^ 2 ≤ (a - c) * b ^ 2 := by
  have M : 0 ≤ (a - b) * (c * (a + b) - a * b) := by
    apply mul_nonneg (by linarith)
    nlinarith [mul_pos (by linarith : (0:ℝ) < a) (by linarith : (0:ℝ) < 2 * c - b),
      mul_pos hb0 (by linarith : (0:ℝ) < 2 * c - a)]
  linarith

lemma no_two (K L vlo muhi m l N Np : ℝ) (hK : 0 < K) (hL : 0 < L)
    (hm : m < muhi) (hm2 : 2 * m - muhi < vlo)
    (hl0 : 0 < l) (hl1 : l < 1) (hNp : vlo < Np)
    (hNpe : K * (Np - vlo) ^ 2 = 2 * L * (m - Np))
    (hup : (1 + l) * Np < (1 - l) * vlo + 2 * l * muhi)
    (hNm : N < m) (hc2 : (1 - l) * vlo + 2 * l * muhi ≤ (1 + l) * N)
    (he : K * (N - ((1 + l) / (1 - l) * N - 2 * l / (1 - l) * muhi)) ^ 2 = 2 * L * (m - N)) :
    False := by
  have hw0 : 0 < 1 - l := by linarith
  have hwne : (1 - l) ≠ 0 := ne_of_gt hw0
  have hd : N - ((1 + l) / (1 - l) * N - 2 * l / (1 - l) * muhi) =
      2 * l * (muhi - N) / (1 - l) := by
    field_simp; ring
  rw [hd, div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero 2 hwne)] at he
  -- he : K * (2 * l * (muhi - N)) ^ 2 = 2 * L * (m - N) * (1 - l) ^ 2
  have hc2' : 2 * l * (muhi - N) ≤ (1 - l) * (N - vlo) := by linarith
  have hup' : (1 - l) * (Np - vlo) < 2 * l * (muhi - Np) := by linarith
  have hb : 0 < muhi - N := by linarith
  have h2l : 0 < 2 * l * (muhi - N) := by positivity
  have hNv : vlo < N := by
    by_contra hh; push_neg at hh
    have : (1 - l) * (N - vlo) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw0.le (by linarith)
    linarith
  have hNNp : Np ≤ N := by
    by_contra hlt; push_neg at hlt
    have q1 : (2 * l * (muhi - N)) ^ 2 ≤ ((1 - l) * (N - vlo)) ^ 2 :=
      pow_le_pow_left₀ h2l.le hc2' 2
    have q1' := mul_le_mul_of_nonneg_left q1 hK.le
    rw [he] at q1'
    have q3 : (2 * L * (m - N)) * (1 - l) ^ 2 ≤ (K * (N - vlo) ^ 2) * (1 - l) ^ 2 := by
      linarith
    have q4 : 2 * L * (m - N) ≤ K * (N - vlo) ^ 2 :=
      le_of_mul_le_mul_right q3 (by positivity)
    have q2 : (N - vlo) ^ 2 < (Np - vlo) ^ 2 :=
      pow_lt_pow_left₀ (by linarith) (by linarith) two_ne_zero
    have q5 := mul_lt_mul_of_pos_left q2 hK
    have q6 : 2 * L * (m - Np) < 2 * L * (m - N) := by
      have := mul_lt_mul_of_pos_left hlt (by linarith : (0:ℝ) < 2 * L)
      linarith
    linarith
  have S1 : ((1 - l) * (Np - vlo)) ^ 2 < (2 * l * (muhi - Np)) ^ 2 :=
    pow_lt_pow_left₀ hup' (by positivity) two_ne_zero
  have S1' := mul_lt_mul_of_pos_left S1 hK
  have I1 : K * ((1 - l) * (Np - vlo)) ^ 2 = 2 * L * (m - Np) * (1 - l) ^ 2 := by
    linear_combination (1 - l) ^ 2 * hNpe
  have hb2 : 0 < (muhi - N) ^ 2 := by positivity
  have T1 := mul_lt_mul_of_pos_right S1' hb2
  have T2 : K * (2 * l * (muhi - Np)) ^ 2 * (muhi - N) ^ 2 =
      2 * L * (m - N) * (1 - l) ^ 2 * (muhi - Np) ^ 2 := by
    linear_combination (muhi - Np) ^ 2 * he
  have hB : 0 < 2 * L * (1 - l) ^ 2 := by positivity
  have S3' : 2 * L * (1 - l) ^ 2 * ((m - Np) * (muhi - N) ^ 2) <
      2 * L * (1 - l) ^ 2 * ((m - N) * (muhi - Np) ^ 2) := by
    rw [I1] at T1; linarith
  have S3 := lt_of_mul_lt_mul_left S3' hB.le
  have M := mono_aux (muhi - Np) (muhi - N) (muhi - m) hb (by linarith) (by linarith) (by linarith)
  have e1 : (muhi - N) - (muhi - m) = m - N := by ring
  have e2 : (muhi - Np) - (muhi - m) = m - Np := by ring
  rw [e1, e2] at M
  linarith

end Aux_STD_p1

open ShortTermDisclosure.Equilibrium Aux_STD_p1 in
theorem solution (P : Params) (hP : P.Standing) :
    ∃ lamStar : ℝ, 0 < lamStar ∧ lamStar < 1 ∧
    ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
      (∃ E : Profile, IsEquilibrium P η E) ∧
      ∀ E : Profile, IsEquilibrium P η E →
        E.tN = (1 + lam η) * E.N - lam η * P.muhi ∧
        (∀ v ∈ Set.Icc P.vlo P.vhi,
          E.tD v = (1 + lam η) * v - lam η * P.muhi) ∧
        (lam η = 0 → E.D = Set.Icc P.vlo P.vhi) ∧
        (0 < lam η → lam η ≤ lamStar →
          P.vlo ≤ (1 + lam η) / (1 - lam η) * E.N -
            2 * lam η / (1 - lam η) * P.muhi ∧
          (1 + lam η) / (1 - lam η) * E.N -
            2 * lam η / (1 - lam η) * P.muhi < E.N ∧
          E.N ≤ P.vhi ∧
          Set.Icc P.vlo P.vhi \ E.D =
            Set.Ioo ((1 + lam η) / (1 - lam η) * E.N -
              2 * lam η / (1 - lam η) * P.muhi) E.N) ∧
        (lamStar < lam η →
          P.vlo < E.N ∧ E.N ≤ P.vhi ∧
          Set.Icc P.vlo P.vhi \ E.D = Set.Ico P.vlo E.N) := by
  have hP' := hP
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP'
  have hKpos : 0 < P.p / (1 - P.p) := div_pos h4 (by linarith)
  have hLpos : 0 < P.vhi - P.vlo := by linarith
  have hmuhi : 0 < P.muhi := by linarith
  obtain ⟨Np, hNp1, hNp2, hNpe⟩ := upper_root P hP
  have hden : 0 < 2 * P.muhi - Np - P.vlo := by linarith
  have hstar0 : 0 < (Np - P.vlo) / (2 * P.muhi - Np - P.vlo) := div_pos (by linarith) hden
  have hstar1 : (Np - P.vlo) / (2 * P.muhi - Np - P.vlo) < 1 := (div_lt_one hden).2 (by linarith)
  refine ⟨(Np - P.vlo) / (2 * P.muhi - Np - P.vlo), hstar0, hstar1, ?_⟩
  intro η hη0 hη1
  have l0 := lam_nonneg η hη0 hη1
  have l1 := lam_le_one η hη1
  have hcrit : ∀ x : ℝ, x ≤ (Np - P.vlo) / (2 * P.muhi - Np - P.vlo) ↔
      (1 - x) * P.vlo + 2 * x * P.muhi ≤ (1 + x) * Np := by
    intro x
    rw [le_div_iff₀ hden]
    constructor <;> intro h <;> linarith
  have tfun : ∀ x ∈ Set.Icc P.vlo P.vhi,
      IsSHBestResponse η P.muhi x ((1 + lam η) * x - lam η * P.muhi) := fun x hx =>
    (lemma_1 η P.muhi x _ hη0 hη1 hmuhi (by linarith [hx.1]) (by linarith [hx.2])).2 rfl
  have build : ∀ N ∈ Set.Icc P.vlo P.vhi, MeasurableSet (ndset P (lam η) N) →
      belief P (ndset P (lam η) N) = N → ∃ E : Profile, IsEquilibrium P η E := by
    intro N hN hmeas hbel
    refine ⟨⟨Set.Icc P.vlo P.vhi \ ndset P (lam η) N, N,
      fun v => (1 + lam η) * v - lam η * P.muhi, (1 + lam η) * N - lam η * P.muhi⟩, ?_⟩
    have hdiff : Set.Icc P.vlo P.vhi \ (Set.Icc P.vlo P.vhi \ ndset P (lam η) N) =
        ndset P (lam η) N := Set.diff_diff_cancel_left (ndset_sub P _ N)
    refine ⟨Set.diff_subset, measurableSet_Icc.diff hmeas, ?_, fun v hv => tfun v hv,
      tfun N hN, ?_⟩
    · show N = belief P (Set.Icc P.vlo P.vhi \ (Set.Icc P.vlo P.vhi \ ndset P (lam η) N))
      rw [hdiff, hbel]
    · intro v hv
      show v ∈ Set.Icc P.vlo P.vhi \ ndset P (lam η) N ↔ _
      rw [mgr P hP η v N _ _ hη0 hη1 hv hN (tfun v hv) (tfun N hN)]
      simp only [Set.mem_diff, ndset, Set.mem_setOf_eq]
      tauto
  have hm_in : (P.vhi + P.vlo) / 2 ∈ Set.Icc P.vlo P.vhi := ⟨by linarith, by linarith⟩
  have bel_empty' : belief P ∅ = (P.vhi + P.vlo) / 2 := by
    rw [belief_empty P hP]; ring
  refine ⟨?_, ?_⟩
  · -- existence
    rcases eq_or_lt_of_le l0 with hl | hl
    · have hnd : ndset P (lam η) ((P.vhi + P.vlo) / 2) = ∅ := by
        rw [← hl]; exact nd_zero P _
      refine build _ hm_in (by rw [hnd]; exact MeasurableSet.empty) ?_
      rw [hnd, bel_empty']
    · by_cases hle : lam η ≤ (Np - P.vlo) / (2 * P.muhi - Np - P.vlo)
      · have hl1 : lam η < 1 := lt_of_le_of_lt hle hstar1
        have hc := (hcrit _).1 hle
        set l := lam η with hldef
        let f : ℝ → ℝ := fun x => P.p / (1 - P.p) *
          (x - ((1 + l) / (1 - l) * x - 2 * l / (1 - l) * P.muhi)) ^ 2 -
          2 * (P.vhi - P.vlo) * ((P.vhi + P.vlo) / 2 - x)
        have fc : ContinuousOn f (Set.Icc Np ((P.vhi + P.vlo) / 2)) := by
          apply Continuous.continuousOn
          fun_prop
        have hv1Np : P.vlo ≤ (1 + l) / (1 - l) * Np - 2 * l / (1 - l) * P.muhi :=
          (le_v1_iff l Np P.muhi P.vlo hl1).2 hc
        have hv1Np' := v1_lt l Np P.muhi hl hl1 (by linarith)
        have fNp : f Np ≤ 0 := by
          have q : (Np - ((1 + l) / (1 - l) * Np - 2 * l / (1 - l) * P.muhi)) ^ 2 ≤
              (Np - P.vlo) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
          have := mul_le_mul_of_nonneg_left q hKpos.le
          show _ - _ ≤ 0
          linarith
        have fm : 0 ≤ f ((P.vhi + P.vlo) / 2) := by
          show 0 ≤ _ - _
          have := mul_nonneg hKpos.le (sq_nonneg ((P.vhi + P.vlo) / 2 -
            ((1 + l) / (1 - l) * ((P.vhi + P.vlo) / 2) - 2 * l / (1 - l) * P.muhi)))
          nlinarith
        obtain ⟨N, ⟨hN1, hN2⟩, hfN⟩ :=
          intermediate_value_Icc hNp2.le fc ⟨fNp, fm⟩
        have hNmu : N < P.muhi := by linarith
        have hv1N := v1_lt l N P.muhi hl hl1 hNmu
        have hNlt : N < (P.vhi + P.vlo) / 2 := by
          rcases eq_or_lt_of_le hN2 with h | h
          · exfalso
            have hf0 : f N = 0 := hfN
            simp only [f] at hf0
            rw [h] at hf0 hv1N
            have : 0 < P.p / (1 - P.p) * ((P.vhi + P.vlo) / 2 -
              ((1 + l) / (1 - l) * ((P.vhi + P.vlo) / 2) - 2 * l / (1 - l) * P.muhi)) ^ 2 :=
              mul_pos hKpos (by have := sub_pos.2 hv1N; positivity)
            linarith
          · exact h
        have hcN : (1 - l) * P.vlo + 2 * l * P.muhi ≤ (1 + l) * N := by nlinarith
        have hv1lo := (le_v1_iff l N P.muhi P.vlo hl1).2 hcN
        have hnd := nd_two P l N hl1 (by linarith) hcN
        refine build N ⟨by linarith, by linarith⟩ (by rw [hnd]; exact measurableSet_Ioo) ?_
        rw [hnd]
        refine ((two_tailed_fixed_point P hP _ N hv1lo hv1N (by linarith)).1).2 ?_
        have hf0 : f N = 0 := hfN
        simp only [f] at hf0
        linarith
      · push_neg at hle
        have hc : (1 + lam η) * Np < (1 - lam η) * P.vlo + 2 * lam η * P.muhi := by
          by_contra hh; push_neg at hh
          exact absurd ((hcrit _).2 hh) (not_le.2 hle)
        have hnd := nd_up P (lam η) Np l1 (by linarith) hc
        refine build Np ⟨by linarith, by linarith⟩ (by rw [hnd]; exact measurableSet_Ico) ?_
        rw [hnd]
        exact (upper_fixed_point P hP Np hNp1 (by linarith)).2 hNpe
  · -- every equilibrium
    intro E hE
    obtain ⟨hsub, hmeas, hbel, hbrD, hbrN, hman⟩ := hE
    have hNb := belief_bounds P hP _ (measurableSet_Icc.diff hmeas) Set.diff_subset
    rw [← hbel] at hNb
    have hN : E.N ∈ Set.Icc P.vlo P.vhi := hNb
    have htN : E.tN = (1 + lam η) * E.N - lam η * P.muhi :=
      (lemma_1 η P.muhi E.N E.tN hη0 hη1 hmuhi (by linarith [hN.1]) (by linarith [hN.2])).1 hbrN
    have htD : ∀ v ∈ Set.Icc P.vlo P.vhi, E.tD v = (1 + lam η) * v - lam η * P.muhi :=
      fun v hv => (lemma_1 η P.muhi v (E.tD v) hη0 hη1 hmuhi (by linarith [hv.1])
        (by linarith [hv.2])).1 (hbrD v hv)
    have hset : Set.Icc P.vlo P.vhi \ E.D = ndset P (lam η) E.N := by
      ext v
      simp only [Set.mem_diff, ndset, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hv, hvD⟩
        have := (mgr P hP η v E.N _ _ hη0 hη1 hv hN (hbrD v hv) hbrN)
        rw [hman v hv] at hvD
        rw [this] at hvD
        push_neg at hvD
        exact ⟨hv, hvD⟩
      · rintro ⟨hv, hh⟩
        refine ⟨hv, fun hvD => ?_⟩
        rw [hman v hv, mgr P hP η v E.N _ _ hη0 hη1 hv hN (hbrD v hv) hbrN] at hvD
        exact hvD hh
    rw [hset] at hbel
    -- belief of an empty nondisclosure set
    have upper_case : (1 + lam η) * E.N < (1 - lam η) * P.vlo + 2 * lam η * P.muhi →
        P.vlo < E.N ∧ Set.Icc P.vlo P.vhi \ E.D = Set.Ico P.vlo E.N := by
      intro hc
      have hnd := nd_up P (lam η) E.N l1 hN.2 hc
      rw [hnd] at hbel
      refine ⟨?_, hset.trans hnd⟩
      by_contra hh; push_neg at hh
      rw [Set.Ico_eq_empty (not_lt.2 hh), bel_empty'] at hbel
      linarith
    refine ⟨htN, htD, ?_, ?_, ?_⟩
    · intro hl
      have hnd : ndset P (lam η) E.N = ∅ := by rw [hl]; exact nd_zero P _
      rw [hnd, Set.diff_eq_empty] at hset
      exact Set.Subset.antisymm hsub hset
    · intro hl hle
      have hl1 : lam η < 1 := lt_of_le_of_lt hle hstar1
      have hcN : (1 - lam η) * P.vlo + 2 * lam η * P.muhi ≤ (1 + lam η) * E.N := by
        by_contra hh; push_neg at hh
        obtain ⟨hNlo, hset2⟩ := upper_case hh
        have hnd := nd_up P (lam η) E.N l1 hN.2 hh
        rw [hnd] at hbel
        have he := (upper_fixed_point P hP E.N hNlo hN.2).1 hbel.symm
        have := up_unique _ _ _ _ _ _ hKpos hLpos hNlo hNp1 he hNpe
        rw [this] at hh
        have := (hcrit _).1 hle
        linarith
      have hnd := nd_two P (lam η) E.N hl1 hN.2 hcN
      exact ⟨(le_v1_iff _ _ _ _ hl1).2 hcN, v1_lt _ _ _ hl hl1 (by linarith [hN.2]),
        hN.2, hset.trans hnd⟩
    · intro hlt
      have hl : 0 < lam η := lt_trans hstar0 hlt
      have hc : (1 + lam η) * E.N < (1 - lam η) * P.vlo + 2 * lam η * P.muhi := by
        by_contra hcN; push_neg at hcN
        have hl1 : lam η < 1 := by
          by_contra hh; push_neg at hh
          have : lam η = 1 := le_antisymm l1 hh
          rw [this] at hcN
          linarith [hN.2]
        have hnd := nd_two P (lam η) E.N hl1 hN.2 hcN
        rw [hnd] at hbel
        have hv1lo := (le_v1_iff _ _ _ _ hl1).2 hcN
        have hv1N := v1_lt (lam η) E.N P.muhi hl hl1 (by linarith [hN.2])
        have htt := two_tailed_fixed_point P hP _ E.N hv1lo hv1N hN.2
        have he := htt.1.1 hbel.symm
        have hNm := htt.2 hbel.symm
        have hupNp : (1 + lam η) * Np < (1 - lam η) * P.vlo + 2 * lam η * P.muhi := by
          by_contra hh; push_neg at hh
          exact absurd ((hcrit _).2 hh) (not_le.2 hlt)
        exact no_two _ _ _ _ _ _ _ _ hKpos hLpos (by linarith) (by linarith) hl hl1 hNp1
          hNpe hupNp hNm hcN he
      obtain ⟨hNlo, hset2⟩ := upper_case hc
      exact ⟨hNlo, hN.2, hset2⟩
