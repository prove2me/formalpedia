-- Prove2me | solution 2 for SLPEPricing.Regret.theorem_1
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T00:07:52.811314+00:00
-- url     : https://prove2.me/submissions/0b9c6e75-7a09-45ab-80f8-b4d9c1c9dab1

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model

set_option autoImplicit false

namespace E500

open SLPEPricing.Regret

/-! ## D1: the instance -/

noncomputable def P (p : ℝ) : ℝ :=
  73/100 - (p - 73/100) + 67/100 * (p - 73/100)^3 + 3/100 * (p - 73/100)^4
    - 1/25 * (p - 73/100)^5
noncomputable def P1 (p : ℝ) : ℝ :=
  -1 + 201/100 * (p - 73/100)^2 + 3/25 * (p - 73/100)^3 - 1/5 * (p - 73/100)^4
noncomputable def P2 (p : ℝ) : ℝ :=
  201/50 * (p - 73/100) + 9/25 * (p - 73/100)^2 - 4/5 * (p - 73/100)^3
noncomputable def P3 (p : ℝ) : ℝ :=
  201/50 + 18/25 * (p - 73/100) - 12/5 * (p - 73/100)^2

lemma hasDerivAt_P (x : ℝ) : HasDerivAt P (P1 x) x := by
  have hu : HasDerivAt (fun p : ℝ => p - 73/100) 1 x := (hasDerivAt_id' x).sub_const _
  have h := ((((hasDerivAt_const x (73/100 : ℝ)).sub hu).add ((hu.pow 3).const_mul (67/100))).add
    ((hu.pow 4).const_mul (3/100))).sub ((hu.pow 5).const_mul (1/25))
  refine h.congr_deriv ?_
  unfold P1; norm_num <;> ring

lemma hasDerivAt_P1 (x : ℝ) : HasDerivAt P1 (P2 x) x := by
  have hu : HasDerivAt (fun p : ℝ => p - 73/100) 1 x := (hasDerivAt_id' x).sub_const _
  have h := ((((hasDerivAt_const x (-1 : ℝ)).add ((hu.pow 2).const_mul (201/100))).add
    ((hu.pow 3).const_mul (3/25))).sub ((hu.pow 4).const_mul (1/5)))
  refine h.congr_deriv ?_
  unfold P2; norm_num <;> ring

lemma hasDerivAt_P2 (x : ℝ) : HasDerivAt P2 (P3 x) x := by
  have hu : HasDerivAt (fun p : ℝ => p - 73/100) 1 x := (hasDerivAt_id' x).sub_const _
  have h := (((hu.const_mul (201/50)).add ((hu.pow 2).const_mul (9/25))).sub
    ((hu.pow 3).const_mul (4/5)))
  refine h.congr_deriv ?_
  unfold P3; norm_num <;> ring

noncomputable def H2 : ℝ := 3 * Real.exp 100
noncomputable def x5 : ℝ := 1180572527 / 536870912
noncomputable def D5 : ℝ := 437893890380859375 / 2305843009213693952
noncomputable def z5 : ℝ := x5 + D5
noncomputable def B5 : ℝ := P x5 * x5 / z5
noncomputable def H3 : ℝ :=
  (B5 - P z5 + H2 * expNegInvGlue (z5 - 11/5)) / expNegInvGlue (z5 - 119/50)

noncomputable def dd (p : ℝ) : ℝ :=
  1/800 * (P p - H2 * expNegInvGlue (p - 11/5) + H3 * expNegInvGlue (p - 119/50))

lemma dd_low {p : ℝ} (hp : p ≤ 11/5) : dd p = 1/800 * P p := by
  unfold dd
  rw [expNegInvGlue.zero_of_nonpos (by linarith), expNegInvGlue.zero_of_nonpos (by linarith)]
  ring

lemma dd_z5 : dd z5 = 1/800 * B5 := by
  have hz : (119/50 : ℝ) < z5 := by unfold z5 x5 D5; norm_num
  have hg : 0 < expNegInvGlue (z5 - 119/50) := expNegInvGlue.pos_of_pos (by linarith)
  unfold dd H3
  rw [div_mul_cancel₀ _ hg.ne']
  ring

lemma dd_contDiff : ContDiff ℝ 3 dd := by
  have hg : ContDiff ℝ 3 expNegInvGlue := expNegInvGlue.contDiff
  have hP : ContDiff ℝ 3 P := by unfold P; fun_prop
  unfold dd
  fun_prop

lemma iter_eq (n : ℕ) : ∀ x : ℝ, x < 11/5 →
    iteratedDeriv n dd x = iteratedDeriv n (fun p => 1/800 * P p) x := by
  induction n with
  | zero => intro x hx; simp [dd_low hx.le]
  | succ n ih =>
    intro x hx
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Iio_mem_nhds hx] with y hy using ih y hy

lemma iter1 : iteratedDeriv 1 (fun p => 1/800 * P p) = fun p => 1/800 * P1 p := by
  rw [iteratedDeriv_one]; funext x; exact ((hasDerivAt_P x).const_mul _).deriv

lemma iter2 : iteratedDeriv 2 (fun p => 1/800 * P p) = fun p => 1/800 * P2 p := by
  rw [iteratedDeriv_succ, iter1]; funext x; exact ((hasDerivAt_P1 x).const_mul _).deriv

lemma iter3 : iteratedDeriv 3 (fun p => 1/800 * P p) = fun p => 1/800 * P3 p := by
  rw [iteratedDeriv_succ, iter2]; funext x; exact ((hasDerivAt_P2 x).const_mul _).deriv

lemma deriv_dd {x : ℝ} (hx : x < 11/5) : deriv dd x = 1/800 * P1 x := by
  have := iter_eq 1 x hx
  rw [iteratedDeriv_one, iter1] at this
  exact this

lemma P1_nonpos {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : P1 p ≤ 0 := by
  unfold P1
  rcases le_total p (73/100) with h | h
  · set v := 73/100 - p with hv
    have hv0 : 0 ≤ v := by linarith
    have hva : v ≤ 73/100 := by linarith
    have hpv : p - 73/100 = -v := by linarith
    rw [hpv]
    have ha : 0 ≤ 73/100 - v := by linarith
    nlinarith [mul_nonneg ha hv0, mul_nonneg (mul_nonneg ha hv0) hv0,
      mul_nonneg (mul_nonneg (mul_nonneg ha hv0) hv0) hv0, mul_nonneg ha ha,
      mul_nonneg (mul_nonneg ha hv0) ha]
  · have hu0 : 0 ≤ p - 73/100 := by linarith
    have hu1 : p - 73/100 ≤ 27/100 := by linarith
    nlinarith [mul_nonneg hu0 hu0, mul_nonneg (mul_nonneg hu0 hu0) hu0,
      mul_nonneg (mul_nonneg hu0 hu0) (sub_nonneg.2 hu1)]

lemma dd_antitone : AntitoneOn dd (Set.Icc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
  · exact dd_contDiff.continuous.continuousOn
  · exact (dd_contDiff.differentiable (by norm_num)).differentiableOn
  · intro x hx
    rw [interior_Icc] at hx
    rw [deriv_dd (by linarith [hx.2])]
    have := P1_nonpos hx.1.le hx.2.le
    linarith

lemma abs_bound_aux {a b : ℝ} (h1 : -a ≤ b) (h2 : b ≤ a) : |b| ≤ a := abs_le.2 ⟨h1, h2⟩

lemma standing : Standing dd (73/100) (3/2 * (1/800)) (9/2 * (1/800)) (859/500 * (1/800))
    (15/8) 20 where
  smooth := dd_contDiff
  antitone := dd_antitone
  nonneg := by
    intro p hp
    have h1 : dd 1 ≤ dd p := dd_antitone hp ⟨by norm_num, le_rfl⟩ hp.2
    have : dd 1 = 1/800 * P 1 := dd_low (by norm_num)
    have h2 : 0 ≤ dd 1 := by rw [this]; unfold P; norm_num
    linarith
  pstar_pos := by norm_num
  pstar_lt_one := by norm_num
  unique_max := by
    intro p hp hne
    unfold r
    rw [dd_low (by linarith [hp.2]), dd_low (by norm_num)]
    unfold P
    have hu : p - 73/100 ≠ 0 := sub_ne_zero.2 hne
    have hu2 : 0 < (p - 73/100)^2 := by positivity
    set u := p - 73/100 with hudef
    have hp' : p = u + 73/100 := by linarith
    rw [hp']
    have hl : -73/100 ≤ u := by linarith [hp.1]
    have hr : u ≤ 27/100 := by linarith [hp.2]
    have hw1 : u * (u + 73/100) ≤ 1/2 := by nlinarith
    have hw2 : -1/2 ≤ u * (u + 73/100) := by nlinarith
    have hg0 : 0 ≤ 67/100 + 3/100 * u - 1/25 * u^2 := by nlinarith
    have hg1 : 67/100 + 3/100 * u - 1/25 * u^2 ≤ 1 := by nlinarith
    have hwg : u * (u + 73/100) * (67/100 + 3/100 * u - 1/25 * u^2) ≤ 1/2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hw1) hg0]
    have key : (73/100 : ℝ) * (73/100 - (73/100 - 73/100) + 67/100 * (73/100 - 73/100)^3
        + 3/100 * (73/100 - 73/100)^4 - 1/25 * (73/100 - 73/100)^5)
        - (u + 73/100) * (73/100 - u + 67/100 * u^3 + 3/100 * u^4 - 1/25 * u^5)
        = u^2 * (1 - u * (u + 73/100) * (67/100 + 3/100 * u - 1/25 * u^2)) := by ring
    have hpos : 0 < u^2 * (1 - u * (u + 73/100) * (67/100 + 3/100 * u - 1/25 * u^2)) := by
      apply mul_pos hu2; linarith
    nlinarith [key, hpos]
  kappa_pos := by norm_num
  assumption1 := by
    intro p hp
    rw [deriv_dd (by linarith [hp.2]), dd_low (by norm_num)]
    unfold P P1
    nlinarith [sq_nonneg ((p - 73/100) * (p - 73/100 - 3/10)), sq_nonneg (p - 73/100)]
  K1_bound := by
    intro k hk p hp
    have hx : p < 11/5 := by linarith [hp.2]
    rw [iter_eq k p hx]
    have hl : -173/100 ≤ p - 73/100 := by linarith [hp.1]
    have hr : p - 73/100 ≤ 127/100 := by linarith [hp.2]
    have ha : 0 ≤ p - 73/100 + 173/100 := by linarith
    have hb : 0 ≤ 127/100 - (p - 73/100) := by linarith
    interval_cases k
    · simp only [iteratedDeriv_zero]
      apply abs_bound_aux <;> unfold P <;>
        nlinarith [mul_nonneg ha hb, mul_nonneg (mul_nonneg ha hb) ha,
          mul_nonneg (mul_nonneg ha hb) hb, mul_nonneg (mul_nonneg (mul_nonneg ha hb) ha) hb,
          mul_nonneg (mul_nonneg (mul_nonneg ha hb) ha) ha,
          mul_nonneg (mul_nonneg (mul_nonneg ha hb) hb) hb]
    · rw [iter1]
      apply abs_bound_aux <;> unfold P1 <;>
        nlinarith [mul_nonneg ha hb, mul_nonneg (mul_nonneg ha hb) ha,
          mul_nonneg (mul_nonneg ha hb) hb, mul_nonneg (mul_nonneg (mul_nonneg ha hb) ha) hb,
          mul_nonneg (mul_nonneg (mul_nonneg ha hb) ha) ha,
          mul_nonneg (mul_nonneg (mul_nonneg ha hb) hb) hb]
    · rw [iter2]
      apply abs_bound_aux <;> unfold P2 <;>
        nlinarith [mul_nonneg ha hb, mul_nonneg (mul_nonneg ha hb) ha,
          mul_nonneg (mul_nonneg ha hb) hb]
    · rw [iter3]
      apply abs_bound_aux <;> unfold P3 <;>
        nlinarith [mul_nonneg ha hb, sq_nonneg (p - 73/100 - 3/20)]
  c_pos := by norm_num
  gradient := by
    rw [deriv_dd (by norm_num)]
    unfold P1; norm_num [abs_of_neg]
  rho_pos := by norm_num
  mu_ge := by unfold Mconst; norm_num
  mu_lt := by norm_num

/-! ## D2: generic mechanics -/

lemma cont_obj (Δ q a yL yM1 yM2 yH : ℝ) :
    Continuous (fun p => p * dest Δ q a yL yM1 yM2 yH p) := by
  unfold dest
  refine continuous_id'.mul ?_
  refine Continuous.if_le ?_ ?_ continuous_id' continuous_const ?_
  · fun_prop
  · fun_prop
  · intro x hx
    rw [hx]; ring

lemma est_mem (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (hsel : IsArgmaxSelector amax)
    (Δ q a yL yM1 yM2 yH : ℝ) (hΔ : 0 ≤ Δ) :
    estimate amax Δ q a yL yM1 yM2 yH ∈ Set.Icc (q - Δ) (q + Δ) :=
  (hsel _ _ _ (by linarith) (cont_obj Δ q a yL yM1 yM2 yH).continuousOn).1

lemma est_eq (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (hsel : IsArgmaxSelector amax)
    (Δ q a yL yM1 yM2 yH m : ℝ) (hΔ : 0 ≤ Δ) (hm : m ∈ Set.Icc (q - Δ) (q + Δ))
    (hs : ∀ x ∈ Set.Icc (q - Δ) (q + Δ), x ≠ m →
      x * dest Δ q a yL yM1 yM2 yH x < m * dest Δ q a yL yM1 yM2 yH m) :
    estimate amax Δ q a yL yM1 yM2 yH = m := by
  obtain ⟨h1, h2⟩ := hsel (fun p => p * dest Δ q a yL yM1 yM2 yH p) (q - Δ) (q + Δ)
    (by linarith) (cont_obj Δ q a yL yM1 yM2 yH).continuousOn
  unfold estimate
  by_contra hne
  have h3 := hs _ h1 hne
  have h4 := h2 m hm
  linarith

lemma right_wins (q Δ a sL sR : ℝ) (hΔ : 0 < Δ) (h1 : 0 < a + sR * (q + Δ))
    (h2 : 0 < a - sR * q + 2 * sR * (q + Δ))
    (hL : ∀ x, q - Δ ≤ x → x ≤ q → x * (a + sL * (x - q)) < (q + Δ) * (a + sR * Δ)) :
    ∀ x ∈ Set.Icc (q - Δ) (q + Δ), x ≠ q + Δ →
      x * (if x ≤ q then a + sL * (x - q) else a + sR * (x - q)) <
        (q + Δ) * (if q + Δ ≤ q then a + sL * (q + Δ - q) else a + sR * (q + Δ - q)) := by
  intro x hx hne
  rw [if_neg (show ¬ (q + Δ ≤ q) by linarith)]
  have e : q + Δ - q = Δ := by ring
  rw [e]
  split_ifs with h
  · exact hL x hx.1 h
  · push_neg at h
    have hxz : x < q + Δ := lt_of_le_of_ne hx.2 hne
    have key : Δ * (a - sR * q + sR * (q + Δ + x)) =
        (q + Δ - x) * (a + sR * (q + Δ)) + (x - q) * (a - sR * q + 2 * sR * (q + Δ)) := by ring
    have hpos : 0 < a - sR * q + sR * (q + Δ + x) := by
      have h5 : 0 < Δ * (a - sR * q + sR * (q + Δ + x)) := by
        rw [key]; nlinarith [mul_pos (sub_pos.2 hxz) h1, mul_nonneg (sub_nonneg.2 h.le) h2.le]
      by_contra hc
      push_neg at hc
      nlinarith
    have e2 : (q + Δ) * (a + sR * Δ) - x * (a + sR * (x - q)) =
        (q + Δ - x) * (a - sR * q + sR * (q + Δ + x)) := by ring
    nlinarith [mul_pos (sub_pos.2 hxz) hpos]

lemma Delta_succ (μ : ℝ) (i : ℕ) : Delta μ (i + 2) = μ * Delta μ (i + 1) ^ 2 := rfl

lemma Delta_pos {μ : ℝ} (hμ : 0 < μ) : ∀ i, 0 < Delta μ i
  | 0 => by norm_num [Delta]
  | 1 => by norm_num [Delta]
  | (i + 2) => by rw [Delta_succ]; have := Delta_pos hμ (i + 1); positivity

lemma nRound_pos {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) {T : ℕ} (hT : 3 ≤ T) (i : ℕ) :
    0 < nRound μ ρ T i := by
  unfold nRound
  apply Nat.ceil_pos.2
  have hL : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have := Delta_pos hμ i
  positivity

lemma rs_succ (μ ρ : ℝ) (T i : ℕ) (hi : 1 ≤ i) :
    roundStart μ ρ T (i + 1) = roundStart μ ρ T i + 3 * nRound μ ρ T i := by
  unfold roundStart; rw [Finset.sum_Ico_succ_top hi]; ring

lemma rs_mono (μ ρ : ℝ) (T : ℕ) : Monotone (roundStart μ ρ T) := by
  intro a b hab
  unfold roundStart
  apply Nat.mul_le_mul_left
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right hab)

lemma sumM (d : ℝ → ℝ) (ε : ℕ → ℝ) (q Δ E : ℝ) (s n : ℕ) (hn : 0 < n)
    (hε : ∀ t, s + n ≤ t → t < s + 2 * n → ε t = E) :
    (1 / (n : ℝ)) * ∑ t ∈ Finset.Ico (s + n) (s + 2 * n), (d (blockPrice q Δ s n t) + ε t)
      = d q + E := by
  rw [Finset.sum_congr rfl (g := fun _ => d q + E)]
  · rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, show s + 2 * n - (s + n) = n by omega]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  · intro t ht
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 ht
    rw [blockPrice, if_neg (show ¬ t < s + n by omega), if_pos h2, hε t h1 h2]

lemma roundUpdate_const (d : ℝ → ℝ) (ε : ℕ → ℝ) (μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (T i : ℕ) (q E : ℝ) (hn : 0 < nRound μ ρ T i)
    (hs : sel i = (roundStart μ ρ T i, roundStart μ ρ T i + nRound μ ρ T i,
      roundStart μ ρ T i + nRound μ ρ T i, roundStart μ ρ T i + 2 * nRound μ ρ T i))
    (hε : ∀ t, roundStart μ ρ T i ≤ t → t < roundStart μ ρ T i + 3 * nRound μ ρ T i → ε t = E) :
    roundUpdate (fun p t => d p + ε t) μ ρ amax sel T i q =
      estimate amax (Delta μ i) q (d q + E) (d (q - Delta μ i) + E) (d q + E) (d q + E)
        (d (q + Delta μ i) + E) := by
  simp only [roundUpdate, hs]
  rw [sumM d ε q (Delta μ i) E _ _ hn (fun t h1 h2 => hε t (by omega) (by omega))]
  rw [blockPrice, if_pos (by omega), blockPrice, if_neg (by omega), if_pos (by omega),
    blockPrice, if_neg (by omega), if_neg (by omega)]
  rw [hε _ le_rfl (by omega), hε _ (by omega) (by omega), hε _ (by omega) (by omega)]

lemma centre_succ (d : ℝ → ℝ) (μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T i : ℕ) (hi : 1 ≤ i) :
    centre d μ ρ amax sel ε T (i + 1) =
      roundUpdate (fun p t => d p + ε t) μ ρ amax sel T i (centre d μ ρ amax sel ε T i) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rfl

/-! ## D4: noise and pair selector of the counterexample -/

noncomputable def epsI (T : ℕ) (t : ℕ) : ℝ :=
  if t < roundStart (15/8) 20 T 2 then 1/1600
  else if t < roundStart (15/8) 20 T 3 then 9/16384 else 0

noncomputable def selI (T : ℕ) (i : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (roundStart (15/8) 20 T i, roundStart (15/8) 20 T i + nRound (15/8) 20 T i,
    roundStart (15/8) 20 T i + nRound (15/8) 20 T i,
    roundStart (15/8) 20 T i + 2 * nRound (15/8) 20 T i)

noncomputable def Eof (i : ℕ) : ℝ := if i = 1 then 1/1600 else if i = 2 then 9/16384 else 0

lemma eps_round (T : ℕ) (i : ℕ) (hi : 1 ≤ i) (t : ℕ)
    (h1 : roundStart (15/8) 20 T i ≤ t)
    (h2 : t < roundStart (15/8) 20 T i + 3 * nRound (15/8) 20 T i) :
    epsI T t = Eof i := by
  have m23 := rs_mono (15/8 : ℝ) 20 T (show 2 ≤ 3 by norm_num)
  unfold epsI Eof
  rcases (show i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with h | h | h
  · subst h
    have hs := rs_succ (15/8 : ℝ) 20 T 1 le_rfl
    norm_num at hs
    rw [if_pos (by omega), if_pos rfl]
  · subst h
    have hs := rs_succ (15/8 : ℝ) 20 T 2 (by norm_num)
    norm_num at hs
    rw [if_neg (by omega), if_pos (by omega), if_neg (by norm_num), if_pos rfl]
  · have m3 := rs_mono (15/8 : ℝ) 20 T h
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma D1v : Delta (15/8) 1 = 1/2 := rfl
lemma D2v : Delta (15/8) 2 = 15/32 := by
  rw [show Delta (15/8) 2 = 15/8 * Delta (15/8) 1 ^ 2 from rfl, D1v]; norm_num
lemma D3v : Delta (15/8) 3 = 3375/8192 := by
  rw [show Delta (15/8) 3 = 15/8 * Delta (15/8) 2 ^ 2 from rfl, D2v]; norm_num
lemma D4v : Delta (15/8) 4 = 170859375/536870912 := by
  rw [show Delta (15/8) 4 = 15/8 * Delta (15/8) 3 ^ 2 from rfl, D3v]; norm_num
lemma D5v : Delta (15/8) 5 = D5 := by
  rw [show Delta (15/8) 5 = 15/8 * Delta (15/8) 4 ^ 2 from rfl, D4v]; unfold D5; norm_num

lemma A2_holds (T : ℕ) (hT : 3 ≤ T) : Assumption2 (15/8) 20 T (selI T) (epsI T) := by
  intro i hi _
  have hn := nRound_pos (μ := 15/8) (ρ := 20) (by norm_num) (by norm_num) hT i
  unfold Assumption2At
  simp only [selI]
  refine ⟨⟨le_rfl, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
    ?_, ?_⟩
  · rw [eps_round T i hi _ le_rfl (by omega), eps_round T i hi _ (by omega) (by omega)]
  · rw [eps_round T i hi _ (by omega) (by omega), eps_round T i hi _ (by omega) (by omega)]

lemma conc_holds (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (T : ℕ) (hT : 3 ≤ T) :
    Concentration dd (15/8) 20 amax (selI T) (epsI T) T := by
  intro i hi _
  have hn := nRound_pos (μ := 15/8) (ρ := 20) (by norm_num) (by norm_num) hT i
  unfold ConcentrationAt avgM roundObs pM
  rw [sumM dd (epsI T) _ _ (Eof i) _ _ hn
    (fun t h1 h2 => eps_round T i hi t (by omega) (by omega))]
  rw [add_sub_cancel_left]
  unfold Eof
  split_ifs with h1 h2
  · subst h1; rw [D1v]; norm_num
  · subst h2; rw [D2v]; norm_num
  · have := Delta_pos (μ := (15/8 : ℝ)) (by norm_num) i
    simp only [abs_zero]; positivity

/-! ## D5: rounds 1-4 pick the right endpoint -/

lemma step (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (T : ℕ) (hT : 3 ≤ T) (i : ℕ) (hi : 1 ≤ i) (q : ℝ)
    (hq : centre dd (15/8) 20 amax (selI T) (epsI T) T i = q) :
    centre dd (15/8) 20 amax (selI T) (epsI T) T (i + 1) =
      estimate amax (Delta (15/8) i) q (dd q + Eof i) (dd (q - Delta (15/8) i) + Eof i)
        (dd q + Eof i) (dd q + Eof i) (dd (q + Delta (15/8) i) + Eof i) := by
  rw [centre_succ _ _ _ _ _ _ _ _ hi, hq]
  exact roundUpdate_const dd (epsI T) (15/8) 20 amax (selI T) T i q (Eof i)
    (nRound_pos (by norm_num) (by norm_num) hT i) rfl (fun t h1 h2 => eps_round T i hi t h1 h2)

lemma round_right (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (hsel : IsArgmaxSelector amax) (T : ℕ)
    (hT : 3 ≤ T) (k : ℕ) (hk : 1 ≤ k) (q Δ E pl pm ph : ℝ)
    (hq : centre dd (15/8) 20 amax (selI T) (epsI T) T k = q) (hΔ : Delta (15/8) k = Δ)
    (hE : Eof k = E) (hpl : dd (q - Δ) = pl) (hpm : dd q = pm) (hph : dd (q + Δ) = ph)
    (hΔ0 : 0 < Δ)
    (h1 : 0 < (pm + E) + (ph + E - (pm + E)) / Δ * (q + Δ))
    (h2 : 0 < (pm + E) - (ph + E - (pm + E)) / Δ * q + 2 * ((ph + E - (pm + E)) / Δ) * (q + Δ))
    (hL : ∀ x, q - Δ ≤ x → x ≤ q → x * ((pm + E) + (pm + E - (pl + E)) / Δ * (x - q)) <
      (q + Δ) * ((pm + E) + (ph + E - (pm + E)) / Δ * Δ)) :
    centre dd (15/8) 20 amax (selI T) (epsI T) T (k + 1) = q + Δ := by
  rw [step amax T hT k hk q hq, hΔ, hE, hpl, hpm, hph]
  apply est_eq amax hsel _ _ _ _ _ _ _ _ hΔ0.le ⟨by linarith, le_rfl⟩
  intro x hx hne
  unfold dest
  exact right_wins q Δ (pm + E) _ _ hΔ0 h1 h2 hL x hx hne

lemma cI2 (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (hsel : IsArgmaxSelector amax) (T : ℕ) (hT : 3 ≤ T) :
    centre dd (15/8) 20 amax (selI T) (epsI T) T 2 = (1 : ℝ) := by
  have h := round_right amax hsel T hT 1 (by norm_num) (1/2 : ℝ) (1/2 : ℝ) (1/1600 : ℝ) (38005324021/25000000000000 : ℝ) (118994725959/100000000000000 : ℝ) (29580602917/50000000000000 : ℝ)
    (rfl) (by rw [D1v]; try norm_num) (by norm_num [Eof])
    (by rw [dd_low (by norm_num)]; unfold P; norm_num) (by rw [dd_low (by norm_num)]; unfold P; norm_num)
    (by rw [dd_low (by norm_num)]; unfold P; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro x hx1 hx2; nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hx2), sq_nonneg (x - (16239/10000 : ℝ))])
  rw [h]; norm_num

lemma cI3 (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (hsel : IsArgmaxSelector amax) (T : ℕ) (hT : 3 ≤ T) :
    centre dd (15/8) 20 amax (selI T) (epsI T) T 3 = (47/32 : ℝ) := by
  have h := round_right amax hsel T hT 2 (by norm_num) (1 : ℝ) (15/32 : ℝ) (9/16384 : ℝ) (7565714140001399/6553600000000000000 : ℝ) (29580602917/50000000000000 : ℝ) (2142294736072649/6553600000000000000 : ℝ)
    (cI2 amax hsel T hT) (by rw [D2v]; try norm_num) (by norm_num [Eof])
    (by rw [dd_low (by norm_num)]; unfold P; norm_num) (by rw [dd_low (by norm_num)]; unfold P; norm_num)
    (by rw [dd_low (by norm_num)]; unfold P; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro x hx1 hx2; nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hx2), sq_nonneg (x - (9751/10000 : ℝ))])
  rw [h]; norm_num

lemma cI4 (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (hsel : IsArgmaxSelector amax) (T : ℕ) (hT : 3 ≤ T) :
    centre dd (15/8) 20 amax (selI T) (epsI T) T 4 = (15407/8192 : ℝ) := by
  have h := round_right amax hsel T hT 3 (by norm_num) (47/32 : ℝ) (3375/8192 : ℝ) (0 : ℝ) (3844330471579357067684282999/7205759403792793600000000000000 : ℝ) (2142294736072649/6553600000000000000 : ℝ) (5153040978705008572080314249/7205759403792793600000000000000 : ℝ)
    (cI3 amax hsel T hT) (by rw [D3v]; try norm_num) (by norm_num [Eof])
    (by rw [dd_low (by norm_num)]; unfold P; norm_num) (by rw [dd_low (by norm_num)]; unfold P; norm_num)
    (by rw [dd_low (by norm_num)]; unfold P; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro x hx1 hx2; nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hx2), sq_nonneg (x - (10603/10000 : ℝ))])
  rw [h]; norm_num

lemma cI5 (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (hsel : IsArgmaxSelector amax) (T : ℕ) (hT : 3 ≤ T) :
    centre dd (15/8) 20 amax (selI T) (epsI T) T 5 = (1180572527/536870912 : ℝ) := by
  have h := round_right amax hsel T hT 4 (by norm_num) (15407/8192 : ℝ) (170859375/536870912 : ℝ) (0 : ℝ) (3075930248837578403501149887640781009150926280086199/8711228593176024664662389950253266213273600000000000000 : ℝ) (5153040978705008572080314249/7205759403792793600000000000000 : ℝ) (13621815786153142243342833885480313636690450362117449/8711228593176024664662389950253266213273600000000000000 : ℝ)
    (cI4 amax hsel T hT) (by rw [D4v]; try norm_num) (by norm_num [Eof])
    (by rw [dd_low (by norm_num)]; unfold P; norm_num) (by rw [dd_low (by norm_num)]; unfold P; norm_num)
    (by rw [dd_low (by norm_num)]; unfold P; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro x hx1 hx2; nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hx2), sq_nonneg (x - (313/500 : ℝ))])
  rw [h]; norm_num

/-! ## D5b: round 5 lands on the vertex `x5 + D5/2` -/

lemma vertex_wins (x5 D5 a pl b : ℝ) (hD : 0 < D5) (ha : 0 < a) (hlo0 : 0 < x5 - D5)
    (hpl : pl ≤ a) (hlo : (x5 - D5) * pl < x5 * a) (hb : b = a * x5 / (x5 + D5)) :
    ∀ x ∈ Set.Icc (x5 - D5) (x5 + D5), x ≠ x5 + D5 / 2 →
      x * (if x ≤ x5 then a + (a - pl) / D5 * (x - x5) else a + (b - a) / D5 * (x - x5)) <
        (x5 + D5 / 2) * (if x5 + D5 / 2 ≤ x5 then a + (a - pl) / D5 * (x5 + D5 / 2 - x5)
          else a + (b - a) / D5 * (x5 + D5 / 2 - x5)) := by
  intro x hx hne
  rw [if_neg (show ¬ (x5 + D5 / 2 ≤ x5) by linarith)]
  have hz : 0 < x5 + D5 := by linarith
  have hbv : (b - a) / D5 = -a / (x5 + D5) := by
    rw [hb]; field_simp; ring
  rw [hbv]
  have hfy : (x5 + D5 / 2) * (a + -a / (x5 + D5) * (x5 + D5 / 2 - x5)) =
      a * (x5 + D5 / 2) ^ 2 / (x5 + D5) := by
    field_simp; ring
  rw [hfy]
  split_ifs with h
  · set s := (a - pl) / D5 with hsdef
    have hs : s * D5 = a - pl := by rw [hsdef]; field_simp
    have e1 : D5 * (x * (a + s * (x - x5))) = (x5 - x) * ((x5 - D5) * pl) +
        (x - (x5 - D5)) * (x5 * a) + (a - pl) * (x - (x5 - D5)) * (x - x5) := by
      linear_combination (x * (x - x5)) * hs
    have h1 : (x5 - x) * ((x5 - D5) * pl) ≤ (x5 - x) * (x5 * a) :=
      mul_le_mul_of_nonneg_left hlo.le (by linarith)
    have h2 : (a - pl) * (x - (x5 - D5)) * (x - x5) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos
      · exact mul_nonneg (by linarith) (by linarith [hx.1])
      · linarith
    have h3 : x * (a + s * (x - x5)) ≤ x5 * a := by
      have : D5 * (x * (a + s * (x - x5))) ≤ D5 * (x5 * a) := by nlinarith
      exact le_of_mul_le_mul_left this hD
    have h4 : x5 * a < a * (x5 + D5 / 2) ^ 2 / (x5 + D5) := by
      rw [lt_div_iff₀ hz]; nlinarith [mul_pos ha (mul_pos hD hD)]
    linarith
  · push_neg at h
    have hxy : x - (x5 + D5 / 2) ≠ 0 := sub_ne_zero.2 hne
    have e2 : a * (x5 + D5 / 2) ^ 2 / (x5 + D5) - x * (a + -a / (x5 + D5) * (x - x5)) =
        a / (x5 + D5) * (x - (x5 + D5 / 2)) ^ 2 := by
      field_simp; ring
    have : 0 < a / (x5 + D5) * (x - (x5 + D5 / 2)) ^ 2 :=
      mul_pos (div_pos ha hz) (by positivity)
    linarith

lemma cI6 (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (hsel : IsArgmaxSelector amax) (T : ℕ) (hT : 3 ≤ T) :
    centre dd (15/8) 20 amax (selI T) (epsI T) T 6 = x5 + D5 / 2 := by
  have h := step amax T hT 5 (by norm_num) x5 (by rw [cI5 amax hsel T hT]; rfl)
  rw [D5v, show Eof 5 = 0 by norm_num [Eof]] at h
  simp only [add_zero] at h
  have hD : (0 : ℝ) < D5 := by unfold D5; norm_num
  rw [h, dd_low (p := x5 - D5) (by unfold x5 D5; norm_num), dd_low (p := x5) (by unfold x5; norm_num),
    show x5 + D5 = z5 from rfl, dd_z5]
  apply est_eq amax hsel _ _ _ _ _ _ _ _ hD.le ⟨by linarith, by linarith⟩
  intro x hx hne
  unfold dest
  refine vertex_wins x5 D5 (1/800 * P x5) (1/800 * P (x5 - D5)) (1/800 * B5) hD
    (by unfold P x5; norm_num) (by unfold x5 D5; norm_num) (by unfold P x5 D5; norm_num)
    (by unfold P x5 D5; norm_num) (by unfold B5 z5; ring) x ?_ hne
  exact hx

/-! ## D6: the trap after round 6 -/

noncomputable def yv : ℝ := x5 + D5 / 2

lemma D6le : Delta (15/8) 6 ≤ 677/10000 := by
  rw [show Delta (15/8) 6 = 15/8 * Delta (15/8) 5 ^ 2 from rfl, D5v]; unfold D5; norm_num

lemma roundUpdate_mem (Yfn : ℝ → ℕ → ℝ) (μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (hsel : IsArgmaxSelector amax) (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (T i : ℕ) (q : ℝ)
    (hΔ : 0 ≤ Delta μ i) :
    roundUpdate Yfn μ ρ amax sel T i q ∈ Set.Icc (q - Delta μ i) (q + Delta μ i) := by
  unfold roundUpdate
  exact est_mem amax hsel _ _ _ _ _ _ _ hΔ

lemma trap (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (hsel : IsArgmaxSelector amax) (T : ℕ) (hT : 3 ≤ T) :
    ∀ k, 6 ≤ k → Delta (15/8) k ≤ 677/10000 ∧
      |centre dd (15/8) 20 amax (selI T) (epsI T) T k - yv| + 6/5 * Delta (15/8) k
        ≤ 6/5 * (677/10000) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨D6le, ?_⟩
    rw [cI6 amax hsel T hT]
    unfold yv
    simp only [sub_self, abs_zero, zero_add]
    linarith [D6le]
  | succ k hk ih =>
    obtain ⟨h1, h2⟩ := ih
    have hpos := Delta_pos (μ := (15/8:ℝ)) (by norm_num) k
    have hs : Delta (15/8) (k+1) = 15/8 * Delta (15/8) k ^ 2 := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rfl
    have hm : centre dd (15/8) 20 amax (selI T) (epsI T) T (k+1) ∈ Set.Icc
        (centre dd (15/8) 20 amax (selI T) (epsI T) T k - Delta (15/8) k)
        (centre dd (15/8) 20 amax (selI T) (epsI T) T k + Delta (15/8) k) := by
      rw [centre_succ dd (15/8) 20 amax (selI T) (epsI T) T k (by omega)]
      exact roundUpdate_mem _ _ _ amax hsel _ _ _ _ hpos.le
    have h3 : |centre dd (15/8) 20 amax (selI T) (epsI T) T (k+1)
        - centre dd (15/8) 20 amax (selI T) (epsI T) T k| ≤ Delta (15/8) k :=
      abs_le.2 ⟨by linarith [hm.1], by linarith [hm.2]⟩
    have h4 := abs_sub_le (centre dd (15/8) 20 amax (selI T) (epsI T) T (k+1))
      (centre dd (15/8) 20 amax (selI T) (epsI T) T k) yv
    rw [hs]
    have h5 := mul_le_mul_of_nonneg_left h1 hpos.le
    constructor
    · nlinarith
    · nlinarith

lemma trap_price (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (hsel : IsArgmaxSelector amax) (T : ℕ)
    (hT : 3 ≤ T) (k : ℕ) (hk : 6 ≤ k) (p : ℝ)
    (hp : p ∈ Set.Icc (centre dd (15/8) 20 amax (selI T) (epsI T) T k - Delta (15/8) k)
      (centre dd (15/8) 20 amax (selI T) (epsI T) T k + Delta (15/8) k)) :
    2212/1000 ≤ p ∧ p ≤ 2376/1000 := by
  obtain ⟨_, h2⟩ := trap amax hsel T hT k hk
  have hpos := Delta_pos (μ := (15/8:ℝ)) (by norm_num) k
  have hy1 : (2212/1000 : ℝ) + 6/5 * (677/10000) ≤ yv := by unfold yv x5 D5; norm_num
  have hy2 : yv + 6/5 * (677/10000) ≤ 2376/1000 := by unfold yv x5 D5; norm_num
  have ha := neg_abs_le (centre dd (15/8) 20 amax (selI T) (epsI T) T k - yv)
  have hb := le_abs_self (centre dd (15/8) 20 amax (selI T) (epsI T) T k - yv)
  constructor
  · linarith [hp.1]
  · linarith [hp.2]

lemma dd_trap_nonpos {p : ℝ} (h1 : 2212/1000 ≤ p) (h2 : p ≤ 2376/1000) : dd p ≤ 0 := by
  unfold dd
  rw [expNegInvGlue.zero_of_nonpos (show p - 119/50 ≤ 0 by linarith), mul_zero, add_zero]
  have hg : 3 ≤ H2 * expNegInvGlue (p - 11/5) := by
    have hmono : expNegInvGlue (3/250) ≤ expNegInvGlue (p - 11/5) :=
      expNegInvGlue.monotone (by linarith)
    have hv : expNegInvGlue (3/250) = Real.exp (-(250/3)) := by
      unfold expNegInvGlue; rw [if_neg (by norm_num)]; norm_num
    rw [hv] at hmono
    have he : Real.exp (-100) ≤ Real.exp (-(250/3)) := Real.exp_le_exp.2 (by norm_num)
    have h1 : H2 * Real.exp (-100) = 3 := by
      unfold H2; rw [mul_assoc, ← Real.exp_add]; norm_num
    have hH : 0 ≤ H2 := by unfold H2; positivity
    nlinarith [mul_le_mul_of_nonneg_left (he.trans hmono) hH]
  have hP : P p ≤ 3 := by
    unfold P
    have hu1 : 1482/1000 ≤ p - 73/100 := by linarith
    have hu2 : p - 73/100 ≤ 33/20 := by linarith
    have hu0 : 0 ≤ p - 73/100 := by linarith
    have e3 : (p - 73/100)^3 ≤ (33/20)^3 := pow_le_pow_left₀ hu0 hu2 3
    have e4 : (p - 73/100)^4 ≤ (33/20)^4 := pow_le_pow_left₀ hu0 hu2 4
    have e5 : 0 ≤ (p - 73/100)^5 := by positivity
    nlinarith
  linarith

/-! ## D7: prices and the regret lower bound -/

lemma blockPrice_mem (q Δ : ℝ) (s n t : ℕ) (hΔ : 0 ≤ Δ) :
    blockPrice q Δ s n t ∈ Set.Icc (q - Δ) (q + Δ) := by
  unfold blockPrice
  split_ifs <;> constructor <;> linarith

lemma price_mem_round (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (T t : ℕ) :
    price dd (15/8) 20 amax (selI T) (epsI T) T t ∈ Set.Icc
      (centre dd (15/8) 20 amax (selI T) (epsI T) T (roundOf (15/8) 20 T t)
        - Delta (15/8) (roundOf (15/8) 20 T t))
      (centre dd (15/8) 20 amax (selI T) (epsI T) T (roundOf (15/8) 20 T t)
        + Delta (15/8) (roundOf (15/8) 20 T t)) :=
  blockPrice_mem _ _ _ _ _ (Delta_pos (by norm_num) _).le

lemma rs1 (T : ℕ) : roundStart (15/8) 20 T 1 = 0 := by simp [roundStart]

lemma rs6_eq (T : ℕ) : roundStart (15/8) 20 T 6 = 3 * (nRound (15/8) 20 T 1 + nRound (15/8) 20 T 2
    + nRound (15/8) 20 T 3 + nRound (15/8) 20 T 4 + nRound (15/8) 20 T 5) := by
  have h5 := rs_succ (15/8:ℝ) 20 T 5 (by norm_num)
  have h4 := rs_succ (15/8:ℝ) 20 T 4 (by norm_num)
  have h3 := rs_succ (15/8:ℝ) 20 T 3 (by norm_num)
  have h2 := rs_succ (15/8:ℝ) 20 T 2 (by norm_num)
  have h1 := rs_succ (15/8:ℝ) 20 T 1 le_rfl
  have h0 := rs1 T
  norm_num at h1 h2 h3 h4 h5
  omega

lemma rs6_ge (T : ℕ) (hT : 3 ≤ T) : 15 ≤ roundStart (15/8) 20 T 6 := by
  rw [rs6_eq]
  have := nRound_pos (μ := (15/8:ℝ)) (ρ := 20) (by norm_num) (by norm_num) hT 1
  have := nRound_pos (μ := (15/8:ℝ)) (ρ := 20) (by norm_num) (by norm_num) hT 2
  have := nRound_pos (μ := (15/8:ℝ)) (ρ := 20) (by norm_num) (by norm_num) hT 3
  have := nRound_pos (μ := (15/8:ℝ)) (ρ := 20) (by norm_num) (by norm_num) hT 4
  have := nRound_pos (μ := (15/8:ℝ)) (ρ := 20) (by norm_num) (by norm_num) hT 5
  omega

lemma price_bd (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (hsel : IsArgmaxSelector amax) (T : ℕ)
    (hT : 3 ≤ T) (t : ℕ) :
    price dd (15/8) 20 amax (selI T) (epsI T) T t ∈ Set.Icc (0:ℝ) (5/2) := by
  have hm := price_mem_round amax T t
  generalize price dd (15/8) 20 amax (selI T) (epsI T) T t = p at hm ⊢
  generalize roundOf (15/8) 20 T t = k at hm
  rcases (show k ≤ 5 ∨ 6 ≤ k by omega) with hk | hk
  · interval_cases k
    · have e1 : centre dd (15/8) 20 amax (selI T) (epsI T) T 0 = 1/2 := rfl
      have e2 : Delta (15/8) 0 = 1/2 := rfl
      rw [e1, e2] at hm; constructor <;> linarith [hm.1, hm.2]
    · have e1 : centre dd (15/8) 20 amax (selI T) (epsI T) T 1 = 1/2 := rfl
      rw [e1, D1v] at hm; constructor <;> linarith [hm.1, hm.2]
    · rw [cI2 amax hsel T hT, D2v] at hm; constructor <;> linarith [hm.1, hm.2]
    · rw [cI3 amax hsel T hT, D3v] at hm; constructor <;> linarith [hm.1, hm.2]
    · rw [cI4 amax hsel T hT, D4v] at hm; constructor <;> linarith [hm.1, hm.2]
    · rw [cI5 amax hsel T hT, D5v] at hm; unfold D5 at hm; constructor <;> linarith [hm.1, hm.2]
  · have := trap_price amax hsel T hT k hk p hm
    constructor <;> linarith [this.1, this.2]

lemma price_trap (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (hsel : IsArgmaxSelector amax) (T : ℕ)
    (hT : 3 ≤ T) (t : ℕ) (ht : roundStart (15/8) 20 T 6 ≤ t) :
    2212/1000 ≤ price dd (15/8) 20 amax (selI T) (epsI T) T t ∧
      price dd (15/8) 20 amax (selI T) (epsI T) T t ≤ 2376/1000 := by
  have h15 := rs6_ge T hT
  have hk : 6 ≤ roundOf (15/8) 20 T t := by
    unfold roundOf; exact Nat.le_findGreatest (by omega) ht
  exact trap_price amax hsel T hT _ hk _ (price_mem_round amax T t)

noncomputable def amaxI (f : ℝ → ℝ) (a b : ℝ) : ℝ := by
  classical
  exact if h : a ≤ b ∧ ContinuousOn f (Set.Icc a b) then
    Classical.choose (isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 h.1) h.2) else a

lemma amaxI_sel : IsArgmaxSelector amaxI := by
  intro f a b hab hf
  have h : a ≤ b ∧ ContinuousOn f (Set.Icc a b) := ⟨hab, hf⟩
  unfold amaxI
  rw [dif_pos h]
  obtain ⟨h1, h2⟩ :=
    Classical.choose_spec (isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 h.1) h.2)
  exact ⟨h1, fun x hx => isMaxOn_iff.1 h2 x hx⟩

lemma r_bound : ∃ B, ∀ x ∈ Set.Icc (0:ℝ) (5/2), ‖r dd x‖ ≤ B :=
  isCompact_Icc.exists_bound_of_continuousOn
    ((continuous_id.mul dd_contDiff.continuous).continuousOn)

lemma rstar_pos : 0 < r dd (73/100) := by
  unfold r; rw [dd_low (by norm_num)]; unfold P; norm_num

lemma regret_ge (T : ℕ) (hT : 3 ≤ T) (B : ℝ) (hB : ∀ x ∈ Set.Icc (0:ℝ) (5/2), ‖r dd x‖ ≤ B) :
    (T:ℝ) * r dd (73/100) - (r dd (73/100) + B) * (roundStart (15/8) 20 T 6 : ℝ) ≤
      regret dd (73/100) (15/8) 20 amaxI (selI T) (epsI T) T := by
  have hr0 := rstar_pos
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, by norm_num⟩)
  unfold regret
  have key : ∀ t ∈ Finset.range T, r dd (73/100) - (r dd (73/100) + B) *
      (if t < roundStart (15/8) 20 T 6 then (1:ℝ) else 0) ≤
      r dd (73/100) - r dd (price dd (15/8) 20 amaxI (selI T) (epsI T) T t) := by
    intro t _
    have hb := price_bd amaxI amaxI_sel T hT t
    split_ifs with h
    · have h1 := hB _ hb
      rw [Real.norm_eq_abs] at h1
      have h2 := le_abs_self (r dd (price dd (15/8) 20 amaxI (selI T) (epsI T) T t))
      linarith
    · push_neg at h
      have ht := price_trap amaxI amaxI_sel T hT t h
      have h3 := dd_trap_nonpos ht.1 ht.2
      have h4 : r dd (price dd (15/8) 20 amaxI (selI T) (epsI T) T t) ≤ 0 := by
        unfold r; exact mul_nonpos_of_nonneg_of_nonpos hb.1 h3
      linarith
  refine le_trans ?_ (Finset.sum_le_sum key)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Finset.sum_boole]
  have hc : (((Finset.range T).filter (fun t => t < roundStart (15/8) 20 T 6)).card : ℝ) ≤
      roundStart (15/8) 20 T 6 := by
    have : ((Finset.range T).filter (fun t => t < roundStart (15/8) 20 T 6)).card ≤
        roundStart (15/8) 20 T 6 := by
      refine (Finset.card_le_card (t := Finset.range (roundStart (15/8) 20 T 6)) ?_).trans
        (Finset.card_range _).le
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
      exact hx.2
    exact_mod_cast this
  have hrB : 0 ≤ r dd (73/100) + B := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hc hrB]

/-! ## D8: schedule length and asymptotics -/

lemma nRound_le (T i : ℕ) (hT : 3 ≤ T) :
    (nRound (15/8) 20 T i : ℝ) ≤ 2 * 20^4 * Real.log T / Delta (15/8) i ^ 4 + 1 := by
  unfold nRound
  have hL : 0 ≤ Real.log (T:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ T))
  have := Delta_pos (μ := (15/8:ℝ)) (by norm_num) i
  exact (Nat.ceil_lt_add_one (by positivity)).le

noncomputable def Acon : ℝ := 3 * (2 * 20^4 / Delta (15/8) 1 ^ 4 + 2 * 20^4 / Delta (15/8) 2 ^ 4
  + 2 * 20^4 / Delta (15/8) 3 ^ 4 + 2 * 20^4 / Delta (15/8) 4 ^ 4 + 2 * 20^4 / Delta (15/8) 5 ^ 4)

lemma Acon_nonneg : 0 ≤ Acon := by unfold Acon; positivity

lemma rs6_le (T : ℕ) (hT : 3 ≤ T) :
    (roundStart (15/8) 20 T 6 : ℝ) ≤ 15 + Acon * Real.log T := by
  rw [rs6_eq]; push_cast
  have h1 := nRound_le T 1 hT
  have h2 := nRound_le T 2 hT
  have h3 := nRound_le T 3 hT
  have h4 := nRound_le T 4 hT
  have h5 := nRound_le T 5 hT
  have e : Acon * Real.log T = 3 * (2 * 20^4 * Real.log T / Delta (15/8) 1 ^ 4
      + 2 * 20^4 * Real.log T / Delta (15/8) 2 ^ 4 + 2 * 20^4 * Real.log T / Delta (15/8) 3 ^ 4
      + 2 * 20^4 * Real.log T / Delta (15/8) 4 ^ 4
      + 2 * 20^4 * Real.log T / Delta (15/8) 5 ^ 4) := by
    unfold Acon; ring
  rw [e]; linarith

lemma asym (a M B A : ℝ) (ha : 0 < a) (hM : 0 ≤ M) (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ N : ℕ, 2 ≤ N ∧ M * (N:ℝ)^6 + B * (15 + A * (8 * N)) < a * (N:ℝ)^8 := by
  refine ⟨⌈(M + 15 * B + 8 * A * B) / a + 1⌉₊ + 2, by omega, ?_⟩
  have hX := Nat.le_ceil ((M + 15 * B + 8 * A * B) / a + 1)
  generalize ⌈(M + 15 * B + 8 * A * B) / a + 1⌉₊ = m at hX
  push_cast
  generalize hn : (m:ℝ) + 2 = n
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hXn : (M + 15 * B + 8 * A * B) / a + 1 ≤ n := by linarith
  have hn2 : (2:ℝ) ≤ n := by linarith
  have haX : a * ((M + 15 * B + 8 * A * B) / a + 1) = M + 15 * B + 8 * A * B + a := by
    field_simp
  have h1 : (1:ℝ) ≤ n := by linarith
  have hn6 : 1 ≤ n^6 := one_le_pow₀ h1
  have hn_le : n ≤ n^6 := by
    calc n = n^1 := (pow_one n).symm
      _ ≤ n^6 := pow_le_pow_right₀ h1 (by norm_num)
  have hXn2 : (M + 15 * B + 8 * A * B) / a + 1 ≤ n^2 := by nlinarith
  have hn2' : ((M + 15 * B + 8 * A * B) / a + 1) * n^6 ≤ n^2 * n^6 :=
    mul_le_mul_of_nonneg_right hXn2 (by positivity)
  have step1 : a * ((M + 15 * B + 8 * A * B) / a + 1) * n^6 ≤ a * n^8 := by
    rw [show n^8 = n^2 * n^6 by ring, mul_assoc]
    exact mul_le_mul_of_nonneg_left hn2' ha.le
  rw [haX] at step1
  have hBn : B * 15 ≤ B * 15 * n^6 := le_mul_of_one_le_right (by positivity) hn6
  have hABn : A * B * n ≤ A * B * n^6 := mul_le_mul_of_nonneg_left hn_le (by positivity)
  have han : 0 < a * n^6 := by positivity
  nlinarith

lemma big (C1 C2 : ℝ) : ∃ T : ℕ, 3 ≤ T ∧
    (C1 + C2 * Real.log (Real.log (T:ℝ))) * Real.sqrt (T:ℝ) * Real.log (T:ℝ) <
      regret dd (73/100) (15/8) 20 amaxI (selI T) (epsI T) T := by
  obtain ⟨B0, hB0⟩ := r_bound
  have hB : 0 ≤ B0 := (norm_nonneg _).trans (hB0 0 ⟨le_rfl, by norm_num⟩)
  have hr := rstar_pos
  obtain ⟨N, hN2, hNb⟩ := asym (r dd (73/100)) (64 * (|C1| + |C2|)) (r dd (73/100) + B0) Acon hr
    (by positivity) (by linarith) Acon_nonneg
  have hT3 : 3 ≤ N^8 := by
    have : 2^8 ≤ N^8 := Nat.pow_le_pow_left hN2 8
    omega
  refine ⟨N^8, hT3, ?_⟩
  have hreg := regret_ge (N^8) hT3 B0 hB0
  have hrs := rs6_le (N^8) hT3
  push_cast at hreg hrs ⊢
  have hNr : (2:ℝ) ≤ N := by exact_mod_cast hN2
  have hlogT : Real.log ((N:ℝ)^8) = 8 * Real.log N := by rw [Real.log_pow]; norm_num
  have hlN : Real.log N ≤ N - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hl2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
  have hl2' := Real.log_two_gt_d9
  have hsq : Real.sqrt ((N:ℝ)^8) = (N:ℝ)^4 := by
    rw [show (N:ℝ)^8 = ((N:ℝ)^4)^2 by ring]; exact Real.sqrt_sq (by positivity)
  rw [hsq, hlogT]
  rw [hlogT] at hrs
  have hL1 : 1 < 8 * Real.log N := by linarith
  have hLL0 : 0 ≤ Real.log (8 * Real.log N) := Real.log_nonneg hL1.le
  have hLL : Real.log (8 * Real.log N) ≤ 8 * Real.log N - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hQ : C1 + C2 * Real.log (8 * Real.log N) ≤ |C1| + |C2| * (8 * N) := by
    have ha1 := le_abs_self C1
    have h3 : C2 * Real.log (8 * Real.log N) ≤ |C2| * Real.log (8 * Real.log N) :=
      mul_le_mul_of_nonneg_right (le_abs_self C2) hLL0
    have h4 : |C2| * Real.log (8 * Real.log N) ≤ |C2| * (8 * N) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    linarith
  have hlhs : (C1 + C2 * Real.log (8 * Real.log N)) * (N:ℝ)^4 * (8 * Real.log N) ≤
      64 * (|C1| + |C2|) * (N:ℝ)^6 := by
    have hpos : 0 ≤ (N:ℝ)^4 * (8 * Real.log N) := by positivity
    have hQ0 : 0 ≤ |C1| + |C2| * (8 * N) := by positivity
    calc (C1 + C2 * Real.log (8 * Real.log N)) * (N:ℝ)^4 * (8 * Real.log N)
        = (C1 + C2 * Real.log (8 * Real.log N)) * ((N:ℝ)^4 * (8 * Real.log N)) := by ring
      _ ≤ (|C1| + |C2| * (8 * N)) * ((N:ℝ)^4 * (8 * N)) :=
          mul_le_mul hQ (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hpos hQ0
      _ ≤ 64 * (|C1| + |C2|) * (N:ℝ)^6 := by
          have e : (|C1| + |C2| * (8 * N)) * ((N:ℝ)^4 * (8 * N)) =
              8 * |C1| * (N:ℝ)^5 + 64 * |C2| * (N:ℝ)^6 := by ring
          have h5 : (N:ℝ)^5 ≤ (N:ℝ)^6 := pow_le_pow_right₀ (by linarith) (by norm_num)
          rw [e]
          nlinarith [mul_le_mul_of_nonneg_left h5 (abs_nonneg C1), abs_nonneg C1,
            abs_nonneg C2, (by positivity : (0:ℝ) ≤ (N:ℝ)^6)]
  have hAL : Acon * (8 * Real.log N) ≤ Acon * (8 * N) :=
    mul_le_mul_of_nonneg_left (by linarith) Acon_nonneg
  have h6 : (r dd (73/100) + B0) * (roundStart (15/8) 20 (N^8) 6 : ℝ) ≤
      (r dd (73/100) + B0) * (15 + Acon * (8 * N)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

end E500

open SLPEPricing.Regret in
theorem solution : ¬ (∀ (d : ℝ → ℝ) (pstar κ K₁ c μ ρ : ℝ), Standing d pstar κ K₁ c μ ρ →
    ∃ C₁ C₂ C₃ : ℝ, ∀ amax : (ℝ → ℝ) → ℝ → ℝ → ℝ, IsArgmaxSelector amax →
      ∀ T : ℕ, 3 ≤ T → ∀ (ε : ℕ → ℝ) (sel : ℕ → ℕ × ℕ × ℕ × ℕ),
        (lpc d μ ρ amax sel ε T : ℝ) ≤ C₃ + 3 * Real.logb 2 (Real.log (T : ℝ)) ∧
        (Assumption2 μ ρ T sel ε → Concentration d μ ρ amax sel ε T →
          regret d pstar μ ρ amax sel ε T ≤
            (C₁ + C₂ * Real.log (Real.log (T : ℝ))) * Real.sqrt (T : ℝ) * Real.log (T : ℝ))) := by
  intro h
  obtain ⟨C₁, C₂, C₃, hC⟩ := h E500.dd _ _ _ _ _ _ E500.standing
  obtain ⟨T, hT, hlt⟩ := E500.big C₁ C₂
  have := (hC E500.amaxI E500.amaxI_sel T hT (E500.epsI T) (E500.selI T)).2
    (E500.A2_holds T hT) (E500.conc_holds E500.amaxI T hT)
  linarith
