-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.weighted_objective_sdp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:50:10.453137+00:00
-- url     : https://prove2.me/submissions/bf7443bd-8156-4926-89e5-1f80d6279c4d

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19
noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace P19WO
open QAlgorithms.Papers.Independent.Information100.P19
open Polynomial Set

lemma sos_zero : SOS (0 : ℝ[X]) := ⟨0, Fin.elim0, by simp⟩

lemma sos_sq (u : ℝ[X]) : SOS (u ^ 2) := ⟨1, fun _ => u, by simp⟩

lemma sos_add {A B : ℝ[X]} (hA : SOS A) (hB : SOS B) : SOS (A + B) := by
  obtain ⟨N, u, rfl⟩ := hA
  obtain ⟨M, v, rfl⟩ := hB
  exact ⟨N + M, Fin.append u v, by rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]⟩

lemma sos_mul {A B : ℝ[X]} (hA : SOS A) (hB : SOS B) : SOS (A * B) := by
  obtain ⟨N, u, rfl⟩ := hA
  obtain ⟨M, v, rfl⟩ := hB
  refine ⟨N * M, fun k => u (finProdFinEquiv.symm k).1 * v (finProdFinEquiv.symm k).2, ?_⟩
  rw [Equiv.sum_comp finProdFinEquiv.symm (fun p : Fin N × Fin M => (u p.1 * v p.2) ^ 2),
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  simp [mul_pow]

lemma sos_C {c : ℝ} (hc : 0 ≤ c) : SOS (C c) := by
  have : C c = (C (Real.sqrt c)) ^ 2 := by rw [← C_pow, Real.sq_sqrt hc]
  rw [this]; exact sos_sq _

lemma sos_eval_nonneg {A : ℝ[X]} (hA : SOS A) (x : ℝ) : 0 ≤ A.eval x := by
  obtain ⟨N, u, rfl⟩ := hA
  rw [eval_finsetSum]
  exact Finset.sum_nonneg fun i _ => by rw [eval_pow]; positivity

/-- Truncated preordering of weight m. -/
def T (m : ℕ) (p : ℝ[X]) : Prop :=
  ∃ Q S : ℝ[X], SOS Q ∧ SOS S ∧ Q.natDegree ≤ 2 * m ∧
    (X * (1 - X) * S).natDegree ≤ 2 * m ∧ p = Q + X * (1 - X) * S

lemma T_mono {m m' : ℕ} (h : m ≤ m') {p : ℝ[X]} (hp : T m p) : T m' p := by
  obtain ⟨Q, S, hQ, hS, h1, h2, rfl⟩ := hp
  exact ⟨Q, S, hQ, hS, by omega, by omega, rfl⟩

lemma T_mul {m1 m2 : ℕ} {p1 p2 : ℝ[X]} (h1 : T m1 p1) (h2 : T m2 p2) : T (m1 + m2) (p1 * p2) := by
  obtain ⟨Q1, S1, hQ1, hS1, d1, e1, rfl⟩ := h1
  obtain ⟨Q2, S2, hQ2, hS2, d2, e2, rfl⟩ := h2
  refine ⟨Q1 * Q2 + (X * (1 - X)) ^ 2 * (S1 * S2), Q1 * S2 + Q2 * S1,
    sos_add (sos_mul hQ1 hQ2) (sos_mul (sos_sq _) (sos_mul hS1 hS2)),
    sos_add (sos_mul hQ1 hS2) (sos_mul hQ2 hS1), ?_, ?_, by ring⟩
  · have : (X * (1 - X)) ^ 2 * (S1 * S2) = (X * (1 - X) * S1) * (X * (1 - X) * S2) := by ring
    rw [this]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_mul_le).trans (by omega)
    · exact (natDegree_mul_le).trans (by omega)
  · have : X * (1 - X) * (Q1 * S2 + Q2 * S1) = Q1 * (X * (1 - X) * S2) + Q2 * (X * (1 - X) * S1) := by
      ring
    rw [this]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_mul_le).trans (by omega)
    · exact (natDegree_mul_le).trans (by omega)

lemma T_sos {m : ℕ} {Q : ℝ[X]} (hQ : SOS Q) (hd : Q.natDegree ≤ 2 * m) : T m Q :=
  ⟨Q, 0, hQ, sos_zero, hd, by simp, by simp⟩

lemma T_lin2 {α1 β1 α2 β2 : ℝ} (ha1 : 0 ≤ α1) (hb1 : 0 ≤ β1) (ha2 : 0 ≤ α2) (hb2 : 0 ≤ β2) :
    T 1 ((C α1 * X + C β1 * (1 - X)) * (C α2 * X + C β2 * (1 - X))) := by
  refine ⟨C (α1 * α2) * X ^ 2 + C (β1 * β2) * (1 - X) ^ 2, C (α1 * β2 + α2 * β1),
    sos_add (sos_mul (sos_C (mul_nonneg ha1 ha2)) (sos_sq _))
      (sos_mul (sos_C (mul_nonneg hb1 hb2)) (sos_sq _)),
    sos_C (by positivity), ?_, ?_, ?_⟩
  · compute_degree
  · compute_degree
  · simp only [map_mul, map_add]; ring

lemma T_lin {α β : ℝ} (ha : 0 ≤ α) (hb : 0 ≤ β) : T 1 (C α * X + C β * (1 - X)) := by
  have := T_lin2 ha hb zero_le_one zero_le_one
  convert this using 1
  simp

lemma T_const {c : ℝ} (hc : 0 ≤ c) : T 0 (C c) := T_sos (sos_C hc) (by simp)

lemma closure_nonneg (f : ℝ[X]) (a b r : ℝ) (hab : a < b)
    (h : ∀ x ∈ Ioo a b, x ≠ r → 0 ≤ f.eval x) : ∀ x ∈ Icc a b, 0 ≤ f.eval x := by
  have hcl : IsClosed {x : ℝ | 0 ≤ f.eval x} := isClosed_le continuous_const f.continuous
  have hsub : Ioo a b ∩ {r}ᶜ ⊆ {x | 0 ≤ f.eval x} := fun x hx => h x hx.1 hx.2
  have h2 : Ioo a b ⊆ closure (Ioo a b ∩ {r}ᶜ) :=
    (dense_compl_singleton r).open_subset_closure_inter isOpen_Ioo
  intro x hx
  rw [← closure_Ioo hab.ne] at hx
  have := closure_mono h2 hx
  rw [closure_closure] at this
  exact hcl.closure_subset_iff.mpr hsub this


lemma quad_pos (f : ℝ[X]) (hd : f.natDegree = 2) (hr : ∀ x, f.eval x ≠ 0) :
    ∃ f' : ℝ[X], (f' = f ∨ f' = -f) ∧ SOS f' ∧ f'.natDegree = 2 ∧ ∀ x, 0 < f'.eval x := by
  set a := f.coeff 2 with ha_def
  set b := f.coeff 1 with hb_def
  set c := f.coeff 0 with hc_def
  have hf : f = C a * X ^ 2 + C b * X + C c := by
    conv_lhs => rw [as_sum_range' f 3 (by omega)]
    simp [Finset.sum_range_succ, ← C_mul_X_pow_eq_monomial, ha_def, hb_def, hc_def]
    ring
  have hf0 : f ≠ 0 := by rintro rfl; simp at hd
  have ha : a ≠ 0 := by
    have := leadingCoeff_ne_zero.mpr hf0
    rwa [leadingCoeff, hd] at this
  have hev : ∀ x, f.eval x = a * (x * x) + b * x + c := by
    intro x; rw [hf]; simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]; ring
  have hdisc : discrim a b c < 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero ha
      ⟨Real.sqrt (discrim a b c), (Real.mul_self_sqrt hn).symm⟩
    exact hr x (by rw [hev]; exact hx)
  unfold discrim at hdisc
  set u := b / (2 * a) with hu
  set D := (4 * a * c - b ^ 2) / (4 * a ^ 2) with hD
  have hD0 : 0 < D := by
    rw [hD]; apply div_pos (by linarith); positivity
  have key : f = C a * ((X + C u) ^ 2 + C D) := by
    have e1 : C a * ((X + C u) ^ 2 + C D) = C a * X ^ 2 + C (2 * a * u) * X + C (a * (u ^ 2 + D)) := by
      simp only [map_mul, map_add, map_pow, map_ofNat]; ring
    have e2 : 2 * a * u = b := by rw [hu]; field_simp
    have e3 : a * (u ^ 2 + D) = c := by rw [hu, hD]; field_simp; ring
    rw [e1, e2, e3, ← hf]
  have hsos' : SOS ((X + C u) ^ 2 + C D) := sos_add (sos_sq _) (sos_C hD0.le)
  have hev2 : ∀ x, ((X + C u) ^ 2 + C D).eval x = (x + u) ^ 2 + D := by intro x; simp
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · refine ⟨-f, Or.inr rfl, ?_, by rw [natDegree_neg, hd], ?_⟩
    · have : -f = C (-a) * ((X + C u) ^ 2 + C D) := by rw [key, map_neg]; ring
      rw [this]; exact sos_mul (sos_C (by linarith)) hsos'
    · intro x
      rw [eval_neg, key, eval_mul, eval_C, hev2]
      have : 0 < (x + u) ^ 2 + D := by positivity
      nlinarith
  · refine ⟨f, Or.inl rfl, ?_, hd, ?_⟩
    · rw [key]; exact sos_mul (sos_C hpos.le) hsos'
    · intro x
      rw [key, eval_mul, eval_C, hev2]
      have : 0 < (x + u) ^ 2 + D := by positivity
      positivity

lemma extract (p : ℝ[X]) (hd : 1 ≤ p.natDegree) (hp : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ p.eval x) :
    (∃ α β : ℝ, ∃ q : ℝ[X], 0 ≤ α ∧ 0 ≤ β ∧ p = (C α * X + C β * (1 - X)) * q ∧
      q.natDegree + 1 = p.natDegree ∧ ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ q.eval x) ∨
    (∃ f q : ℝ[X], T 1 f ∧ p = f * q ∧ q.natDegree + 2 = p.natDegree ∧
      ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ q.eval x) := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hd
  have hpu : ¬ IsUnit p := by
    intro hu; have := natDegree_eq_zero_of_isUnit hu; omega
  obtain ⟨f, hfi, g, hfg⟩ := WfDvdMonoid.exists_irreducible_factor hpu hp0
  have hf0 : f ≠ 0 := hfi.ne_zero
  have hg0 : g ≠ 0 := by rintro rfl; simp at hfg; exact hp0 hfg
  have hf2 := hfi.natDegree_le_two
  have hf1 : 1 ≤ f.natDegree := by
    by_contra h
    push Not at h
    have : f.degree = 0 := by
      rw [degree_eq_natDegree hf0]; norm_cast; omega
    exact hfi.not_isUnit (isUnit_iff_degree_eq_zero.mpr this)
  rcases (by omega : f.natDegree = 1 ∨ f.natDegree = 2) with h1 | h2
  · obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one ((degree_eq_iff_natDegree_eq hf0).mpr h1)
    have hpr : p.IsRoot r := by
      show p.eval r = 0
      rw [hfg, eval_mul, hr.eq_zero, zero_mul]
    set q0 := p /ₘ (X - C r) with hq0def
    have hq0 : (X - C r) * q0 = p := mul_divByMonic_eq_iff_isRoot.mpr hpr
    have hq0ne : q0 ≠ 0 := by rintro h; rw [h, mul_zero] at hq0; exact hp0 hq0.symm
    have hevp : ∀ x, p.eval x = (x - r) * q0.eval x := by
      intro x; rw [← hq0]; simp
    have hdeg0 : q0.natDegree + 1 = p.natDegree := by
      rw [← hq0, natDegree_mul (X_sub_C_ne_zero r) hq0ne, natDegree_X_sub_C]; ring
    by_cases hrin : 0 < r ∧ r < 1
    · have h_up : 0 ≤ q0.eval r := by
        refine closure_nonneg q0 r 1 r hrin.2 (fun x hx _ => ?_) r ⟨le_refl _, hrin.2.le⟩
        have := hp x ⟨by linarith [hx.1, hrin.1], hx.2.le⟩
        rw [hevp] at this
        by_contra hneg; push Not at hneg
        nlinarith [mul_pos (sub_pos.2 hx.1) (neg_pos.2 hneg)]
      have h_dn : 0 ≤ (-q0).eval r := by
        refine closure_nonneg (-q0) 0 r r hrin.1 (fun x hx _ => ?_) r ⟨hrin.1.le, le_refl _⟩
        have := hp x ⟨hx.1.le, by linarith [hx.2, hrin.2]⟩
        rw [hevp] at this
        rw [eval_neg]
        by_contra hneg; push Not at hneg
        nlinarith [mul_pos (sub_pos.2 hx.2) (neg_lt_zero.mp hneg)]
      rw [eval_neg] at h_dn
      have hq0r : q0.IsRoot r := by show q0.eval r = 0; linarith
      set q1 := q0 /ₘ (X - C r) with hq1def
      have hq1 : (X - C r) * q1 = q0 := mul_divByMonic_eq_iff_isRoot.mpr hq0r
      have hq1ne : q1 ≠ 0 := by rintro h; rw [h, mul_zero] at hq1; exact hq0ne hq1.symm
      have hdeg1 : q1.natDegree + 1 = q0.natDegree := by
        rw [← hq1, natDegree_mul (X_sub_C_ne_zero r) hq1ne, natDegree_X_sub_C]; ring
      right
      refine ⟨(X - C r) ^ 2, q1, T_sos (sos_sq _) (by compute_degree), ?_, by omega, ?_⟩
      · rw [← hq0, ← hq1]; ring
      · refine closure_nonneg q1 0 1 r one_pos (fun x hx hxr => ?_)
        have := hp x ⟨hx.1.le, hx.2.le⟩
        rw [hevp, ← hq1, eval_mul] at this
        simp only [eval_sub, eval_X, eval_C] at this
        have hpos : 0 < (x - r) ^ 2 := by
          have : x - r ≠ 0 := sub_ne_zero.mpr hxr
          positivity
        by_contra hneg; push Not at hneg
        nlinarith [mul_pos hpos (neg_pos.2 hneg)]
    · left
      rcases le_or_gt r 0 with hr0 | hr0
      · refine ⟨1 - r, -r, q0, by linarith, by linarith, ?_, hdeg0, ?_⟩
        · rw [← hq0]; congr 1; simp only [map_sub, map_neg, map_one]; ring
        · refine closure_nonneg q0 0 1 r one_pos (fun x hx _ => ?_)
          have := hp x ⟨hx.1.le, hx.2.le⟩
          rw [hevp] at this
          by_contra hneg; push Not at hneg
          nlinarith [mul_pos (show 0 < x - r by linarith [hx.1]) (neg_pos.2 hneg)]
      · have hr1 : 1 ≤ r := by
          by_contra h; push Not at h; exact hrin ⟨hr0, h⟩
        refine ⟨r - 1, r, -q0, by linarith, by linarith, ?_, by rw [natDegree_neg]; exact hdeg0, ?_⟩
        · rw [← hq0]; simp only [map_sub, map_one]; ring
        · refine closure_nonneg (-q0) 0 1 r one_pos (fun x hx _ => ?_)
          have := hp x ⟨hx.1.le, hx.2.le⟩
          rw [hevp] at this
          rw [eval_neg]
          by_contra hneg; push Not at hneg
          nlinarith [mul_pos (show 0 < r - x by linarith [hx.2]) (neg_lt_zero.mp hneg)]
  · have hroot : ∀ x, f.eval x ≠ 0 := by
      intro x hx
      have := degree_eq_one_of_irreducible_of_root hfi hx
      rw [degree_eq_natDegree hf0, h2] at this
      norm_cast at this
    have hdegg : g.natDegree + 2 = p.natDegree := by
      rw [hfg, natDegree_mul hf0 hg0, h2]; ring
    obtain ⟨f', hf' | hf', hsos, hdeg, hpos⟩ := quad_pos f h2 hroot
    · right
      refine ⟨f', g, T_sos hsos (by omega), by rw [hf', hfg], hdegg, fun x hx => ?_⟩
      have := hp x hx
      rw [hfg, eval_mul, ← hf'] at this
      have := hpos x
      by_contra hneg; push Not at hneg
      nlinarith
    · right
      refine ⟨f', -g, T_sos hsos (by omega), by rw [hf', hfg]; ring,
        by rw [natDegree_neg]; exact hdegg, fun x hx => ?_⟩
      have := hp x hx
      have hp' := hpos x
      rw [hf', eval_neg] at hp'
      rw [hfg, eval_mul] at this
      rw [eval_neg]
      by_contra hneg; push Not at hneg
      nlinarith


theorem cert (d : ℕ) : ∀ p : ℝ[X], p.natDegree = d → (∀ x ∈ Icc (0:ℝ) 1, 0 ≤ p.eval x) →
    (d % 2 = 0 → T (d / 2) p) ∧
    (d % 2 = 1 → ∃ α β : ℝ, ∃ q : ℝ[X], 0 ≤ α ∧ 0 ≤ β ∧ T (d / 2) q ∧
      p = (C α * X + C β * (1 - X)) * q) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro p hpd hp
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨fun _ => ?_, fun h => by simp at h⟩
    have hc : 0 ≤ p.coeff 0 := by
      have := hp 0 ⟨le_refl _, zero_le_one⟩
      rwa [← coeff_zero_eq_eval_zero] at this
    rw [eq_C_of_natDegree_eq_zero hpd]
    exact T_const hc
  · rcases extract p (by omega) hp with ⟨α, β, q, hα, hβ, rfl, hdq, hq⟩ | ⟨f, q, hf, rfl, hdq, hq⟩
    · have ihq := ih (d - 1) (by omega) q (by omega) hq
      constructor
      · intro hev
        obtain ⟨α', β', q2, ha', hb', hT, rfl⟩ := ihq.2 (by omega)
        rw [← mul_assoc]
        exact T_mono (by omega) (T_mul (T_lin2 hα hβ ha' hb') hT)
      · intro hodd
        have e : (d - 1) / 2 = d / 2 := by omega
        exact ⟨α, β, q, hα, hβ, e ▸ ihq.1 (by omega), rfl⟩
    · have ihq := ih (d - 2) (by omega) q (by omega) hq
      constructor
      · intro hev
        exact T_mono (by omega) (T_mul hf (ihq.1 (by omega)))
      · intro hodd
        obtain ⟨α, β, q2, ha, hb, hT, rfl⟩ := ihq.2 (by omega)
        exact ⟨α, β, f * q2, ha, hb, T_mono (by omega) (T_mul hf hT), by ring⟩

lemma part1 (k : ℕ) (hk : 1 ≤ k) (h : ℝ[X]) : minorantFeasible k h ↔ sosFeasible k h := by
  unfold minorantFeasible sosFeasible
  constructor
  · rintro ⟨hdeg, h0, h1, hle⟩
    refine ⟨hdeg, h0, h1, ?_⟩
    set p : ℝ[X] := X - h.comp (X ^ 2) with hpdef
    have hp : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ p.eval x := by
      intro x hx
      rw [hpdef, eval_sub, eval_X, eval_comp]
      simp only [eval_pow, eval_X]
      have := hle (x ^ 2) ⟨by positivity, by nlinarith [hx.1, hx.2]⟩
      rw [Real.sqrt_sq hx.1] at this
      linarith
    have hpdeg : p.natDegree ≤ 2 * k := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · rw [natDegree_X]; omega
      · rw [natDegree_comp]; simp; omega
    have hT : T k p := by
      rcases Nat.mod_two_eq_zero_or_one p.natDegree with he | ho
      · exact T_mono (by omega) ((cert _ p rfl hp).1 he)
      · obtain ⟨α, β, q, ha, hb, hTq, heq⟩ := (cert _ p rfl hp).2 ho
        rw [heq]
        exact T_mono (by omega) (T_mul (T_lin ha hb) hTq)
    obtain ⟨Q, S, hQ, hS, dQ, dS, heq⟩ := hT
    refine ⟨Q, S, hQ, hS, dQ, ?_, heq⟩
    by_cases hS0 : S = 0
    · rw [hS0]; simp
    · have hu : (X * (1 - X) : ℝ[X]).natDegree = 2 := by compute_degree!
      have hu0 : (X * (1 - X) : ℝ[X]) ≠ 0 := by
        intro h0; rw [h0] at hu; simp at hu
      rw [natDegree_mul hu0 hS0, hu] at dS
      omega
  · rintro ⟨hdeg, h0, h1, Q, S, hQ, hS, _, _, heq⟩
    refine ⟨hdeg, h0, h1, fun x hx => ?_⟩
    set t := Real.sqrt x with ht
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have ht1 : t ≤ 1 := by rw [ht]; exact Real.sqrt_le_one.mpr hx.2
    have htx : t ^ 2 = x := Real.sq_sqrt hx.1
    have := congrArg (eval t) heq
    simp only [eval_sub, eval_X, eval_comp, eval_pow, eval_add, eval_mul, eval_one] at this
    rw [htx] at this
    have hq := sos_eval_nonneg hQ t
    have hs := sos_eval_nonneg hS t
    have : 0 ≤ t * (1 - t) * S.eval t := mul_nonneg (mul_nonneg ht0 (by linarith)) hs
    linarith


lemma rpow_int (r : ℝ) (hr : -1 < r) :
    IntegrableOn (fun x : ℝ => x ^ r) (Ioc 0 1) ∧ ∫ x in Ioc (0:ℝ) 1, x ^ r = 1 / (r + 1) := by
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_rpow' hr), ?_⟩
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hr), Real.one_rpow,
    Real.zero_rpow (by linarith : r + 1 ≠ 0)]
  ring

lemma eval_expand (k : ℕ) (h : ℝ[X]) (hdeg : h.natDegree ≤ k) (hc0 : h.coeff 0 = 0) (x : ℝ) :
    h.eval x = ∑ j ∈ Finset.range k, h.coeff (j + 1) * x ^ (j + 1) := by
  rw [eval_eq_sum_range' (n := k + 1) (by omega), Finset.sum_range_succ', hc0]
  simp

lemma part2 (k : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hbeta1 : beta < 3/2) (h : ℝ[X])
    (hdeg : h.natDegree ≤ k) (hc0 : h.coeff 0 = 0) :
    IntegrableOn (fun x : ℝ => Real.rpow x (-beta) * (Real.sqrt x - h.eval x)) (Ioc 0 1) ∧
      weightedError beta hbeta hbeta1 h = 2 / (3 - 2 * beta) - weightedScore k beta h := by
  set G : ℝ → ℝ := fun x => x ^ (1/2 - beta) -
    ∑ j ∈ Finset.range k, h.coeff (j + 1) * x ^ ((j:ℝ) + 1 - beta) with hG
  have hEq : EqOn G (fun x : ℝ => Real.rpow x (-beta) * (Real.sqrt x - h.eval x)) (Ioc 0 1) := by
    intro x hx
    simp only [hG, Real.rpow_eq_pow]
    rw [eval_expand k h hdeg hc0, mul_sub, Finset.mul_sum, Real.sqrt_eq_rpow,
      ← Real.rpow_add hx.1]
    congr 1
    · ring_nf
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, ← Real.rpow_natCast, ← Real.rpow_add hx.1]
      push_cast
      ring_nf
  have hA := rpow_int (1/2 - beta) (by linarith)
  have hB : ∀ j : ℕ, -1 < (j:ℝ) + 1 - beta := by
    intro j; have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have hGi : IntegrableOn G (Ioc 0 1) := by
    refine hA.1.sub (integrable_finset_sum _ fun j _ => ?_)
    exact ((rpow_int _ (hB j)).1).const_mul _
  refine ⟨hGi.congr_fun hEq measurableSet_Ioc, ?_⟩
  unfold weightedError weightedScore
  rw [← setIntegral_congr_fun measurableSet_Ioc hEq, hG]
  rw [integral_sub hA.1 (integrable_finset_sum _ fun j _ => ((rpow_int _ (hB j)).1).const_mul _),
    integral_finset_sum _ fun j _ => ((rpow_int _ (hB j)).1).const_mul _, hA.2]
  congr 1
  · rw [show (1:ℝ)/2 - beta + 1 = (3 - 2*beta)/2 by ring, one_div_div]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, (rpow_int _ (hB j)).2]
    rw [show (j:ℝ) + 1 - beta + 1 = (j:ℝ) + 2 - beta by ring, mul_one_div]

end P19WO

theorem solution (k : ℕ) (hk : 1≤k) (beta : ℝ) (hbeta : 0≤beta) (hbeta1 : beta<3/2) :
    (∀ h : Polynomial ℝ, QAlgorithms.Papers.Independent.Information100.P19.minorantFeasible k h ↔
      QAlgorithms.Papers.Independent.Information100.P19.sosFeasible k h) ∧
    (∀ h : Polynomial ℝ, QAlgorithms.Papers.Independent.Information100.P19.sosFeasible k h →
      IntegrableOn (fun x : ℝ => Real.rpow x (-beta)*(Real.sqrt x-h.eval x)) (Set.Ioc 0 1) ∧
      QAlgorithms.Papers.Independent.Information100.P19.weightedError beta hbeta hbeta1 h =
        2/(3-2*beta)-QAlgorithms.Papers.Independent.Information100.P19.weightedScore k beta h) ∧
    (∀ h : Polynomial ℝ, QAlgorithms.Papers.Independent.Information100.P19.WeightedOptimizer k beta h ↔
      QAlgorithms.Papers.Independent.Information100.P19.sosFeasible k h ∧
        ∀ g : Polynomial ℝ, QAlgorithms.Papers.Independent.Information100.P19.sosFeasible k g →
          QAlgorithms.Papers.Independent.Information100.P19.weightedScore k beta g ≤
            QAlgorithms.Papers.Independent.Information100.P19.weightedScore k beta h) := by
  have P2 : ∀ h : Polynomial ℝ, QAlgorithms.Papers.Independent.Information100.P19.sosFeasible k h →
      IntegrableOn (fun x : ℝ => Real.rpow x (-beta)*(Real.sqrt x-h.eval x)) (Set.Ioc 0 1) ∧
      QAlgorithms.Papers.Independent.Information100.P19.weightedError beta hbeta hbeta1 h =
        2/(3-2*beta)-QAlgorithms.Papers.Independent.Information100.P19.weightedScore k beta h :=
    fun h hs => P19WO.part2 k beta hbeta hbeta1 h hs.1 hs.2.1
  refine ⟨P19WO.part1 k hk, P2, fun h => ?_⟩
  unfold QAlgorithms.Papers.Independent.Information100.P19.WeightedOptimizer
  constructor
  · rintro ⟨h0, h1, hm, hopt⟩
    have hs := (P19WO.part1 k hk h).mp hm
    refine ⟨hs, fun g hg => ?_⟩
    have := hopt g ((P19WO.part1 k hk g).mpr hg)
    rw [(P2 h hs).2, (P2 g hg).2] at this
    linarith
  · rintro ⟨hs, hopt⟩
    refine ⟨hbeta, hbeta1, (P19WO.part1 k hk h).mpr hs, fun g hg => ?_⟩
    have hg' := (P19WO.part1 k hk g).mp hg
    rw [(P2 h hs).2, (P2 g hg').2]
    linarith [hopt g hg']

