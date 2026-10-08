-- Prove2me | solution 1 for QueueingFundamentals.GG1.mdc_pgf_roots
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:45:33.524912+00:00
-- url     : https://prove2.me/submissions/2d0254e9-cb3f-4d76-84e2-43d34e7c5f4b

import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_MDc

set_option autoImplicit false

namespace P007984b6

open QueueingFundamentals.GG1

lemma hasSum_poisson (lam : ℝ) (w : ℂ) :
    HasSum (fun m => (poissonProb lam m : ℂ) * w ^ m) (Complex.exp (-(lam : ℂ) * (1 - w))) := by
  have h := NormedSpace.expSeries_div_hasSum_exp ((lam : ℂ) * w)
  rw [← Complex.exp_eq_exp_ℂ] at h
  have h2 := h.mul_left (Complex.exp (-(lam : ℂ)))
  have e1 : (fun m => (poissonProb lam m : ℂ) * w ^ m) =
      fun i => Complex.exp (-(lam : ℂ)) * (((lam : ℂ) * w) ^ i / (i.factorial : ℂ)) := by
    funext m
    simp only [poissonProb]
    push_cast
    rw [mul_pow]
    field_simp
  have e2 : Complex.exp (-(lam : ℂ) * (1 - w)) = Complex.exp (-(lam : ℂ)) * Complex.exp ((lam : ℂ) * w) := by
    rw [← Complex.exp_add]; ring_nf
  rw [e1, e2]; exact h2

lemma poisson_nonneg (lam : ℝ) (hlam : 0 ≤ lam) (m : ℕ) : 0 ≤ poissonProb lam m := by
  unfold poissonProb; positivity

lemma poisson_summable (lam : ℝ) : Summable (poissonProb lam) := by
  have := (Real.summable_pow_div_factorial lam).mul_left (Real.exp (-lam))
  have e : poissonProb lam = fun i => Real.exp (-lam) * (lam ^ i / (i.factorial : ℝ)) := by
    funext m; simp only [poissonProb]; ring
  rw [e]; exact this

lemma pgf_identity (lam : ℝ) (hlam : 0 ≤ lam) (c : ℕ) (p : ℕ → ℝ) (hp : IsMDcStationary lam c p)
    (w : ℂ) (hw : ‖w‖ ≤ 1) :
    QueueingFundamentals.MG1.pgf p w * (1 - w ^ c * Complex.exp ((lam : ℂ) * (1 - w))) =
      ∑ j ∈ Finset.range c, (p j : ℂ) * (w ^ j - w ^ c) := by
  obtain ⟨hnn, hsum, hbal⟩ := hp
  have hps : Summable p := hsum.summable
  have hpow : ∀ n : ℕ, ‖w ^ n‖ ≤ 1 := fun n => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
  have hsP : Summable (fun n => (p n : ℂ) * w ^ n) := by
    refine Summable.of_norm_bounded hps (fun n => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnn n)]
    exact mul_le_of_le_one_right (hnn n) (hpow n)
  set b : ℕ → ℝ := fun k => if k = 0 then cumProb p c else p (c + k) with hb
  have hbnn : ∀ k, 0 ≤ b k := by
    intro k; simp only [hb]; split_ifs
    · exact Finset.sum_nonneg (fun n _ => hnn n)
    · exact hnn _
  have hbs : Summable b := by
    rw [← summable_nat_add_iff 1]
    have := (summable_nat_add_iff (c + 1)).mpr hps
    convert this using 1
    funext k; simp only [hb]; simp; ring_nf
  set f : ℕ → ℂ := fun k => (b k : ℂ) * w ^ k with hf
  set g : ℕ → ℂ := fun m => (poissonProb lam m : ℂ) * w ^ m with hg
  have hfn : Summable (fun k => ‖f k‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hbs
    simp only [hf]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hbnn k)]
    exact mul_le_of_le_one_right (hbnn k) (hpow k)
  have hgn : Summable (fun m => ‖g m‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) (poisson_summable lam)
    simp only [hg]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (poisson_nonneg lam hlam m)]
    exact mul_le_of_le_one_right (poisson_nonneg lam hlam m) (hpow m)
  have hcauchy := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hfn hgn
  have hinner : ∀ n, ∑ k ∈ Finset.range (n + 1), f k * g (n - k) = (p n : ℂ) * w ^ n := by
    intro n
    have h1 : ∀ k ∈ Finset.range (n + 1), f k * g (n - k) =
        ((b k * poissonProb lam (n - k) : ℝ) : ℂ) * w ^ n := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp only [hf, hg]; push_cast
      rw [show w ^ n = w ^ k * w ^ (n - k) by rw [← pow_add, Nat.add_sub_cancel' hkn]]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← Complex.ofReal_sum]
    congr 2
    rw [hbal n, Finset.sum_range_succ']
    simp only [hb, if_pos rfl, Nat.succ_ne_zero, if_false, Nat.sub_zero]
    rw [add_comm]
    congr 1
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (f := fun k => p (c + k) * poissonProb lam (n - k))]
    rfl
  have hPw : QueueingFundamentals.MG1.pgf p w = (∑' k, f k) * (∑' m, g m) := by
    rw [hcauchy]; unfold QueueingFundamentals.MG1.pgf
    exact tsum_congr (fun n => (hinner n).symm)
  have hA : ∑' m, g m = Complex.exp (-(lam : ℂ) * (1 - w)) := (hasSum_poisson lam w).tsum_eq
  have hfs : Summable f := hfn.of_norm
  have hB : ∑' k, f k = (cumProb p c : ℂ) + ∑' k, (p (c + (k + 1)) : ℂ) * w ^ (k + 1) := by
    rw [hfs.tsum_eq_zero_add]
    simp [hf, hb]
  have hsplit := hsP.sum_add_tsum_nat_add (c + 1)
  set T := ∑' k, (p (k + (c + 1)) : ℂ) * w ^ (k + (c + 1)) with hT
  set R := ∑' k, (p (c + (k + 1)) : ℂ) * w ^ (k + 1) with hR
  have hRT : w ^ c * R = T := by
    rw [hR, hT, ← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    rw [show k + (c + 1) = c + (k + 1) by ring, pow_add]; ring
  have hsumc : ∑ j ∈ Finset.range c, (p j : ℂ) * (w ^ j - w ^ c) =
      (∑ j ∈ Finset.range (c + 1), (p j : ℂ) * w ^ j) - (cumProb p c : ℂ) * w ^ c := by
    simp only [cumProb]; push_cast
    rw [Finset.sum_range_succ, Finset.sum_range_succ, add_mul, Finset.sum_mul]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hAE : Complex.exp (-(lam : ℂ) * (1 - w)) * Complex.exp ((lam : ℂ) * (1 - w)) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  rw [hsumc]
  rw [hB, hA] at hPw
  set P := QueueingFundamentals.MG1.pgf p w
  set S := ∑ j ∈ Finset.range (c + 1), (p j : ℂ) * w ^ j
  set Pc := (cumProb p c : ℂ)
  set A := Complex.exp (-(lam : ℂ) * (1 - w))
  set E := Complex.exp ((lam : ℂ) * (1 - w))
  have h3 : P = S + T := by rw [hsplit]; rfl
  linear_combination h3 - w ^ c * E * hPw - E * A * hRT - (T + Pc * w ^ c) * hAE

open Polynomial in
lemma factor (c : ℕ) (hc : 1 ≤ c) (z : Fin (c - 1) → ℂ) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (Q : ℂ[X]) (hQ0 : Q ≠ 0) (hdeg : Q.natDegree ≤ c)
    (hr1 : Q.eval 1 = 0) (hrz : ∀ i, Q.eval (z i) = 0) :
    ∃ K : ℂ, ∀ y, Q.eval y = K * ((y - 1) * ∏ i, (y - z i)) := by
  classical
  set s : Multiset ℂ := 1 ::ₘ (Finset.univ.val.map z) with hs
  have hnd : s.Nodup := by
    rw [hs, Multiset.nodup_cons]
    refine ⟨?_, Multiset.Nodup.map hinj Finset.univ.nodup⟩
    intro h
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp h
    exact hz1 i hi
  have hle : s ≤ Q.roots := by
    rw [Multiset.le_iff_subset hnd]
    intro a ha
    rw [Polynomial.mem_roots hQ0, Polynomial.IsRoot.def]
    rw [hs, Multiset.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hr1
    · obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp ha
      exact hrz i
  obtain ⟨T, hT⟩ := (Multiset.prod_X_sub_C_dvd_iff_le_roots hQ0 s).mpr hle
  set R := (s.map fun a => X - C a).prod with hR
  have hRdeg : R.natDegree = c := by
    rw [hR, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hs, Multiset.card_cons,
      Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
    omega
  have hRmon : R.Monic := Polynomial.monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hT0 : T ≠ 0 := by rintro rfl; simp at hT; exact hQ0 hT
  have hTdeg : T.natDegree = 0 := by
    have := Polynomial.natDegree_mul hRmon.ne_zero hT0
    rw [← hT] at this; omega
  refine ⟨T.coeff 0, fun y => ?_⟩
  have hReq : R = (X - C 1) * ∏ i, (X - C (z i)) := by
    rw [hR, hs, Multiset.map_cons, Multiset.prod_cons, Multiset.map_map]; rfl
  rw [hT, Polynomial.eq_C_of_natDegree_eq_zero hTdeg, Polynomial.eval_mul, Polynomial.eval_C, hReq,
    Polynomial.eval_mul, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.coeff_C_zero]
  ring

end P007984b6

open QueueingFundamentals.GG1 in
theorem solution (lam : ℝ) (hlam : 0 < lam) (c : ℕ) (hc : 1 ≤ c) (hstab : lam < c)
    (z : Fin (c - 1) → ℂ) (hinj : Function.Injective z)
    (hroot : ∀ i, ‖z i‖ ≤ 1 ∧ z i ≠ 1 ∧ z i ^ c = Complex.exp (-(lam : ℂ) * (1 - z i)))
    (hall : ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 1 → w ^ c = Complex.exp (-(lam : ℂ) * (1 - w)) →
      ∃ i, z i = w)
    (p : ℕ → ℝ) (hp : IsMDcStationary lam c p) :
    (∀ w : ℂ, ‖w‖ ≤ 1 →
      QueueingFundamentals.MG1.pgf p w * (1 - w ^ c * Complex.exp ((lam : ℂ) * (1 - w))) =
        ((lam : ℂ) - c) / (∏ i, (1 - z i)) * ((w - 1) * ∏ i, (w - z i))) ∧
    (2 ≤ c →
      (p 0 : ℂ) = ((c : ℂ) - lam) * (-1) ^ (c - 1) * (∏ i, z i) / ∏ i, (1 - z i)) := by
  classical
  open Polynomial in
  set Q : ℂ[X] := ∑ j ∈ Finset.range c, C (p j : ℂ) * (X ^ j - X ^ c) with hQ
  have hQeval : ∀ y, Q.eval y = ∑ j ∈ Finset.range c, (p j : ℂ) * (y ^ j - y ^ c) := by
    intro y; simp [hQ, Polynomial.eval_finsetSum]
  have hQdeg : Q.natDegree ≤ c := by
    rw [hQ]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j hj => ?_)
    have hj' : j ≤ c := (Finset.mem_range.mp hj).le
    refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_sub_le _ _).trans ?_)
    simp only [Polynomial.natDegree_X_pow]
    exact max_le hj' le_rfl
  set F : ℂ → ℂ := fun w => 1 - w ^ c * Complex.exp ((lam : ℂ) * (1 - w)) with hF
  have hkey : ∀ w : ℂ, ‖w‖ ≤ 1 → Q.eval w = QueueingFundamentals.MG1.pgf p w * F w := by
    intro w hw
    rw [hQeval, hF]
    exact (P007984b6.pgf_identity lam hlam.le c p hp w hw).symm
  have hF1 : F 1 = 0 := by simp [hF]
  have hFz : ∀ i, F (z i) = 0 := by
    intro i
    simp only [hF]
    rw [(hroot i).2.2, ← Complex.exp_add]
    ring_nf; simp
  have hFd : HasDerivAt F ((lam : ℂ) - c) 1 := by
    have h := (((hasDerivAt_id (1 : ℂ)).const_sub 1).const_mul (lam : ℂ)).cexp
    have h2 := ((hasDerivAt_pow c (1 : ℂ)).mul h).const_sub 1
    exact h2.congr_deriv (by simp <;> ring)
  -- the approach sequence
  set r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1) with hr
  set x : ℕ → ℂ := fun n => ((r n : ℝ) : ℂ) with hx
  have hr0 : ∀ n, 0 ≤ r n := by
    intro n; simp only [hr]
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith
  have hr1 : ∀ n, r n < 1 := by
    intro n; simp only [hr]
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hxn : ∀ n, ‖x n‖ ≤ 1 := by
    intro n; simp only [hx, Complex.norm_real, Real.norm_of_nonneg (hr0 n)]; exact (hr1 n).le
  have hxne : ∀ n, x n ≠ 1 := by
    intro n h
    exact (hr1 n).ne (Complex.ofReal_eq_one.mp h)
  have hrt : Filter.Tendsto r Filter.atTop (nhds 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [hr] using this
  have hxt : Filter.Tendsto x Filter.atTop (nhds 1) := by
    have := (Complex.continuous_ofReal.tendsto 1).comp hrt
    rw [Complex.ofReal_one] at this
    exact this
  -- continuity of the pgf on the closed disk
  obtain ⟨hnn, hsum, _⟩ := hp
  have hcont : ContinuousOn (QueueingFundamentals.MG1.pgf p) (Metric.closedBall 0 1) := by
    unfold QueueingFundamentals.MG1.pgf
    refine continuousOn_tsum (u := p) (fun i => (continuous_const.mul (continuous_pow i)).continuousOn)
      hsum.summable (fun n w hw => ?_)
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnn n), norm_pow]
    exact mul_le_of_le_one_right (hnn n) (pow_le_one₀ (norm_nonneg _) hw)
  have hP1 : QueueingFundamentals.MG1.pgf p 1 = 1 := by
    unfold QueueingFundamentals.MG1.pgf
    simp only [one_pow, mul_one]
    have := (Complex.hasSum_ofReal.mpr hsum).tsum_eq
    simpa using this
  have hPt : Filter.Tendsto (fun n => QueueingFundamentals.MG1.pgf p (x n)) Filter.atTop (nhds 1) := by
    have hw : ContinuousWithinAt (QueueingFundamentals.MG1.pgf p) (Metric.closedBall 0 1) 1 :=
      hcont 1 (by simp)
    rw [← hP1]
    refine hw.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hxt, Filter.Eventually.of_forall (fun n => ?_)⟩)
    simpa using hxn n
  have hSt : Filter.Tendsto (fun n => slope F 1 (x n)) Filter.atTop (nhds ((lam : ℂ) - c)) := by
    refine (hasDerivAt_iff_tendsto_slope.mp hFd).comp
      (tendsto_nhdsWithin_iff.2 ⟨hxt, Filter.Eventually.of_forall (fun n => ?_)⟩)
    exact hxne n
  set u : ℕ → ℂ := fun n => (x n - 1)⁻¹ * Q.eval (x n) with hu
  have hu1 : Filter.Tendsto u Filter.atTop (nhds ((lam : ℂ) - c)) := by
    have := hPt.mul hSt
    rw [one_mul] at this
    refine this.congr (fun n => ?_)
    simp only [hu, slope_def_field, hF1, sub_zero, hkey _ (hxn n)]
    field_simp [sub_ne_zero.mpr (hxne n)]
  have hlc : (lam : ℂ) - c ≠ 0 := by
    intro h
    have : (lam : ℂ) = (c : ℝ) := by rw [sub_eq_zero] at h; rw [h]; simp
    have := Complex.ofReal_injective this
    linarith
  have hQ0 : Q ≠ 0 := by
    intro h0
    have hz : ∀ n, u n = 0 := fun n => by simp [hu, h0]
    have : Filter.Tendsto u Filter.atTop (nhds 0) := by
      rw [show u = fun _ => 0 from funext hz]; exact tendsto_const_nhds
    exact hlc (tendsto_nhds_unique hu1 this)
  have hz1 : ∀ i, z i ≠ 1 := fun i => (hroot i).2.1
  obtain ⟨K, hK⟩ := P007984b6.factor c hc z hinj hz1 Q hQ0 hQdeg
    (by rw [hkey 1 (by simp), hF1, mul_zero])
    (fun i => by rw [hkey (z i) (hroot i).1, hFz i, mul_zero])
  have hu2 : Filter.Tendsto u Filter.atTop (nhds (K * ∏ i, (1 - z i))) := by
    have hc2 : Continuous (fun y : ℂ => K * ∏ i, (y - z i)) := by fun_prop
    have := (hc2.tendsto 1).comp hxt
    refine this.congr (fun n => ?_)
    simp only [Function.comp, hu, hK]
    field_simp [sub_ne_zero.mpr (hxne n)]
  have hKeq : K * ∏ i, (1 - z i) = (lam : ℂ) - c := tendsto_nhds_unique hu2 hu1
  have hprod : ∏ i, (1 - z i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hz1 i).symm)
  have hKv : K = ((lam : ℂ) - c) / ∏ i, (1 - z i) := by
    rw [← hKeq]; field_simp
  have part1 : ∀ w : ℂ, ‖w‖ ≤ 1 →
      QueueingFundamentals.MG1.pgf p w * (1 - w ^ c * Complex.exp ((lam : ℂ) * (1 - w))) =
        ((lam : ℂ) - c) / (∏ i, (1 - z i)) * ((w - 1) * ∏ i, (w - z i)) := by
    intro w hw
    have := hkey w hw
    rw [hK, hKv] at this
    rw [← this]
  refine ⟨part1, fun _ => ?_⟩
  have h0 := part1 0 (by simp)
  have hpgf0 : QueueingFundamentals.MG1.pgf p 0 = p 0 := by
    unfold QueueingFundamentals.MG1.pgf
    rw [tsum_eq_single 0]
    · simp
    · intro b hb; simp [hb]
  rw [hpgf0, zero_pow (by omega : c ≠ 0)] at h0
  simp only [zero_mul, sub_zero, mul_one, zero_sub] at h0
  rw [h0, Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  field_simp
  ring
