-- Prove2me | solution 1 for WeierstrassEllipticZeta.sigma_addition_from_differential
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T20:37:56.108375+00:00
-- url     : https://prove2.me/submissions/f91f6770-8787-4c30-9361-4d7ea1e14af2

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic.LinearCombination

noncomputable section
open Filter
open scoped Topology

open WeierstrassEllipticZeta

private lemma zeta_neg (L : PeriodPair) (z : ℂ) :
    weierstrassZeta L (-z) = -weierstrassZeta L z := by
  classical
  have hsum : (∑' l : L.lattice, if -l = 0 then (0 : ℂ) else
      1 / (-z - ((-l : L.lattice) : ℂ)) + 1 / ((-l : L.lattice) : ℂ) +
        -z / ((-l : L.lattice) : ℂ) ^ 2) =
      ∑' l : L.lattice, -(if l = 0 then 0 else
        1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2) := by
    apply tsum_congr
    intro l
    by_cases hl : l = 0
    · simp [hl]
    · simp only [neg_eq_zero, if_neg hl, NegMemClass.coe_neg, even_two, Even.neg_pow]
      rw [show -z - -(l : ℂ) = -(z - (l : ℂ)) by ring]
      simp only [div_neg, neg_div]
      ring
  unfold weierstrassZeta
  conv_lhs => arg 2; rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, hsum, tsum_neg, div_neg]
  ring

private lemma sigma_ne_zero (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (z : ℂ) (hz : z ∉ L.lattice) : S.sigma z ≠ 0 := by
  intro hzero
  have hf := S.entire.analyticAt z
  have ha : AnalyticAt ℂ (weierstrassZeta L) z :=
    (show DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ from
      fun w hw => (hzeta w hw).differentiableAt.differentiableWithinAt).analyticOnNhd
        L.isClosed_lattice.isOpen_compl z hz
  have hfinite : analyticOrderAt S.sigma z ≠ ⊤ := by
    intro ho
    have heq : S.sigma = fun _ => 0 :=
      (show AnalyticOnNhd ℂ S.sigma Set.univ from fun w _ => S.entire.analyticAt w).eq_of_eventuallyEq
        (fun _ _ => analyticAt_const) (analyticOrderAt_eq_top.mp ho)
    have h0 := S.deriv_zero
    rw [heq] at h0
    have hbad := h0.unique (hasDerivAt_const (0 : ℂ) (0 : ℂ))
    norm_num at hbad
  have hderiv : deriv S.sigma =ᶠ[𝓝 z] S.sigma * weierstrassZeta L := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    simpa [mul_comm] using (S.hasDerivAt w hw).deriv
  have ho : analyticOrderAt (deriv S.sigma) z + 1 = analyticOrderAt S.sigma z := by
    simpa [hzero] using hf.analyticOrderAt_deriv_add_one
  rw [analyticOrderAt_congr hderiv, analyticOrderAt_mul hf ha] at ho
  have hle : analyticOrderAt S.sigma z + 1 ≤ analyticOrderAt S.sigma z := by
    calc
      _ ≤ (analyticOrderAt S.sigma z + analyticOrderAt (weierstrassZeta L) z) + 1 :=
        add_le_add (show analyticOrderAt S.sigma z ≤
          analyticOrderAt S.sigma z + analyticOrderAt (weierstrassZeta L) z from le_self_add) le_rfl
      _ = _ := ho
  exact (lt_irrefl _ ((ENat.add_one_le_iff hfinite).mp hle))

private lemma sigma_neg (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → S.sigma z ≠ 0)
    (z : ℂ) (hz : z ∉ L.lattice) : S.sigma (-z) = -S.sigma z := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hd (w : ℂ) (hw : w ∉ L.lattice) :
      HasDerivAt (fun x => S.sigma (-x) / S.sigma x) 0 w := by
    have hm : HasDerivAt (fun x => S.sigma (-x))
        (weierstrassZeta L w * S.sigma (-w)) w := by
      convert! (S.hasDerivAt (-w) (by simpa using hw)).comp w
        (hasDerivAt_id w).neg using 1
      simp [zeta_neg]
    convert! hm.div (S.hasDerivAt w hw) (hne w hw) using 1
    ring
  obtain ⟨c, hc⟩ := hopen.exists_is_const_of_deriv_eq_zero
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hd w hw).deriv)
  have heq : (fun w => S.sigma (-w)) =ᶠ[𝓝 (0 : ℂ)]
      (fun w => c * S.sigma w) := by
    filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with w hw
    by_cases hw0 : w = 0
    · simp [hw0, S.zero]
    · have hwL : w ∉ L.lattice := fun h => hw ⟨h, hw0⟩
      exact (div_eq_iff (hne w hwL)).mp (hc w hwL)
  have hm : HasDerivAt (fun w => S.sigma (-w)) (-1) 0 := by
    have hh : HasDerivAt S.sigma 1 (-(0 : ℂ)) := by simpa using S.deriv_zero
    simpa using! hh.comp 0 (hasDerivAt_id (0 : ℂ)).neg
  have hcc := (hm.congr_of_eventuallyEq heq.symm).unique (S.deriv_zero.const_mul c)
  simp only [mul_one] at hcc
  have h := (div_eq_iff (hne z hz)).mp (hc z hz)
  simpa [← hcc] using h

private lemma analytic_locally_constant {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z)
    (hd : ∀ᶠ w in 𝓝[≠] z, deriv f w = 0) :
    f =ᶠ[𝓝 z] (fun _ => f z) := by
  have hdeq : deriv f =ᶠ[𝓝[≠] z] (fun _ => 0) := hd
  have hdz : deriv f z = 0 := tendsto_nhds_unique
    (hf.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' hdeq.symm)
  have hdall : ∀ᶠ w in 𝓝 z, deriv f w = 0 := by
    rw [eventually_nhdsWithin_iff] at hd
    filter_upwards [hd] with w hw
    by_cases hwz : w = z
    · simpa [hwz] using hdz
    · exact hw hwz
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (hf.eventually_analyticAt.and hdall)
  filter_upwards [Metric.ball_mem_nhds z hr] with w hw
  exact Metric.isOpen_ball.is_const_of_deriv_eq_zero Metric.isPreconnected_ball
    (fun x hx => (hball hx).1.differentiableAt.differentiableWithinAt)
    (fun x hx => (hball hx).2) hw (Metric.mem_ball_self hr)

private lemma sigma_ratio_deriv (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hadd : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (w v : ℂ) (hw : w ∉ L.lattice) (hv : v ∉ L.lattice)
    (hp : w + v ∉ L.lattice) (hm : w - v ∉ L.lattice)
    (hB : (L.weierstrassP v - L.weierstrassP w) * S.sigma w ^ 2 * S.sigma v ^ 2 ≠ 0) :
    HasDerivAt (fun x => (S.sigma (x + v) * S.sigma (x - v)) /
      ((L.weierstrassP v - L.weierstrassP x) * S.sigma x ^ 2 * S.sigma v ^ 2)) 0 w := by
  have h1 := hadd w v hw hv hp
  have h2 := hadd w (-v) hw (by simpa using hv) (by simpa [sub_eq_add_neg] using hm)
  rw [L.weierstrassP_neg, L.derivWeierstrassP_neg, zeta_neg] at h2
  have hZ : (L.weierstrassP v - L.weierstrassP w) *
      (weierstrassZeta L (w + v) + weierstrassZeta L (w - v) -
        2 * weierstrassZeta L w) = -L.derivWeierstrassP w := by
    simp only [sub_eq_add_neg] at h2 ⊢
    linear_combination (h1 + h2) / 2
  have hplus : HasDerivAt (fun x => S.sigma (x + v))
      (weierstrassZeta L (w + v) * S.sigma (w + v)) w := by
    simpa using! (S.hasDerivAt (w + v) hp).comp w ((hasDerivAt_id w).add_const v)
  have hminus : HasDerivAt (fun x => S.sigma (x - v))
      (weierstrassZeta L (w - v) * S.sigma (w - v)) w := by
    simpa using! (S.hasDerivAt (w - v) hm).comp w ((hasDerivAt_id w).sub_const v)
  have hP : HasDerivAt L.weierstrassP (L.derivWeierstrassP w) w := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hw)).hasDerivAt
  have hden := (((hasDerivAt_const w (L.weierstrassP v)).sub hP).mul
    ((S.hasDerivAt w hw).pow 2)).mul_const (S.sigma v ^ 2)
  convert! (hplus.mul hminus).div hden hB using 1
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_sub]
  symm
  apply (div_eq_zero_iff).mpr
  left
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
  linear_combination hZ * (S.sigma (w + v) * S.sigma (w - v) *
    S.sigma w ^ 2 * S.sigma v ^ 2)

/-- The sigma addition identity follows from the normalized entire solution
of its differential equation and the canonical zeta addition identity. -/
theorem solution
    (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_zeta_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z) :
    (∀ z : ℂ, z ∉ L.lattice → S.sigma z ≠ 0) ∧
      ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice →
        S.sigma (z + v) * S.sigma (z - v) =
          (L.weierstrassP v - L.weierstrassP z) * S.sigma z ^ 2 * S.sigma v ^ 2 := by
  have hne := sigma_ne_zero L S h_zeta_deriv
  refine ⟨hne, ?_⟩
  intro z v hz hv
  let t := dslope S.sigma 0
  have ht0 : t 0 = 1 := by simp [t, dslope_same, S.deriv_zero.deriv]
  have htx (x : ℂ) : x * t x = S.sigma x := by
    simpa only [t, sub_zero, smul_eq_mul] using sub_smul_dslope_of_zero S.zero x
  have ht (x : ℂ) : AnalyticAt ℂ t x := by
    by_cases hx : x = 0
    · subst x
      obtain ⟨p, hp⟩ := S.entire.analyticAt (0 : ℂ)
      exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
    · have heq : t =ᶠ[𝓝 x] (fun w => S.sigma w / w) := by
        filter_upwards [eventually_ne_nhds hx] with w hw
        simp [t, dslope_of_ne _ hw, slope, S.zero, div_eq_mul_inv, mul_comm]
      exact ((S.entire.analyticAt x).div analyticAt_id hx).congr heq.symm
  let A : ℂ → ℂ := fun x => S.sigma (x + v) * S.sigma (x - v)
  let B : ℂ → ℂ := fun x =>
    ((L.weierstrassP v - L.weierstrassPExcept 0 x) * x ^ 2 - 1) *
      t x ^ 2 * S.sigma v ^ 2
  have hA (x : ℂ) : AnalyticAt ℂ A x := by
    exact ((S.entire.analyticAt (x + v)).comp
      (f := fun x : ℂ => x + v) (analyticAt_id.add analyticAt_const)).mul
      ((S.entire.analyticAt (x - v)).comp
        (f := fun x : ℂ => x - v) (analyticAt_id.sub analyticAt_const))
  have hB : AnalyticOnNhd ℂ B ((L.lattice : Set ℂ) \ {0})ᶜ := by
    intro x hx
    exact (((analyticAt_const.sub (L.analyticOnNhd_weierstrassPExcept 0 x hx)).mul
      (analyticAt_id.pow 2)).sub analyticAt_const).mul ((ht x).pow 2) |>.mul analyticAt_const
  have hB0 : B 0 = -(S.sigma v ^ 2) := by simp [B, ht0]
  have hBn : B 0 ≠ 0 := by rw [hB0]; exact neg_ne_zero.mpr (pow_ne_zero _ (hne v hv))
  have hAB0 : A 0 = B 0 := by simp [A, hB0, sigma_neg L S hne v hv, pow_two]
  have hB_eq (x : ℂ) (hx : x ≠ 0) : B x =
      (L.weierstrassP v - L.weierstrassP x) * S.sigma x ^ 2 * S.sigma v ^ 2 := by
    have hP := L.weierstrassPExcept_add (0 : L.lattice) x
    simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, div_zero, sub_zero] at hP
    rw [← hP, ← htx x]
    dsimp [B]
    field_simp
    ring
  let R : ℂ → ℂ := fun x => A x / B x
  have hR : AnalyticAt ℂ R 0 := (hA 0).div (hB 0 (by simp)) hBn
  have hR0 : R 0 = 1 := by exact (div_eq_one_iff_eq hBn).mpr hAB0
  have hd : ∀ᶠ w in 𝓝[≠] (0 : ℂ), deriv R w = 0 := by
    have hreg : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ ((L.lattice : Set ℂ) \ {0})ᶜ :=
      L.compl_lattice_sdiff_singleton_mem_nhds 0
    have hp : ∀ᶠ w in 𝓝 (0 : ℂ), w + v ∉ L.lattice := by
      simpa using (continuousAt_id.add continuousAt_const).eventually
        (L.isClosed_lattice.isOpen_compl.mem_nhds (show 0 + v ∉ L.lattice by simpa using hv))
    have hm : ∀ᶠ w in 𝓝 (0 : ℂ), w - v ∉ L.lattice := by
      simpa using (continuousAt_id.sub continuousAt_const).eventually
        (L.isClosed_lattice.isOpen_compl.mem_nhds (show 0 - v ∉ L.lattice by simpa using hv))
    filter_upwards [hreg.filter_mono nhdsWithin_le_nhds,
      hp.filter_mono nhdsWithin_le_nhds, hm.filter_mono nhdsWithin_le_nhds,
      ((hB 0 (by simp)).continuousAt.eventually_ne hBn).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hw hwp hwm hBw hw0
    have hwr : w ∉ L.lattice := fun h => hw ⟨h, hw0⟩
    have hBd : (L.weierstrassP v - L.weierstrassP w) * S.sigma w ^ 2 * S.sigma v ^ 2 ≠ 0 := by
      rwa [hB_eq w hw0] at hBw
    have hh := sigma_ratio_deriv L S h_zeta_addition w v hwr hv hwp hwm hBd
    have heq : R =ᶠ[𝓝 w] (fun x => (S.sigma (x + v) * S.sigma (x - v)) /
        ((L.weierstrassP v - L.weierstrassP x) * S.sigma x ^ 2 * S.sigma v ^ 2)) := by
      filter_upwards [eventually_ne_nhds hw0] with x hx
      simp only [R, A, hB_eq x hx]
    exact (hh.congr_of_eventuallyEq heq).deriv
  have hnear : A =ᶠ[𝓝 (0 : ℂ)] B := by
    filter_upwards [analytic_locally_constant hR hd,
      (hB 0 (by simp)).continuousAt.eventually_ne hBn] with w hw hn
    change A w / B w = R 0 at hw
    rw [hR0] at hw
    exact (div_eq_one_iff_eq hn).mp hw
  have hcount : (L.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L.lattice)
  have hconn : IsPreconnected (((L.lattice : Set ℂ) \ {0})ᶜ) :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (hcount.mono Set.sdiff_subset)).2
  have hglobal := (show AnalyticOnNhd ℂ A ((L.lattice : Set ℂ) \ {0})ᶜ from
    fun x _ => hA x).eqOn_of_preconnected_of_eventuallyEq hB hconn (by simp) hnear
  have hz0 : z ≠ 0 := fun h => hz (h ▸ L.lattice.zero_mem)
  exact (hglobal (fun h => hz h.1)).trans (hB_eq z hz0)

