-- Prove2me | solution 1 for OptStopC1.TimeDeriv.theorem_15
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:53:46.805216+00:00
-- url     : https://prove2.me/submissions/53d2285a-d18c-4dce-b98e-0b67c4a3fad9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OptStopC1_TimeDeriv_Flow
import Definitions.Def_OptStopC1_TimeDeriv_Problem
import Definitions.Def_OptStopC1_TimeDeriv_Generator
import Definitions.Def_OptStopC1_TimeDeriv_Hypotheses
import Theorems.Thm_OptStopC1_TimeDeriv_liminf_5_17
import Theorems.Thm_OptStopC1_TimeDeriv_limsup_5_20

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

/-- Mean-value estimate: if `g a = 0`, `g` is continuous on `[a, b]` and at every point of
`(a, b)` where `g ≠ 0` it has a derivative bounded by `c`, then `|g b| ≤ c (b - a)`. -/
lemma optStopThm15_mvt_aux (g : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b) (hc : 0 ≤ c)
    (hcont : ContinuousOn g (Set.Icc a b)) (ha : g a = 0)
    (hd : ∀ u ∈ Set.Ioo a b, g u ≠ 0 → ∃ d, HasDerivAt g d u ∧ |d| ≤ c) :
    |g b| ≤ c * (b - a) := by
  by_cases hb : g b = 0
  · rw [hb, abs_zero]; exact mul_nonneg hc (sub_nonneg.2 hab)
  set S := Set.Icc a b ∩ g ⁻¹' {0} with hS
  have hSc : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSne : S.Nonempty := ⟨a, ⟨le_rfl, hab⟩, ha⟩
  have hSb : BddAbove S := ⟨b, fun u hu => hu.1.2⟩
  set s' := sSup S
  have hs'S : s' ∈ S := hSc.csSup_mem hSne hSb
  have hs'b : s' < b := by
    refine lt_of_le_of_ne hs'S.1.2 ?_
    intro h; apply hb; have := hs'S.2; rw [h] at this; exact this
  have hpos : ∀ u ∈ Set.Ioc s' b, g u ≠ 0 := by
    intro u hu h0
    have : u ∈ S := ⟨⟨le_trans hs'S.1.1 hu.1.le, hu.2⟩, h0⟩
    exact absurd (le_csSup hSb this) (not_le.2 hu.1)
  have hdiff : DifferentiableOn ℝ g (Set.Ioo s' b) := by
    intro u hu
    obtain ⟨d, hd1, -⟩ := hd u ⟨lt_of_le_of_lt hs'S.1.1 hu.1, hu.2⟩ (hpos u ⟨hu.1, hu.2.le⟩)
    exact hd1.differentiableAt.differentiableWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope g hs'b
    (hcont.mono (Set.Icc_subset_Icc hs'S.1.1 le_rfl)) hdiff
  obtain ⟨d, hd1, hd2⟩ := hd ξ ⟨lt_of_le_of_lt hs'S.1.1 hξ.1, hξ.2⟩ (hpos ξ ⟨hξ.1, hξ.2.le⟩)
  rw [hd1.deriv, hs'S.2, sub_zero] at hξeq
  have hne : b - s' ≠ 0 := by linarith
  have hgb : g b = d * (b - s') := by rw [hξeq]; field_simp
  rw [hgb, abs_mul, abs_of_pos (by linarith : (0:ℝ) < b - s')]
  calc |d| * (b - s') ≤ c * (b - s') := mul_le_mul_of_nonneg_right hd2 (by linarith)
    _ ≤ c * (b - a) := mul_le_mul_of_nonneg_left (by linarith [hs'S.1.1]) hc

open OptStopC1.TimeDeriv in
theorem solution {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : StoppingProblem m Ω) (c : GenCoeffs m)
    (hM : M.Thm15Global c) (z : ℝ × Space m) (hz : z ∈ M.boundary)
    (hloc : M.Thm15AtPoint c z)
    (hPR : IsProbRegular M.P M.T M.X (interior M.stoppingSet) z) :
    HasDerivWithinAt (fun s => M.value (s, z.2)) (timeDeriv M.T M.G z) (Set.Icc 0 M.T) z.1 ∧
    Tendsto (timeDeriv M.T M.value) (𝓝[M.contSet] z) (𝓝 (timeDeriv M.T M.G z)) := by
  have hT : 0 < M.T := hM.standing.T_pos
  have : IsProbabilityMeasure M.P := hM.standing.prob
  -- `G ≤ V` on the domain (stop immediately).
  have hVG : ∀ p ∈ domain m M.T, M.G p ≤ M.value p := by
    intro p hp
    obtain ⟨-, -, τs, -, -, hopt⟩ := hM.well_posed p hp
    have hp1 : p.1 ≤ M.T := hp.1.2
    have hadm : M.IsAdmissible p (fun _ => 0) := by
      refine ⟨?_, fun ω => ?_⟩
      · exact isStoppingTime_const M.𝔽 _
      · simp; linarith
    have hgain : M.gain p (fun _ => 0) = M.G p := by
      unfold StoppingProblem.gain StoppingProblem.payoff StoppingProblem.discount
      simp [hM.standing.flow.start]
    rw [← hgain]
    refine le_csSup ⟨M.gain p τs, ?_⟩ ⟨_, hadm, rfl⟩
    rintro v ⟨τ, hτ, rfl⟩
    exact hopt τ hτ
  have hdomIcc : ∀ x : Space m, Set.MapsTo (fun s : ℝ => (s, x)) (Set.Icc 0 M.T)
      (domain m M.T) := fun x s hs => ⟨hs, Set.mem_univ _⟩
  have hgcont : ∀ x : Space m, Continuous (fun s : ℝ => (s, x)) := fun x =>
    continuous_id.prodMk continuous_const
  -- Part (b): the limit along `C`, from (5.17) and (5.20).
  have hlim : Tendsto (timeDeriv M.T M.value) (𝓝[M.contSet] z) (𝓝 (timeDeriv M.T M.G z)) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      by_contra hcon
      rw [Filter.not_eventually] at hcon
      have hfr : ∃ᶠ y in 𝓝[M.contSet] z, y ∈ M.contSet ∧ ¬ a < timeDeriv M.T M.value y :=
        hcon.and_eventually self_mem_nhdsWithin |>.mono fun y hy => ⟨hy.2, hy.1⟩
      obtain ⟨q, hqt, hqp⟩ := exists_seq_forall_of_frequently hfr
      have hq : Tendsto q atTop (𝓝 z) := hqt.mono_right nhdsWithin_le_nhds
      have := liminf_5_17 M c hM z hz hloc hPR q (fun n => (hqp n).1) hq a ha
      obtain ⟨n, hn⟩ := this.exists
      exact (hqp n).2 hn
    · intro b hb
      by_contra hcon
      rw [Filter.not_eventually] at hcon
      have hfr : ∃ᶠ y in 𝓝[M.contSet] z, y ∈ M.contSet ∧ ¬ timeDeriv M.T M.value y < b :=
        hcon.and_eventually self_mem_nhdsWithin |>.mono fun y hy => ⟨hy.2, hy.1⟩
      obtain ⟨q, hqt, hqp⟩ := exists_seq_forall_of_frequently hfr
      have hq : Tendsto q atTop (𝓝 z) := hqt.mono_right nhdsWithin_le_nhds
      have := limsup_5_20 M c hM z hz hloc hPR q (fun n => (hqp n).1) hq b hb
      obtain ⟨n, hn⟩ := this.exists
      exact (hqp n).2 hn
  refine ⟨?_, hlim⟩
  -- Part (a): `∂_t V(z)` exists and equals `∂_t G(z)`.
  -- `C = domain ∩ U` with `U` open.
  obtain ⟨U, hUo, hU⟩ : ∃ U : Set (ℝ × Space m), IsOpen U ∧ M.contSet = domain m M.T ∩ U := by
    have hc : ContinuousOn (fun p => M.value p - M.G p) (domain m M.T) :=
      hM.value_cont.sub hM.standing.G_cont
    obtain ⟨u, hu, hue⟩ := continuousOn_iff'.1 hc (Set.Ioi 0) isOpen_Ioi
    refine ⟨u, hu, ?_⟩
    rw [Set.inter_comm, ← hue]
    ext p
    simp only [StoppingProblem.contSet, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Ioi, sub_pos]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hC1 := hM.value_C1
  -- the time derivative of `V` at points of `C`
  have hCd : ∀ q ∈ M.contSet, HasDerivWithinAt (fun s => M.value (s, q.2))
      (fderivWithin ℝ M.value M.contSet q ((1 : ℝ), (0 : Space m))) (Set.Icc 0 M.T) q.1 := by
    intro q hq
    have hV : HasFDerivWithinAt M.value (fderivWithin ℝ M.value M.contSet q) M.contSet q :=
      ((hC1.differentiableOn one_ne_zero) q hq).hasFDerivWithinAt
    have hg : HasDerivWithinAt (fun s : ℝ => (s, q.2)) ((1 : ℝ), (0 : Space m))
        (Set.Icc 0 M.T ∩ (fun s : ℝ => (s, q.2)) ⁻¹' U) q.1 :=
      ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)).hasDerivWithinAt
    have hmaps : Set.MapsTo (fun s : ℝ => (s, q.2))
        (Set.Icc 0 M.T ∩ (fun s : ℝ => (s, q.2)) ⁻¹' U) M.contSet := by
      intro s hs
      rw [hU]
      exact ⟨hdomIcc q.2 hs.1, hs.2⟩
    have hV' : HasFDerivWithinAt M.value (fderivWithin ℝ M.value M.contSet q) M.contSet
        (q.1, q.2) := by simpa using hV
    have := hV'.comp_hasDerivWithinAt q.1 hg hmaps
    have hUn : (fun s : ℝ => (s, q.2)) ⁻¹' U ∈ 𝓝 q.1 := by
      apply (hgcont q.2).continuousAt.preimage_mem_nhds
      apply hUo.mem_nhds
      have : q ∈ domain m M.T ∩ U := hU ▸ hq
      simpa using this.2
    exact (hasDerivWithinAt_inter hUn).1 this
  have hCeq : ∀ q ∈ M.contSet, HasDerivWithinAt (fun s => M.value (s, q.2))
      (timeDeriv M.T M.value q) (Set.Icc 0 M.T) q.1 := by
    intro q hq
    have := hCd q hq
    rwa [← this.derivWithin (uniqueDiffOn_Icc hT q.1 hq.1.1)] at this
  have hzD := hz.1
  have hzdom : z ∈ domain m M.T := hzD.1
  set x := z.2
  set t0 := z.1
  set g : ℝ → ℝ := fun s => M.value (s, x) - M.G (s, x) with hgdef
  have hg0 : g t0 = 0 := by
    simp only [hgdef, t0, x, Prod.mk.eta]; rw [hzD.2, sub_self]
  have hgnn : ∀ s ∈ Set.Icc 0 M.T, 0 ≤ g s := fun s hs =>
    sub_nonneg.2 (hVG _ (hdomIcc x hs))
  have hgcontI : ContinuousOn g (Set.Icc 0 M.T) :=
    (hM.value_cont.comp (hgcont x).continuousOn (hdomIcc x)).sub
      (hM.standing.G_cont.comp (hgcont x).continuousOn (hdomIcc x))
  -- derivative of `g` at interior points of `C`
  have hgd : ∀ u ∈ Set.Ioo 0 M.T, (u, x) ∈ M.contSet →
      HasDerivAt g (timeDeriv M.T M.value (u, x) - timeDeriv M.T M.G (u, x)) u := by
    intro u hu huC
    have hIcc : Set.Icc 0 M.T ∈ 𝓝 u := Icc_mem_nhds hu.1 hu.2
    have h1 := (hCeq (u, x) huC).hasDerivAt hIcc
    have h2 := ((hM.G_C12.1 (u, x) huC.1).hasDerivWithinAt).hasDerivAt hIcc
    exact h1.sub h2
  -- smallness of `V_t - G_t` near `z` along `C`
  have hsmall : Tendsto (fun y => timeDeriv M.T M.value y - timeDeriv M.T M.G y)
      (𝓝[M.contSet] z) (𝓝 0) := by
    have hG : Tendsto (timeDeriv M.T M.G) (𝓝[M.contSet] z) (𝓝 (timeDeriv M.T M.G z)) :=
      ((hM.G_C12.2.1 z hzdom).mono (fun q hq => hq.1)).tendsto
    simpa using hlim.sub hG
  have hGd : HasDerivWithinAt (fun s => M.G (s, x)) (timeDeriv M.T M.G z) (Set.Icc 0 M.T) t0 :=
    (hM.G_C12.1 z hzdom).hasDerivWithinAt
  have hgD : HasDerivWithinAt g 0 (Set.Icc 0 M.T) t0 := by
    rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro ε hε
    have hev : ∀ᶠ y in 𝓝[M.contSet] z,
        |timeDeriv M.T M.value y - timeDeriv M.T M.G y| ≤ ε := by
      have := hsmall.eventually (Metric.closedBall_mem_nhds (0 : ℝ) hε)
      filter_upwards [this] with y hy
      simpa [Real.dist_eq] using hy
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.1 hev
    have hball : Metric.ball t0 r ∈ 𝓝[Set.Icc 0 M.T] t0 :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t0 hr)
    filter_upwards [hball, self_mem_nhdsWithin] with s hs hsI
    rw [hg0, sub_zero, smul_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs]
    have hdist : ∀ u, |u - t0| < r → dist (u, x) z < r := by
      intro u hu
      have : dist (u, x) z = dist u t0 := by
        rw [Prod.dist_eq]; simp [x, t0]
      rw [this, Real.dist_eq]; exact hu
    have hsr : |s - t0| < r := by rw [← Real.dist_eq]; exact hs
    have hbound : ∀ u ∈ Set.Ioo 0 M.T, |u - t0| < r → g u ≠ 0 →
        ∃ d, HasDerivAt g d u ∧ |d| ≤ ε := by
      intro u hu hur hgu
      have huC : (u, x) ∈ M.contSet := by
        refine ⟨hdomIcc x ⟨hu.1.le, hu.2.le⟩, ?_⟩
        have := lt_of_le_of_ne (hgnn u ⟨hu.1.le, hu.2.le⟩) (Ne.symm hgu)
        simp only [hgdef] at this
        linarith
      exact ⟨_, hgd u hu huC, hrsub ⟨hdist u hur, huC⟩⟩
    rcases le_total t0 s with hts | hst
    · have := optStopThm15_mvt_aux g t0 s ε hts hε.le
        (hgcontI.mono (Set.Icc_subset_Icc hzdom.1.1 hsI.2)) hg0
        (fun u hu hgu => hbound u ⟨lt_of_le_of_lt hzdom.1.1 hu.1, lt_of_lt_of_le hu.2 hsI.2⟩
          (by rw [abs_of_pos (by linarith [hu.1])]; rw [abs_of_nonneg (by linarith)] at hsr
              linarith [hu.2]) hgu)
      rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ s - t0)]
    · -- reflect: apply the estimate to `u ↦ g (-u)` on `[-t0, -s]`
      have hcont' : ContinuousOn (fun u => g (-u)) (Set.Icc (-t0) (-s)) := by
        refine hgcontI.comp continuous_neg.continuousOn ?_
        intro u hu
        exact ⟨by linarith [hsI.1, hu.2], by linarith [hzdom.1.2, hu.1]⟩
      have := optStopThm15_mvt_aux (fun u => g (-u)) (-t0) (-s) ε (by linarith) hε.le hcont'
        (by simp [hg0])
        (by
          intro u hu hgu
          obtain ⟨d, hd1, hd2⟩ := hbound (-u)
            ⟨by linarith [hsI.1, hu.2], by linarith [hzdom.1.2, hu.1]⟩
            (by rw [abs_of_neg (by linarith [hu.1])]
                rw [abs_of_nonpos (by linarith)] at hsr
                linarith [hu.2]) hgu
          refine ⟨d * (-1), ?_, by simpa using hd2⟩
          exact hd1.comp u (hasDerivAt_neg u))
      simp only [neg_neg] at this
      rw [abs_of_nonpos (by linarith : s - t0 ≤ 0), neg_sub]
      calc |g s| ≤ ε * (-s - -t0) := this
        _ = ε * (t0 - s) := by ring
  have := hgD.add hGd
  simp only [zero_add] at this
  refine this.congr (fun s _ => ?_) ?_
  · simp [hgdef]
  · simp [hgdef]
