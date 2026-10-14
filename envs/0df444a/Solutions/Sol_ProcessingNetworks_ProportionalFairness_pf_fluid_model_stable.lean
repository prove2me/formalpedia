-- Prove2me | solution 1 for ProcessingNetworks.ProportionalFairness.pf_fluid_model_stable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T19:57:16.084934+00:00
-- url     : https://prove2.me/submissions/1cd3ddf8-b062-49f8-baf1-94dd8c2f9bec

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_FluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_Aggregation

set_option autoImplicit false

open MeasureTheory Set Filter Topology

/-- Decrease on an interval: continuous `f`, right-Dini bounded by `M` everywhere on `[τ,t)`,
right-Dini `≤ -ε` a.e. on `(τ,t)`  ⇒  `f t ≤ f τ - ε (t-τ)`. -/
lemma dini_decrease_on (f : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε) (τ t : ℝ) (hτt : τ < t)
    (hcont : ContinuousOn f (Icc τ t))
    (M : ℝ) (hM : 0 ≤ M)
    (hbdd : ∀ u ∈ Ico τ t, ∀ᶠ z in 𝓝[>] u, f z - f u ≤ M * (z - u))
    (hdrift : ∀ᵐ u ∂volume, u ∈ Ioo τ t → ∀ η > 0,
      ∀ᶠ z in 𝓝[>] u, f z - f u ≤ (-ε + η) * (z - u)) :
    f t ≤ f τ - ε * (t - τ) := by
  set H : ℝ → ℝ := fun u => M * u - f u with hH
  -- H monotone on [τ,t]
  have hmono : MonotoneOn H (Icc τ t) := by
    intro a ha b hb hab
    have hGc : ContinuousOn (fun u => f u - M * u) (Icc a b) := by
      have h1 : ContinuousOn f (Icc a b) := hcont.mono (Icc_subset_Icc ha.1 hb.2)
      exact h1.sub (continuousOn_const.mul continuousOn_id)
    have key := image_le_of_liminf_slope_right_le_deriv_boundary (f := fun u => f u - M * u)
      (a := a) (b := b) hGc (B := fun _ => f a - M * a) (B' := fun _ => 0) le_rfl
      continuousOn_const (fun x _ => hasDerivWithinAt_const x _ _) ?_ (x := b) ⟨hab, le_rfl⟩
    · simp only [hH]; linarith
    · intro x hx r hr
      have hx' : x ∈ Ico τ t := ⟨le_trans ha.1 hx.1, lt_of_lt_of_le hx.2 hb.2⟩
      have hev := (hbdd x hx').and (eventually_mem_nhdsWithin : ∀ᶠ z in 𝓝[>] x, z ∈ Ioi x)
      refine hev.frequently.mono ?_
      rintro z ⟨hz1, hz2⟩
      have hz2' : x < z := hz2
      rw [slope_def_field]
      have : (f z - M * z) - (f x - M * x) ≤ 0 := by nlinarith
      have h0 : ((f z - M * z) - (f x - M * x)) / (z - x) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg this (by linarith)
      linarith
  have hHnn : H τ ≤ H t := hmono ⟨le_rfl, hτt.le⟩ ⟨hτt.le, le_rfl⟩ hτt.le
  have hdiff : ∀ᵐ u ∂volume, u ∈ Icc τ t → DifferentiableWithinAt ℝ H (Icc τ t) u :=
    hmono.ae_differentiableWithinAt_of_mem
  have hnull := ae_iff.mp hdrift
  obtain ⟨N, hNsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null hnull
  have hdiff0 := ae_iff.mp hdiff
  obtain ⟨N2, hN2sub, hN2meas, hN20⟩ := exists_measurable_superset_of_null hdiff0
  set S : Set ℝ := Ioo τ t \ (N ∪ N2) with hS
  have hSmeas : MeasurableSet S := measurableSet_Ioo.diff (hNmeas.union hN2meas)
  have hSsub : S ⊆ Ioo τ t := sdiff_subset
  have hSvol : volume (Ioo τ t) ≤ volume S := by
    apply measure_mono_ae
    rw [ae_le_set]
    refine measure_mono_null ?_ (measure_union_null hN0 hN20)
    intro u hu
    by_contra h
    exact hu.2 ⟨hu.1, h⟩
  have hderivS : ∀ u ∈ S, HasDerivWithinAt H (M - deriv f u) S u ∧ deriv f u ≤ -ε := by
    intro u hu
    have hu1 : u ∈ Ioo τ t → ∀ η > 0, ∀ᶠ z in 𝓝[>] u, f z - f u ≤ (-ε + η) * (z - u) := by
      by_contra h
      exact hu.2 (Or.inl (hNsub h))
    have hu2 : u ∈ Icc τ t → DifferentiableWithinAt ℝ H (Icc τ t) u := by
      by_contra h
      exact hu.2 (Or.inr (hN2sub h))
    have hmem := hSsub hu
    have hHd : DifferentiableAt ℝ H u :=
      (hu2 (Ioo_subset_Icc_self hmem)).differentiableAt (Icc_mem_nhds hmem.1 hmem.2)
    have hfd : DifferentiableAt ℝ f u := by
      have : f = fun x => M * x - H x := by funext x; simp [hH]
      rw [this]
      exact (differentiableAt_const M |>.mul differentiableAt_id).sub hHd
    have hHder : HasDerivAt H (M - deriv f u) u := by
      have h := ((hasDerivAt_id u).const_mul M).sub hfd.hasDerivAt
      have hfun : H = (fun y => M * id y) - f := by funext x; simp [hH]
      rw [hfun]; simpa using h
    refine ⟨hHder.hasDerivWithinAt, ?_⟩
    have hsl := (hasDerivAt_iff_tendsto_slope.mp hfd.hasDerivAt).mono_left
      (nhdsWithin_mono u (show Ioi u ⊆ {u}ᶜ from fun y hy => ne_of_gt hy))
    refine le_of_forall_pos_le_add (fun η hη => ?_)
    have hle : deriv f u ≤ -ε + η := by
      refine le_of_tendsto hsl ?_
      filter_upwards [hu1 hmem η hη, (eventually_mem_nhdsWithin : ∀ᶠ z in 𝓝[>] u, z ∈ Ioi u)]
        with z hz hz2
      have hz2' : u < z := hz2
      rw [slope_def_field, div_le_iff₀ (by linarith)]
      exact hz
    linarith
  have hlint := lintegral_deriv_eq_volume_image_of_monotoneOn (f := H)
    (f' := fun x => M - deriv f x) hSmeas (fun x hx => (hderivS x hx).1)
    (hmono.mono (hSsub.trans Ioo_subset_Icc_self))
  have hstep : ENNReal.ofReal (M + ε) * volume S ≤ ENNReal.ofReal (H t - H τ) := by
    calc ENNReal.ofReal (M + ε) * volume S
        = ∫⁻ _ in S, ENNReal.ofReal (M + ε) := by rw [setLIntegral_const]
      _ ≤ ∫⁻ x in S, ENNReal.ofReal (M - deriv f x) := by
          apply setLIntegral_mono' hSmeas
          intro x hx
          apply ENNReal.ofReal_le_ofReal
          have := (hderivS x hx).2
          linarith
      _ = volume (H '' S) := hlint
      _ ≤ volume (Icc (H τ) (H t)) := by
          apply measure_mono
          rintro _ ⟨u, hu, rfl⟩
          have hu' := hSsub hu
          exact ⟨hmono ⟨le_rfl, hτt.le⟩ ⟨hu'.1.le, hu'.2.le⟩ hu'.1.le,
            hmono ⟨hu'.1.le, hu'.2.le⟩ ⟨hτt.le, le_rfl⟩ hu'.2.le⟩
      _ = ENNReal.ofReal (H t - H τ) := Real.volume_Icc
  have h2 : ENNReal.ofReal (M + ε) * ENNReal.ofReal (t - τ) ≤ ENNReal.ofReal (H t - H τ) := by
    refine le_trans ?_ hstep
    gcongr
    simpa using hSvol
  rw [← ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_le_ofReal_iff (by linarith)] at h2
  simp only [hH] at h2
  nlinarith

/-- Extinction criterion in difference-quotient form, on `[s,∞)`. -/
lemma dini_extinction_from (f : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε) (s : ℝ)
    (hf0 : ∀ u, s ≤ u → 0 ≤ f u)
    (hcont : ContinuousOn f (Ici s))
    (hbdd : ∀ b : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ u, s ≤ u → u < b →
      ∀ᶠ z in 𝓝[>] u, f z - f u ≤ M * (z - u))
    (hdrift : ∀ᵐ u ∂volume, s < u → 0 < f u → ∀ η > 0,
      ∀ᶠ z in 𝓝[>] u, f z - f u ≤ (-ε + η) * (z - u)) :
    ∀ t, s + f s / ε ≤ t → f t = 0 := by
  intro t ht
  by_contra hne
  have hfs : 0 ≤ f s := hf0 s le_rfl
  have hst : s ≤ t := by
    have : 0 ≤ f s / ε := div_nonneg hfs hε.le
    linarith
  have hpos_t : 0 < f t := lt_of_le_of_ne (hf0 t hst) (Ne.symm hne)
  obtain ⟨M, hM0, hM⟩ := hbdd t
  have hst' : s < t := by
    rcases lt_or_eq_of_le hst with h | h
    · exact h
    · rw [← h] at hpos_t ht
      have : 0 < f s / ε := div_pos hpos_t hε
      linarith
  -- choose the last zero before t
  obtain ⟨τ, hsτ, hτt, hτ, hposτ⟩ : ∃ τ, s ≤ τ ∧ τ < t ∧ (f τ = 0 ∨ τ = s) ∧
      ∀ u ∈ Ioo τ t, 0 < f u := by
    set Zs : Set ℝ := {u | u ∈ Icc s t ∧ f u = 0} with hZ
    by_cases hne : Zs.Nonempty
    · have hclosed : IsClosed Zs := by
        have : ContinuousOn f (Icc s t) := hcont.mono Icc_subset_Ici_self
        have h2 := this.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_singleton (x := (0:ℝ)))
        convert h2 using 1
        ext u; simp [hZ, and_comm]
      have hbdd' : BddAbove Zs := ⟨t, fun u hu => hu.1.2⟩
      have hmem := hclosed.csSup_mem hne hbdd'
      set τ := sSup Zs with hτdef
      have hτle : τ ≤ t := csSup_le hne (fun u hu => hu.1.2)
      have hτne : τ ≠ t := by
        intro h
        rw [h] at hmem
        exact hne.elim fun _ _ => absurd hmem.2 (ne_of_gt hpos_t)
      refine ⟨τ, hmem.1.1, lt_of_le_of_ne hτle hτne, Or.inl hmem.2, ?_⟩
      intro u hu
      have hu_s : s ≤ u := le_trans hmem.1.1 hu.1.le
      have hu_ne : f u ≠ 0 := by
        intro h0
        have : u ∈ Zs := ⟨⟨hu_s, hu.2.le⟩, h0⟩
        exact absurd (le_csSup hbdd' this) (not_le.mpr hu.1)
      exact lt_of_le_of_ne (hf0 u hu_s) (Ne.symm hu_ne)
    · refine ⟨s, le_rfl, hst', Or.inr rfl, ?_⟩
      intro u hu
      have hu_s : s ≤ u := hu.1.le
      have hu_ne : f u ≠ 0 := by
        intro h0
        exact hne ⟨u, ⟨hu_s, hu.2.le⟩, h0⟩
      exact lt_of_le_of_ne (hf0 u hu_s) (Ne.symm hu_ne)
  have hdec := dini_decrease_on f ε hε τ t hτt
    (hcont.mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hsτ)))
    M hM0 (fun u hu => hM u (le_trans hsτ hu.1) hu.2)
    (by
      filter_upwards [hdrift] with u hu hu_mem
      exact hu (lt_of_le_of_lt hsτ hu_mem.1) (hposτ u hu_mem))
  rcases hτ with h0 | hs
  · have : 0 < ε * (t - τ) := mul_pos hε (by linarith)
    linarith
  · subst hs
    have : f τ / ε ≤ t - τ := by linarith
    rw [div_le_iff₀ hε] at this
    nlinarith

open ProcessingNetworks.ProportionalFairness


/-- On a solution, at a time `t>0` where `Z t i > 0`, the right derivative of `D i` is
`ψ Z/(Y m)`, with `|ψ| ≤ R`. -/
lemma PF_Ddot_formula {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t) (i : Fin I) (hZ : 0 < Zh t i) :
    HasDerivAt (fun u => Dh u i)
      (psi dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) (dat.grp i) * Zh t i /
        groupAggregate dat.grp (Zh t) (dat.grp i) / dat.m i) t := by
  obtain ⟨-, -, -, hD, -, hT⟩ := hsol
  have h1 := (hT t ht i hZ).div_const (dat.m i)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ici_mem_nhds ht] with u hu
  exact hD u hu i

lemma PF_psi_abs_le {L : ℕ} (A : Set (Fin L → ℝ)) (R : ℝ) (hR : ∀ x ∈ A, ‖x‖ ≤ R)
    (z : Fin L → ℝ) (ℓ : Fin L) : |psi A z ℓ| ≤ max R 0 := by
  unfold psi
  by_cases hz : 0 < z ℓ
  · rw [if_pos hz]
    by_cases h : ∃ x, IsPFMaximizer A z x
    · rw [dif_pos h]
      have hx := (Classical.choose_spec h).1
      calc |Classical.choose h ℓ| = ‖Classical.choose h ℓ‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖Classical.choose h‖ := norm_le_pi_norm _ _
        _ ≤ R := hR _ hx
        _ ≤ max R 0 := le_max_left _ _
    · rw [dif_neg h]; simp
  · rw [if_neg hz]; simp

lemma PF_log_le_of_abs_le (x B : ℝ) (hB : 0 ≤ B) (hx : |x| ≤ B) :
    Real.log x ≤ max 0 (Real.log B) := by
  by_cases h0 : x = 0
  · simp [h0]
  · have hpos : 0 < |x| := abs_pos.mpr h0
    rw [← Real.log_abs]
    exact (Real.log_le_log hpos hx).trans (le_max_right _ _)

theorem PF_entropy_le_const {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (alpha : Fin I → ℝ) (hα : ∀ i, 0 < alpha i) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (Ah Dh Th Zh : ℝ → Fin I → ℝ), IsPFFluidModelSolution dat Ah Dh Th Zh →
      ∀ t : ℝ, 0 < t →
        ∑ i, Zh t i * Real.log (derivWithin (fun s => Dh s i) (Set.Ici t) t / alpha i) ≤
          c * ∑ i, Zh t i := by
  obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le.mp hdom.1)
  set R0 : ℝ := max R 0 with hR0
  have hR0nn : 0 ≤ R0 := le_max_right _ _
  set ci : Fin I → ℝ := fun i => max 0 (Real.log (R0 / (dat.m i * alpha i))) with hci
  have hcinn : ∀ i, 0 ≤ ci i := fun i => le_max_left _ _
  refine ⟨∑ i, ci i, Finset.sum_nonneg (fun i _ => hcinn i), ?_⟩
  intro Ah Dh Th Zh hsol t ht
  have hZnn : ∀ i, 0 ≤ Zh t i := fun i => hsol.2.1 t ht.le i
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hcle : ci i ≤ ∑ j, ci j :=
    Finset.single_le_sum (f := ci) (fun j _ => hcinn j) (Finset.mem_univ i)
  by_cases hZ : Zh t i = 0
  · simp [hZ]
  · have hZpos : 0 < Zh t i := lt_of_le_of_ne (hZnn i) (Ne.symm hZ)
    have hD := PF_Ddot_formula dat Ah Dh Th Zh hsol t ht i hZpos
    rw [hD.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici t)]
    set Y := groupAggregate dat.grp (Zh t) (dat.grp i) with hY
    have hYge : Zh t i ≤ Y := by
      unfold groupAggregate at hY
      rw [hY]
      exact Finset.single_le_sum (f := fun j => Zh t j) (fun j _ => hZnn j)
        (by simp : i ∈ Finset.univ.filter (fun j => dat.grp j = dat.grp i))
    have hYpos : 0 < Y := lt_of_lt_of_le hZpos hYge
    have hpsi := PF_psi_abs_le dat.TildeAllocSet R hR (groupAggregate dat.grp (Zh t)) (dat.grp i)
    set ps := psi dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) (dat.grp i) with hps
    have hmi := dat.hm i
    have hai := hα i
    have habs : |ps * Zh t i / Y / dat.m i / alpha i| ≤ R0 / (dat.m i * alpha i) := by
      have hq : Zh t i / Y ≤ 1 := (div_le_one hYpos).mpr hYge
      have hq0 : 0 ≤ Zh t i / Y := div_nonneg hZpos.le hYpos.le
      have : ps * Zh t i / Y / dat.m i / alpha i = ps * (Zh t i / Y) / (dat.m i * alpha i) := by
        field_simp
      rw [this, abs_div, abs_mul, abs_of_nonneg hq0, abs_of_pos (mul_pos hmi hai)]
      apply div_le_div_of_nonneg_right _ (mul_pos hmi hai).le
      calc |ps| * (Zh t i / Y) ≤ R0 * 1 := mul_le_mul hpsi hq hq0 hR0nn
        _ = R0 := mul_one _
    have hlog := PF_log_le_of_abs_le _ _ (div_nonneg hR0nn (mul_pos hmi hai).le) habs
    rw [mul_comm (∑ j, ci j)]
    exact mul_le_mul_of_nonneg_left (hlog.trans hcle) hZpos.le

lemma PF_ae_regular {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) :
    ∀ᵐ t ∂volume, 0 < t → RegularPoint Ah Dh Th Zh t := by
  obtain ⟨hZ, -, hA, hD, ⟨hT0, hmono, Kc, hK⟩, -⟩ := hsol
  set K' : NNReal := Real.toNNReal Kc with hK'
  set T' : ℝ → Fin I → ℝ := fun t => Th (max t 0) with hT'
  have hlip : LipschitzWith K' T' := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [dist_pi_le_iff (by positivity)]
    intro i
    have key : ∀ a b : ℝ, a ≤ b → |Th (max b 0) i - Th (max a 0) i| ≤ (max Kc 0) * (b - a) := by
      intro a b hab
      have h1 := hK (max a 0) (max b 0) (le_max_right _ _) (max_le_max hab le_rfl) i
      have hd0 : 0 ≤ max b 0 - max a 0 := by linarith [max_le_max hab (le_refl (0:ℝ))]
      have hd1 : max b 0 - max a 0 ≤ b - a := by
        simp only [max_def]; split_ifs <;> linarith
      calc _ ≤ Kc * (max b 0 - max a 0) := h1
        _ ≤ max Kc 0 * (max b 0 - max a 0) := mul_le_mul_of_nonneg_right (le_max_left _ _) hd0
        _ ≤ max Kc 0 * (b - a) := mul_le_mul_of_nonneg_left hd1 (le_max_right _ _)
    have hco : (K' : ℝ) = max Kc 0 := Real.coe_toNNReal' Kc
    rw [Real.dist_eq, Real.dist_eq, hco]
    rcases le_total s t with hst | hst
    · rw [abs_sub_comm, abs_sub_comm s t, abs_of_nonneg (by linarith : 0 ≤ t - s)]
      exact key s t hst
    · rw [abs_of_nonneg (by linarith : 0 ≤ s - t)]
      exact key t s hst
  filter_upwards [hlip.ae_differentiableAt_real] with t hdt ht
  have hev : Th =ᶠ[𝓝 t] T' := by
    filter_upwards [Ici_mem_nhds ht] with u hu
    simp only [hT', max_eq_left (show (0:ℝ) ≤ u from hu)]
  have hTd : DifferentiableAt ℝ Th t := (hev.differentiableAt_iff).mpr hdt
  have hDev : Dh =ᶠ[𝓝 t] fun u i => Th u i / dat.m i := by
    filter_upwards [Ici_mem_nhds ht] with u hu
    funext i; exact hD u hu i
  have hDd : DifferentiableAt ℝ Dh t := by
    rw [hDev.differentiableAt_iff]
    rw [differentiableAt_pi] at hTd ⊢
    intro i; exact (hTd i).div_const _
  have hAev : Ah =ᶠ[𝓝 t] fun u i => dat.lam i * u + ∑ k, dat.P k i * Dh u k := by
    filter_upwards [Ici_mem_nhds ht] with u hu
    funext i; exact hA u hu i
  have hAd : DifferentiableAt ℝ Ah t := by
    rw [hAev.differentiableAt_iff]
    rw [differentiableAt_pi] at hDd ⊢
    intro i
    exact (differentiableAt_const _ |>.mul differentiableAt_id).add
      (DifferentiableAt.fun_sum (fun k _ => (hDd k).const_mul _))
  have hZev : Zh =ᶠ[𝓝 t] fun u i => Zh 0 i + Ah u i - Dh u i := by
    filter_upwards [Ici_mem_nhds ht] with u hu
    funext i; exact congrFun (hZ u hu) i
  have hZd : DifferentiableAt ℝ Zh t := by
    rw [hZev.differentiableAt_iff]
    rw [differentiableAt_pi] at hDd hAd ⊢
    intro i
    exact ((differentiableAt_const _).add (hAd i)).sub (hDd i)
  exact ⟨hAd, hDd, hTd, hZd⟩

lemma PF_Z_tendsto {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) (i : Fin I) :
    Tendsto (fun s => Zh s i) (𝓝[>] 0) (𝓝 (Zh 0 i)) := by
  obtain ⟨hZ, -, hA, hD, ⟨hT0, hmono, Kc, hK⟩, -⟩ := hsol
  have hT : ∀ k, Tendsto (fun s => Th s k) (𝓝[>] 0) (𝓝 0) := by
    intro k
    have hb : Tendsto (fun s : ℝ => Kc * s) (𝓝[>] 0) (𝓝 0) := by
      have := (continuous_const_mul Kc).tendsto 0
      rw [mul_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (0:ℝ) < s := hs
    have := hK 0 s le_rfl hs'.le k
    rw [hT0] at this
    simpa [Real.norm_eq_abs] using this
  have hD' : ∀ k, Tendsto (fun s => Dh s k) (𝓝[>] 0) (𝓝 0) := by
    intro k
    have h1 := (hT k).div_const (dat.m k)
    simp only [zero_div] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hD s (le_of_lt hs) k).symm
  have hA' : Tendsto (fun s => dat.lam i * s + ∑ k, dat.P k i * Dh s k) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => dat.lam i * s) (𝓝[>] 0) (𝓝 0) := by
      have := (continuous_const_mul (dat.lam i)).tendsto 0
      rw [mul_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    have h2 : Tendsto (fun s => ∑ k, dat.P k i * Dh s k) (𝓝[>] 0) (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset (Fin I))
        (fun k _ => (hD' k).const_mul (dat.P k i))
      simpa using this
    simpa using h1.add h2
  have hfin := ((tendsto_const_nhds (x := Zh 0 i)).add hA').sub (hD' i)
  simp only [add_zero, sub_zero] at hfin
  refine hfin.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have := congrFun (hZ s (le_of_lt hs)) i
  rw [this, hA s (le_of_lt hs) i]

/-! ## PF optimization API -/

noncomputable def PFG {L : ℕ} (z x : Fin L → ℝ) : ℝ := ∑ ℓ, z ℓ * Real.log (x ℓ)

def PFGood {L : ℕ} (z x : Fin L → ℝ) : Prop := ∀ ℓ, 0 < z ℓ → x ℓ ≠ 0

lemma PF_sum_coe_ereal {α : Type*} (s : Finset α) (g : α → ℝ) :
    ∑ a ∈ s, ((g a : ℝ) : EReal) = ((∑ a ∈ s, g a : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]

lemma PF_sum_bot {α : Type*} (s : Finset α) (t : α → EReal) (ht : ∀ a, t a ≠ ⊤)
    (a : α) (ha : a ∈ s) (hb : t a = ⊥) : ∑ a ∈ s, t a = ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd ha (Finset.notMem_empty a)
  | insert b s hbs ih =>
    rw [Finset.sum_insert hbs]
    by_cases hab : a = b
    · subst hab; rw [hb, EReal.bot_add]
    · have : a ∈ s := by
        rcases Finset.mem_insert.mp ha with h | h
        · exact absurd h hab
        · exact h
      rw [ih this, EReal.add_bot]

lemma PF_f_term {L : ℕ} (z x : Fin L → ℝ) (ℓ : Fin L) (hz : 0 ≤ z ℓ) (hx : 0 < z ℓ → x ℓ ≠ 0) :
    (z ℓ : EReal) * extLog (x ℓ) = ((z ℓ * Real.log (x ℓ) : ℝ) : EReal) := by
  rcases eq_or_lt_of_le hz with h | h
  · rw [← h]; simp
  · have := hx h
    unfold extLog
    rw [if_neg this, EReal.coe_mul]

lemma PF_f_eq {L : ℕ} (z x : Fin L → ℝ) (hz : ∀ ℓ, 0 ≤ z ℓ) (hg : PFGood z x) :
    f z x = ((PFG z x : ℝ) : EReal) := by
  unfold f PFG
  rw [← PF_sum_coe_ereal]
  exact Finset.sum_congr rfl (fun ℓ _ => PF_f_term z x ℓ (hz ℓ) (hg ℓ))

lemma PF_f_bot {L : ℕ} (z x : Fin L → ℝ) (hz : ∀ ℓ, 0 ≤ z ℓ) (hg : ¬ PFGood z x) :
    f z x = ⊥ := by
  unfold PFGood at hg
  push Not at hg
  obtain ⟨ℓ, hℓ, hx⟩ := hg
  unfold f
  refine PF_sum_bot _ _ ?_ ℓ (Finset.mem_univ ℓ) ?_
  · intro k
    by_cases hk : x k = 0
    · unfold extLog
      rw [if_pos hk]
      rcases eq_or_lt_of_le (hz k) with h | h
      · rw [← h]; simp
      · rw [EReal.mul_bot_of_pos (EReal.coe_pos.mpr h)]; simp
    · unfold extLog
      rw [if_neg hk, ← EReal.coe_mul]
      exact EReal.coe_ne_top _
  · unfold extLog
    rw [if_pos hx, EReal.mul_bot_of_pos (EReal.coe_pos.mpr hℓ)]

lemma PF_max_fwd {L : ℕ} (A : Set (Fin L → ℝ)) (hdom : IsPFDomain A) (z x : Fin L → ℝ)
    (hz : ∀ ℓ, 0 ≤ z ℓ) (hm : IsPFMaximizer A z x) :
    x ∈ A ∧ PFGood z x ∧ ∀ y ∈ A, PFGood z y → PFG z y ≤ PFG z x := by
  obtain ⟨x0, hx0A, hx0pos⟩ := hdom.2.2.2.2
  have hg0 : PFGood z x0 := fun ℓ _ => (hx0pos ℓ).ne'
  have hgood : PFGood z x := by
    by_contra hng
    have hb := PF_f_bot z x hz hng
    have h1 := hm.2 x0 hx0A
    rw [hb, PF_f_eq z x0 hz hg0] at h1
    exact absurd (le_bot_iff.mp h1) (EReal.coe_ne_bot _)
  refine ⟨hm.1, hgood, fun y hy hgy => ?_⟩
  have h1 := hm.2 y hy
  rw [PF_f_eq z y hz hgy, PF_f_eq z x hz hgood] at h1
  exact EReal.coe_le_coe_iff.mp h1

lemma PF_max_bwd {L : ℕ} (A : Set (Fin L → ℝ)) (z x : Fin L → ℝ)
    (hz : ∀ ℓ, 0 ≤ z ℓ) (hxA : x ∈ A) (hgx : PFGood z x)
    (hmax : ∀ y ∈ A, PFGood z y → PFG z y ≤ PFG z x) : IsPFMaximizer A z x := by
  refine ⟨hxA, fun y hy => ?_⟩
  by_cases hgy : PFGood z y
  · rw [PF_f_eq z y hz hgy, PF_f_eq z x hz hgx]
    exact EReal.coe_le_coe_iff.mpr (hmax y hy hgy)
  · rw [PF_f_bot z y hz hgy]; exact bot_le

lemma PF_exists_max {L : ℕ} (A : Set (Fin L → ℝ)) (hdom : IsPFDomain A) (z : Fin L → ℝ)
    (hz : ∀ ℓ, 0 ≤ z ℓ) : ∃ x, IsPFMaximizer A z x := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hdom.1
  obtain ⟨x0, hx0A, hx0pos⟩ := hdom.2.2.2.2
  have hg0 : PFGood z x0 := fun ℓ _ => (hx0pos ℓ).ne'
  set R1 : ℝ := max R 1 with hR1
  have hR1one : 1 ≤ R1 := le_max_right _ _
  set ρ : ℝ := Real.log R1 with hρ
  have hρ0 : 0 ≤ ρ := Real.log_nonneg hR1one
  have hlogle : ∀ x ∈ A, ∀ ℓ, Real.log (x ℓ) ≤ ρ := by
    intro x hx ℓ
    have habs : |x ℓ| ≤ R1 := by
      calc |x ℓ| = ‖x ℓ‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖x‖ := norm_le_pi_norm _ _
        _ ≤ R := hR x hx
        _ ≤ R1 := le_max_left _ _
    by_cases h0 : x ℓ = 0
    · simp [h0, hρ0]
    · rw [← Real.log_abs]
      exact Real.log_le_log (abs_pos.mpr h0) habs
  set c0 : ℝ := PFG z x0 with hc0
  set Zs : ℝ := ∑ k, z k with hZs
  set δ : Fin L → ℝ := fun ℓ => Real.exp ((c0 - Zs * ρ) / z ℓ) with hδ
  have hbound : ∀ y ∈ A, PFGood z y → c0 ≤ PFG z y → ∀ ℓ, 0 < z ℓ → δ ℓ ≤ |y ℓ| := by
    intro y hy hgy hc ℓ hℓ
    have hsplit : PFG z y = z ℓ * Real.log (y ℓ) +
        ∑ k ∈ Finset.univ.erase ℓ, z k * Real.log (y k) := by
      unfold PFG
      exact (Finset.add_sum_erase Finset.univ (fun k => z k * Real.log (y k))
        (Finset.mem_univ ℓ)).symm
    have hrest : ∑ k ∈ Finset.univ.erase ℓ, z k * Real.log (y k) ≤ Zs * ρ := by
      calc ∑ k ∈ Finset.univ.erase ℓ, z k * Real.log (y k)
          ≤ ∑ k ∈ Finset.univ.erase ℓ, z k * ρ :=
            Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hlogle y hy k) (hz k))
        _ ≤ ∑ k, z k * ρ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun k _ _ => mul_nonneg (hz k) hρ0)
        _ = Zs * ρ := by rw [hZs, Finset.sum_mul]
    have h1 : c0 - Zs * ρ ≤ z ℓ * Real.log (y ℓ) := by linarith
    have h2 : (c0 - Zs * ρ) / z ℓ ≤ Real.log (y ℓ) := by
      rw [div_le_iff₀ hℓ]; linarith
    have hy0 : y ℓ ≠ 0 := hgy ℓ hℓ
    calc δ ℓ = Real.exp ((c0 - Zs * ρ) / z ℓ) := rfl
      _ ≤ Real.exp (Real.log |y ℓ|) := Real.exp_le_exp.mpr (by rwa [Real.log_abs])
      _ = |y ℓ| := Real.exp_log (abs_pos.mpr hy0)
  set K : Set (Fin L → ℝ) := {x | x ∈ A ∧ ∀ ℓ, 0 < z ℓ → δ ℓ ≤ |x ℓ|} with hK
  have hKclosed : IsClosed K := by
    have h1 : IsClosed {x : Fin L → ℝ | ∀ ℓ, 0 < z ℓ → δ ℓ ≤ |x ℓ|} := by
      have : {x : Fin L → ℝ | ∀ ℓ, 0 < z ℓ → δ ℓ ≤ |x ℓ|} =
          ⋂ ℓ, {x : Fin L → ℝ | 0 < z ℓ → δ ℓ ≤ |x ℓ|} := by ext x; simp
      rw [this]
      refine isClosed_iInter (fun ℓ => ?_)
      by_cases hℓ : 0 < z ℓ
      · simp only [hℓ, forall_true_left]
        exact isClosed_le continuous_const ((continuous_apply ℓ).abs)
      · simp [hℓ]
    exact hdom.2.1.inter h1
  have hKcompact : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded hKclosed ?_
    exact hdom.1.subset (fun x hx => hx.1)
  have hx0K : x0 ∈ K := by
    refine ⟨hx0A, fun ℓ hℓ => hbound x0 hx0A hg0 le_rfl ℓ hℓ⟩
  have hcont : ContinuousOn (PFG z) K := by
    unfold PFG
    refine continuousOn_finsetSum _ (fun ℓ _ => ?_)
    by_cases hℓ : 0 < z ℓ
    · refine continuousOn_const.mul ?_
      intro x hx
      have hδpos : 0 < δ ℓ := Real.exp_pos _
      have hx0 : x ℓ ≠ 0 := by
        intro h
        have := hx.2 ℓ hℓ
        rw [h, abs_zero] at this
        linarith
      exact ((Real.continuousAt_log hx0).comp (f := fun p : Fin L → ℝ => p ℓ)
        (continuous_apply ℓ).continuousAt).continuousWithinAt
    · have : z ℓ = 0 := le_antisymm (not_lt.mp hℓ) (hz ℓ)
      simp [this]
      exact continuousOn_const
  obtain ⟨xs, hxsK, hxsmax⟩ := hKcompact.exists_isMaxOn ⟨x0, hx0K⟩ hcont
  have hgxs : PFGood z xs := by
    intro ℓ hℓ h
    have := hxsK.2 ℓ hℓ
    rw [h, abs_zero] at this
    have hδpos : 0 < δ ℓ := Real.exp_pos _
    linarith
  refine ⟨xs, PF_max_bwd A z xs hz hxsK.1 hgxs ?_⟩
  intro y hy hgy
  by_cases hc : c0 ≤ PFG z y
  · have hyK : y ∈ K := ⟨hy, hbound y hy hgy hc⟩
    exact hxsmax hyK
  · push Not at hc
    have : PFG z x0 ≤ PFG z xs := hxsmax hx0K
    linarith

/-- Variational inequality for a PF maximizer (first-order optimality). -/
lemma PF_vi {L : ℕ} (A : Set (Fin L → ℝ)) (hdom : IsPFDomain A) (z x : Fin L → ℝ)
    (hz : ∀ ℓ, 0 ≤ z ℓ) (hm : IsPFMaximizer A z x) (y : Fin L → ℝ) (hy : y ∈ A) :
    ∑ ℓ, z ℓ * ((y ℓ - x ℓ) / x ℓ) ≤ 0 := by
  obtain ⟨hxA, hgx, hmax⟩ := PF_max_fwd A hdom z x hz hm
  set φ : ℝ → ℝ := fun θ => ∑ ℓ, z ℓ * Real.log ((1 - θ) * x ℓ + θ * y ℓ) with hφ
  have hterm : ∀ ℓ ∈ (Finset.univ : Finset (Fin L)),
      HasDerivAt (fun θ : ℝ => z ℓ * Real.log ((1 - θ) * x ℓ + θ * y ℓ))
        (z ℓ * ((y ℓ - x ℓ) / x ℓ)) 0 := by
    intro ℓ _
    rcases eq_or_lt_of_le (hz ℓ) with h0 | hpos
    · rw [← h0]; simp only [zero_mul]; exact hasDerivAt_const _ _
    · have hx : x ℓ ≠ 0 := hgx ℓ hpos
      have hin : HasDerivAt (fun θ : ℝ => (1 - θ) * x ℓ + θ * y ℓ) (y ℓ - x ℓ) 0 := by
        have := (((hasDerivAt_id (0:ℝ)).const_sub 1).mul_const (x ℓ)).add
          ((hasDerivAt_id (0:ℝ)).mul_const (y ℓ))
        exact this.congr_deriv (by ring)
      have hne : (1 - (0:ℝ)) * x ℓ + 0 * y ℓ ≠ 0 := by simpa using hx
      have := (hin.log hne).const_mul (z ℓ)
      simpa using this
  have hderiv : HasDerivAt φ (∑ ℓ, z ℓ * ((y ℓ - x ℓ) / x ℓ)) 0 :=
    HasDerivAt.fun_sum hterm
  have hev : ∀ᶠ θ in 𝓝[>] (0:ℝ), φ θ ≤ φ 0 := by
    have hgood : ∀ᶠ θ in 𝓝 (0:ℝ), ∀ ℓ, 0 < z ℓ → (1 - θ) * x ℓ + θ * y ℓ ≠ 0 := by
      refine Filter.eventually_all.mpr (fun ℓ => ?_)
      by_cases hℓ : 0 < z ℓ
      · have hc : Continuous fun θ : ℝ => (1 - θ) * x ℓ + θ * y ℓ := by fun_prop
        have : (1 - (0:ℝ)) * x ℓ + 0 * y ℓ ≠ 0 := by simpa using hgx ℓ hℓ
        filter_upwards [hc.continuousAt.eventually_ne this] with θ hθ _ using hθ
      · exact Filter.Eventually.of_forall (fun _ h => absurd h hℓ)
    have h01 : ∀ᶠ θ in 𝓝[>] (0:ℝ), θ ∈ Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
    filter_upwards [nhdsWithin_le_nhds hgood, h01] with θ hθ hθ01
    have hmemA : ((1 - θ) • x + θ • y) ∈ A :=
      hdom.2.2.1 hxA hy (by linarith [hθ01.2]) hθ01.1.le (by ring)
    have hG : PFGood z ((1 - θ) • x + θ • y) := by
      intro ℓ hℓ; simpa using hθ ℓ hℓ
    have := hmax _ hmemA hG
    have e1 : PFG z ((1 - θ) • x + θ • y) = φ θ := by simp [PFG, hφ]
    have e0 : PFG z x = φ 0 := by simp [PFG, hφ]
    rw [e1, e0] at this; exact this
  have hsl := (hasDerivAt_iff_tendsto_slope.mp hderiv).mono_left
    (nhdsWithin_mono 0 (show Ioi (0:ℝ) ⊆ {0}ᶜ from fun y hy => ne_of_gt hy))
  refine le_of_tendsto hsl ?_
  filter_upwards [hev, self_mem_nhdsWithin] with θ hθ hθ0
  rw [slope_def_field]
  have : (0:ℝ) < θ := hθ0
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

/-! ## Positivity of psi and the entropy sign (K5) -/

lemma PF_sum_fiber {I L : ℕ} (grp : Fin I → Fin L) (F : Fin I → ℝ) :
    ∑ i, F i = ∑ ℓ, ∑ i ∈ Finset.univ.filter (fun i => grp i = ℓ), F i :=
  (Finset.sum_fiberwise Finset.univ grp F).symm

lemma PF_psi_eq {L : ℕ} (A : Set (Fin L → ℝ)) (hdom : IsPFDomain A) (Y : Fin L → ℝ)
    (hY : ∀ ℓ, 0 ≤ Y ℓ) : ∃ x, IsPFMaximizer A Y x ∧ ∀ ℓ, 0 < Y ℓ → psi A Y ℓ = x ℓ := by
  have hex := PF_exists_max A hdom Y hY
  refine ⟨Classical.choose hex, Classical.choose_spec hex, fun ℓ hℓ => ?_⟩
  unfold psi
  rw [if_pos hℓ, dif_pos hex]

lemma PF_psi_pos {I L : ℕ} (dat : PFUnitaryNetworkData I L) (hdom : IsPFDomain dat.TildeAllocSet)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t) (ℓ : Fin L) (hℓ : 0 < groupAggregate dat.grp (Zh t) ℓ) :
    0 < psi dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) ℓ := by
  have hZnn : ∀ i, 0 ≤ Zh t i := fun i => hsol.2.1 t ht.le i
  have hYnn : ∀ ℓ, 0 ≤ groupAggregate dat.grp (Zh t) ℓ :=
    fun ℓ => Finset.sum_nonneg (fun i _ => hZnn i)
  obtain ⟨x, hxm, hpx⟩ := PF_psi_eq dat.TildeAllocSet hdom _ hYnn
  obtain ⟨-, hgood, -⟩ := PF_max_fwd dat.TildeAllocSet hdom _ x hYnn hxm
  have hxne : x ℓ ≠ 0 := hgood ℓ hℓ
  rw [hpx ℓ hℓ] at *
  -- find a positive component in group ℓ
  have hex : ∃ i, dat.grp i = ℓ ∧ 0 < Zh t i := by
    by_contra hno
    push Not at hno
    have : groupAggregate dat.grp (Zh t) ℓ ≤ 0 := by
      unfold groupAggregate
      exact Finset.sum_nonpos (fun i hi => hno i (Finset.mem_filter.mp hi).2)
    linarith
  obtain ⟨i, hi, hZi⟩ := hex
  have hder := hsol.2.2.2.2.2 t ht i hZi
  have hmono : Monotone (fun u => Th u i) := fun a b hab => hsol.2.2.2.2.1.2.1 hab i
  have hnn := hder.nonneg_of_monotone hmono
  subst hi
  rw [hpx _ hℓ] at hnn
  have hYpos := hℓ
  have : 0 ≤ x (dat.grp i) := by
    by_contra hneg
    push Not at hneg
    have : x (dat.grp i) * Zh t i / groupAggregate dat.grp (Zh t) (dat.grp i) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hZi) hYpos
    linarith
  exact lt_of_le_of_ne this (Ne.symm hxne)

/-! ## Assembly of the positive-rate case from five analytic children -/

noncomputable def phiF {I : ℕ} (alpha : Fin I → ℝ) (Dh Zh : ℝ → Fin I → ℝ) (t : ℝ) : ℝ :=
  ∑ i, Zh t i * Real.log (derivWithin (fun s => Dh s i) (Set.Ici t) t / alpha i)

def PFHyp {I L : ℕ} (dat : PFUnitaryNetworkData I L) (alpha : Fin I → ℝ) : Prop :=
  IsPFDomain dat.TildeAllocSet ∧ (∀ i, 0 ≤ dat.lam i) ∧ (∀ i j, 0 ≤ dat.P i j) ∧
  (∀ i, ∑ j, dat.P i j ≤ 1) ∧
  (∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0)) ∧
  IsTotalArrivalRates dat alpha ∧ (∀ i, 0 < alpha i) ∧
  (∃ a ∈ dat.TildeAllocSet, ∀ ℓ, groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ < a ℓ)

/-! ## K1 algebraic core: the entropy drift as minus a sum of Bregman penalties -/

noncomputable def PFB (v u : ℝ) : ℝ := v * Real.log v - v * Real.log u - v + u

lemma PFB_zero_left (u : ℝ) : PFB 0 u = u := by simp [PFB]

lemma PFB_sqrt (v u : ℝ) (hv : 0 ≤ v) (hu : 0 < u) : (√u - √v) ^ 2 ≤ PFB v u := by
  rcases eq_or_lt_of_le hv with h0 | hvp
  · rw [← h0, PFB_zero_left]; simp [Real.sq_sqrt hu.le]
  · set a := √u with ha
    set b := √v with hb
    have hapos : 0 < a := Real.sqrt_pos.mpr hu
    have hbpos : 0 < b := Real.sqrt_pos.mpr hvp
    have hua : u = a ^ 2 := (Real.sq_sqrt hu.le).symm
    have hvb : v = b ^ 2 := (Real.sq_sqrt hv).symm
    have hlu : Real.log u = 2 * Real.log a := by
      rw [hua, Real.log_pow]; push_cast; ring
    have hlv : Real.log v = 2 * Real.log b := by
      rw [hvb, Real.log_pow]; push_cast; ring
    have hdiv : Real.log a - Real.log b ≤ a / b - 1 := by
      rw [← Real.log_div hapos.ne' hbpos.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hapos hbpos)
    have hmul : b ^ 2 * (Real.log a - Real.log b) ≤ b ^ 2 * (a / b - 1) :=
      mul_le_mul_of_nonneg_left hdiv (by positivity)
    have hbb : b ^ 2 * (a / b - 1) = a * b - b ^ 2 := by field_simp
    unfold PFB
    rw [hlu, hlv, hvb, hua]
    nlinarith

lemma PF_drift_identity {I : ℕ} (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ)
    (α u : Fin I → ℝ) (hα : ∀ i, α i = lam i + ∑ k, P k i * α k) :
    ∑ i, (lam i + ∑ k, P k i * (α k * u k) - α i * u i) * Real.log (u i) =
      -(∑ i, lam i * PFB 1 (u i) +
        ∑ k, α k * (1 - ∑ i, P k i) * (u k * Real.log (u k) - u k + 1) +
        ∑ k, ∑ i, P k i * α k * PFB (u k) (u i)) := by
  set L : Fin I → ℝ := fun i => Real.log (u i) with hL
  set e : Fin I → ℝ := fun k => u k * Real.log (u k) - u k + 1 with he
  have hW : ∀ w : Fin I → ℝ, ∑ i, α i * w i =
      ∑ i, lam i * w i + ∑ k, ∑ i, P k i * α k * w i := by
    intro w
    have h1 : ∑ i, α i * w i = ∑ i, (lam i * w i + ∑ k, P k i * α k * w i) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hα i, add_mul, Finset.sum_mul]
    rw [h1, Finset.sum_add_distrib, Finset.sum_comm]
  set A1 : ℝ := ∑ i, lam i * ((1 - u i) * L i) with hA1
  set A2 : ℝ := ∑ k, ∑ i, P k i * α k * ((u k - u i) * L i) with hA2
  have hLHS : ∑ i, (lam i + ∑ k, P k i * (α k * u k) - α i * u i) * Real.log (u i) = A1 + A2 := by
    have h1 : ∀ i, (lam i + ∑ k, P k i * (α k * u k) - α i * u i) * Real.log (u i) =
        lam i * ((1 - u i) * L i) + ∑ k, P k i * α k * ((u k - u i) * L i) := by
      intro i
      have hs : ∑ k, P k i * α k * ((u k - u i) * L i) =
          (∑ k, P k i * (α k * u k) - (∑ k, P k i * α k) * u i) * L i := by
        rw [sub_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring
      rw [hs, hα i]
      simp only [hL]
      ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_comm
  have hX1 : ∑ i, lam i * PFB 1 (u i) + ∑ i, lam i * e i = -A1 := by
    rw [hA1, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [PFB, he, hL, Real.log_one]
    ring
  have hX2 : ∑ k, α k * (1 - ∑ i, P k i) * e k =
      ∑ k, α k * e k - ∑ k, ∑ i, P k i * α k * e k := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mul_sub, mul_one, sub_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hX3 : ∑ k, ∑ i, P k i * α k * e i - ∑ k, ∑ i, P k i * α k * e k +
      ∑ k, ∑ i, P k i * α k * PFB (u k) (u i) + A2 = 0 := by
    rw [hA2, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    simp only [PFB, he, hL]
    ring
  have hWe := hW e
  rw [hLHS]
  have : ∑ k, α k * (1 - ∑ i, P k i) * (u k * Real.log (u k) - u k + 1) =
      ∑ k, α k * (1 - ∑ i, P k i) * e k := rfl
  rw [this, hX2]
  linarith

lemma PF_e_nonneg (u : ℝ) (hu : 0 ≤ u) : 0 ≤ u * Real.log u - u + 1 := by
  rcases eq_or_lt_of_le hu with h0 | hp
  · rw [← h0]; simp
  · have h := Real.one_sub_inv_le_log_of_pos hp
    have : u * (1 - u⁻¹) ≤ u * Real.log u := mul_le_mul_of_nonneg_left h hp.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ hp.ne'] at this
    linarith

lemma PF_sqrt_lt_of_sq_lt (a b δ : ℝ) (hδ : 0 < δ) (h : (a - b) ^ 2 < δ ^ 2) : a < b + δ := by
  by_contra hc
  push Not at hc
  have h1 : δ ≤ a - b := by linarith
  have : δ ^ 2 ≤ (a - b) ^ 2 := by nlinarith
  linarith

/-- The algebraic heart of Lemma 10.11: if some normalized departure rate `u i0 ≥ 1 + η`, the
entropy drift is at most `-c (η/(3N))²`. -/
lemma PF_drift_core {I : ℕ} (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ) (α : Fin I → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hP : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j ≤ 1)
    (hαpos : ∀ i, 0 < α i) (hα : ∀ i, α i = lam i + ∑ k, P k i * α k)
    (N : ℕ) (hN : ∀ i, ∃ j < N, ∃ k, 0 < lam k ∧ 0 < (P ^ j) k i)
    (c : ℝ) (hc : 0 < c) (hcl : ∀ k, 0 < lam k → c ≤ lam k)
    (hcP : ∀ k i, 0 < P k i → c ≤ P k i * α k)
    (η : ℝ) (hη : 0 < η) (hη3 : η ≤ 3)
    (u : Fin I → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hz : ∀ i, 0 < u i ∨ lam i + ∑ k, P k i * (α k * u k) - α i * u i = 0)
    (i0 : Fin I) (hi0 : 1 + η ≤ u i0) :
    ∑ i, (lam i + ∑ k, P k i * (α k * u k) - α i * u i) * Real.log (u i) ≤
      -(c * (η / (3 * N)) ^ 2) := by
  have hzero : ∀ i, u i = 0 → lam i = 0 ∧ ∀ k, P k i * (α k * u k) = 0 := by
    intro i hi
    rcases hz i with h | h
    · rw [hi] at h; exact absurd h (lt_irrefl 0)
    · rw [hi, mul_zero, sub_zero] at h
      have hs : 0 ≤ ∑ k, P k i * (α k * u k) :=
        Finset.sum_nonneg (fun k _ => mul_nonneg (hP k i) (mul_nonneg (hαpos k).le (hu k)))
      have := (add_eq_zero_iff_of_nonneg (hlam i) hs).mp h
      refine ⟨this.1, fun k => ?_⟩
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
        mul_nonneg (hP k i) (mul_nonneg (hαpos k).le (hu k)))).mp this.2 k (Finset.mem_univ k)
  set tl : Fin I → ℝ := fun i => lam i * PFB 1 (u i) with htl
  set tq : Fin I → ℝ := fun k => α k * (1 - ∑ i, P k i) * (u k * Real.log (u k) - u k + 1) with htq
  set tB : Fin I → Fin I → ℝ := fun k i => P k i * α k * PFB (u k) (u i) with htB
  have htl_lb : ∀ i, 0 < u i → lam i * (√(u i) - 1) ^ 2 ≤ tl i := by
    intro i hi
    have := PFB_sqrt 1 (u i) zero_le_one hi
    rw [Real.sqrt_one] at this
    exact mul_le_mul_of_nonneg_left this (hlam i)
  have htl_nn : ∀ i, 0 ≤ tl i := by
    intro i
    rcases eq_or_lt_of_le (hu i) with h0 | hp
    · simp [htl, (hzero i h0.symm).1]
    · exact le_trans (mul_nonneg (hlam i) (sq_nonneg _)) (htl_lb i hp)
  have htq_nn : ∀ k, 0 ≤ tq k := fun k =>
    mul_nonneg (mul_nonneg (hαpos k).le (by linarith [hrow k])) (PF_e_nonneg _ (hu k))
  have htB_lb : ∀ k i, 0 < u i → P k i * α k * (√(u i) - √(u k)) ^ 2 ≤ tB k i := by
    intro k i hi
    exact mul_le_mul_of_nonneg_left (PFB_sqrt (u k) (u i) (hu k) hi)
      (mul_nonneg (hP k i) (hαpos k).le)
  have htB_nn : ∀ k i, 0 ≤ tB k i := by
    intro k i
    rcases eq_or_lt_of_le (hu i) with h0 | hp
    · have h1 := (hzero i h0.symm).2 k
      rcases mul_eq_zero.mp h1 with h2 | h2
      · simp [htB, h2]
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 (hαpos k).ne'
        · simp [htB, h3, ← h0, PFB_zero_left]
    · exact le_trans (mul_nonneg (mul_nonneg (hP k i) (hαpos k).le) (sq_nonneg _)) (htB_lb k i hp)
  set Pen : ℝ := ∑ i, tl i + ∑ k, tq k + ∑ k, ∑ i, tB k i with hPen
  have hid := PF_drift_identity lam P α u hα
  have hdrift : ∑ i, (lam i + ∑ k, P k i * (α k * u k) - α i * u i) * Real.log (u i) = -Pen := hid
  rw [hdrift, neg_le_neg_iff]
  by_contra hlt
  push Not at hlt
  have hN0 : 0 < N := by
    obtain ⟨j, hj, -⟩ := hN i0
    omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  set δ : ℝ := η / (3 * N) with hδ
  have hδpos : 0 < δ := by positivity
  have hS1 : 0 ≤ ∑ i, tl i := Finset.sum_nonneg (fun i _ => htl_nn i)
  have hS2 : 0 ≤ ∑ k, tq k := Finset.sum_nonneg (fun k _ => htq_nn k)
  have hS3 : 0 ≤ ∑ k, ∑ i, tB k i :=
    Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun i _ => htB_nn k i))
  have htl_le : ∀ i, tl i ≤ Pen := by
    intro i
    have := Finset.single_le_sum (f := tl) (fun j _ => htl_nn j) (Finset.mem_univ i)
    linarith
  have htB_le : ∀ k i, tB k i ≤ Pen := by
    intro k i
    have h1 := Finset.single_le_sum (f := fun i => tB k i) (fun j _ => htB_nn k j)
      (Finset.mem_univ i)
    have h2 := Finset.single_le_sum (f := fun k => ∑ i, tB k i)
      (fun j _ => Finset.sum_nonneg (fun i _ => htB_nn j i)) (Finset.mem_univ k)
    linarith
  -- propagation along positive paths
  have hchain : ∀ j : ℕ, ∀ k i, 0 < lam k → 0 < (P ^ j) k i → √(u i) < 1 + (j + 1) * δ := by
    intro j
    induction j with
    | zero =>
      intro k i hk hki
      have hki' : k = i := by
        by_contra hne
        simp [Matrix.one_apply_ne hne] at hki
      subst hki'
      have hupos : 0 < u k := by
        rcases eq_or_lt_of_le (hu k) with h0 | hp
        · exact absurd (hzero k h0.symm).1 hk.ne'
        · exact hp
      have h1 := htl_lb k hupos
      have h2 : c * (√(u k) - 1) ^ 2 ≤ lam k * (√(u k) - 1) ^ 2 :=
        mul_le_mul_of_nonneg_right (hcl k hk) (sq_nonneg _)
      have h3 : c * (√(u k) - 1) ^ 2 < c * δ ^ 2 := by linarith [htl_le k]
      have h4 : (√(u k) - 1) ^ 2 < δ ^ 2 := lt_of_mul_lt_mul_left h3 hc.le
      have := PF_sqrt_lt_of_sq_lt _ _ δ hδpos h4
      push_cast
      linarith
    | succ j ih =>
      intro k i hk hki
      rw [pow_succ, Matrix.mul_apply] at hki
      obtain ⟨m, -, hm⟩ := Finset.exists_lt_of_sum_lt
        (show ∑ m, (0 : ℝ) < ∑ m, (P ^ j) k m * P m i by simpa using hki)
      have hPmi : 0 < P m i := by
        rcases lt_or_eq_of_le (hP m i) with h | h
        · exact h
        · rw [← h, mul_zero] at hm; exact absurd hm (lt_irrefl 0)
      have hPj : 0 < (P ^ j) k m := by
        by_contra hneg
        push Not at hneg
        have : (P ^ j) k m * P m i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hPmi.le
        linarith
      have him := ih k m hk hPj
      rcases eq_or_lt_of_le (hu i) with h0 | hp
      · rw [← h0, Real.sqrt_zero]; push_cast; positivity
      · have h1 := htB_lb m i hp
        have h2 : c * (√(u i) - √(u m)) ^ 2 ≤ P m i * α m * (√(u i) - √(u m)) ^ 2 :=
          mul_le_mul_of_nonneg_right (hcP m i hPmi) (sq_nonneg _)
        have h3 : c * (√(u i) - √(u m)) ^ 2 < c * δ ^ 2 := by linarith [htB_le m i]
        have h4 : (√(u i) - √(u m)) ^ 2 < δ ^ 2 := lt_of_mul_lt_mul_left h3 hc.le
        have := PF_sqrt_lt_of_sq_lt _ _ δ hδpos h4
        push_cast
        linarith
  obtain ⟨j, hjN, k, hk, hki⟩ := hN i0
  have hfin := hchain j k i0 hk hki
  have hjN' : ((j : ℝ) + 1) ≤ N := by exact_mod_cast hjN
  have hNδ : ((j : ℝ) + 1) * δ ≤ η / 3 := by
    have : (N : ℝ) * δ = η / 3 := by rw [hδ]; field_simp
    nlinarith
  have hsq : 1 + η / 3 ≤ √(u i0) := by
    rw [Real.le_sqrt (by positivity) (by linarith)]
    nlinarith
  linarith

lemma PF_pow_nonneg {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) (hP : ∀ i j, 0 ≤ P i j) :
    ∀ j : ℕ, ∀ k i, 0 ≤ (P ^ j) k i := by
  intro j
  induction j with
  | zero =>
    intro k i
    by_cases h : k = i
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  | succ j ih =>
    intro k i
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun m _ => mul_nonneg (ih k m) (hP m i))

lemma PF_path_exists {I : ℕ} (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ) (α : Fin I → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hP : ∀ i j, 0 ≤ P i j)
    (htr : ∀ i j, Tendsto (fun n => (P ^ n) i j) atTop (𝓝 0))
    (hα : ∀ i, α i = lam i + ∑ k, P k i * α k) (i : Fin I) (hi : 0 < α i) :
    ∃ j : ℕ, ∃ k, 0 < lam k ∧ 0 < (P ^ j) k i := by
  by_contra hno
  push Not at hno
  have hpn := PF_pow_nonneg P hP
  have hzero : ∀ j k, (P ^ j) k i * lam k = 0 := by
    intro j k
    rcases eq_or_lt_of_le (hlam k) with h | h
    · rw [← h, mul_zero]
    · rw [le_antisymm (hno j k h) (hpn j k i), zero_mul]
  have hstep : ∀ n : ℕ, α i = ∑ k, (P ^ n) k i * α k := by
    intro n
    induction n with
    | zero =>
      simp [Matrix.one_apply]
    | succ n ih =>
      rw [ih]
      have h1 : ∑ k, (P ^ n) k i * α k =
          ∑ k, (P ^ n) k i * lam k + ∑ k, (P ^ n) k i * ∑ m, P m k * α m := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hα k, mul_add]
      rw [h1, Finset.sum_eq_zero (fun k _ => hzero n k), zero_add]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [pow_succ', Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
  have hlim : Tendsto (fun n => ∑ k, (P ^ n) k i * α k) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin I))
      (fun k _ => (htr k i).mul_const (α k))
    simpa using this
  have hconst : Tendsto (fun n => ∑ k, (P ^ n) k i * α k) atTop (𝓝 (α i)) := by
    have : (fun n => ∑ k, (P ^ n) k i * α k) = fun _ => α i := by
      funext n; exact (hstep n).symm
    rw [this]; exact tendsto_const_nhds
  have := tendsto_nhds_unique hconst hlim
  linarith

lemma PF_exists_pos_lb {ι : Type*} [Fintype ι] (g : ι → ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, 0 < g x → c ≤ g x := by
  classical
  set S := Finset.univ.filter (fun x => 0 < g x) with hS
  by_cases hne : S.Nonempty
  · refine ⟨S.inf' hne g, ?_, fun x hx => Finset.inf'_le g (by simp [hS, hx])⟩
    obtain ⟨y, hy, hyeq⟩ := Finset.exists_mem_eq_inf' hne g
    rw [hyeq]
    exact (Finset.mem_filter.mp hy).2
  · refine ⟨1, one_pos, fun x hx => absurd ⟨x, by simp [hS, hx]⟩ hne⟩

open ProcessingNetworks.ProportionalFairness

/-- Calculus facts at a regular point of a PF fluid model solution. -/
lemma PF_regular_facts {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t) (hreg : RegularPoint Ah Dh Th Zh t) (i : Fin I) :
    deriv (fun s => Zh s i) t =
        dat.lam i + ∑ k, dat.P k i * deriv (fun s => Dh s k) t - deriv (fun s => Dh s i) t ∧
      0 ≤ deriv (fun s => Dh s i) t ∧
      (Zh t i = 0 → deriv (fun s => Zh s i) t = 0) := by
  obtain ⟨hZ, hZnn, hA, hD, ⟨hT0, hmono, -⟩, -⟩ := hsol
  have hDd : ∀ k, HasDerivAt (fun s => Dh s k) (deriv (fun s => Dh s k) t) t :=
    fun k => ((differentiableAt_pi.mp hreg.2.1) k).hasDerivAt
  refine ⟨?_, ?_, ?_⟩
  · have hev : (fun s => Zh s i) =ᶠ[𝓝 t]
        fun s => Zh 0 i + (dat.lam i * s + ∑ k, dat.P k i * Dh s k) - Dh s i := by
      filter_upwards [Ici_mem_nhds ht] with s hs
      have h1 : Zh s i = Zh 0 i + Ah s i - Dh s i := congrFun (hZ s hs) i
      rw [h1, hA s hs i]
    have hder : HasDerivAt
        (fun s => Zh 0 i + (dat.lam i * s + ∑ k, dat.P k i * Dh s k) - Dh s i)
        (dat.lam i + ∑ k, dat.P k i * deriv (fun s => Dh s k) t - deriv (fun s => Dh s i) t) t := by
      have h1 : HasDerivAt (fun s => dat.lam i * s) (dat.lam i) t := by
        simpa using (hasDerivAt_id t).const_mul (dat.lam i)
      have h2 : HasDerivAt (fun s => ∑ k, dat.P k i * Dh s k)
          (∑ k, dat.P k i * deriv (fun s => Dh s k) t) t :=
        HasDerivAt.fun_sum (fun k _ => (hDd k).const_mul (dat.P k i))
      exact ((h1.add h2).const_add (Zh 0 i)).sub (hDd i)
    rw [hev.deriv_eq, hder.deriv]
  · have hTd : HasDerivAt (fun s => Th s i) (deriv (fun s => Th s i) t) t :=
      ((differentiableAt_pi.mp hreg.2.2.1) i).hasDerivAt
    have hTnn : 0 ≤ deriv (fun s => Th s i) t :=
      hTd.nonneg_of_monotone (fun a b hab => hmono hab i)
    have hev : (fun s => Dh s i) =ᶠ[𝓝 t] fun s => Th s i / dat.m i := by
      filter_upwards [Ici_mem_nhds ht] with s hs
      exact hD s hs i
    rw [hev.deriv_eq, (hTd.div_const (dat.m i)).deriv]
    exact div_nonneg hTnn (dat.hm i).le
  · intro h0
    have hmin : IsLocalMin (fun s => Zh s i) t := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      rw [h0]
      exact hZnn s (le_of_lt hs) i
    exact hmin.deriv_eq_zero

/-- The load condition forces some busy class to depart at rate `≥ (1+η) α_i`. -/
lemma PF_load_witness {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (alpha : Fin I → ℝ) (hα : ∀ i, 0 < alpha i)
    (a : Fin L → ℝ) (haA : a ∈ dat.TildeAllocSet)
    (η : ℝ) (hη : 0 < η)
    (hηl : ∀ ℓ, η * (groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ + 1) ≤
      a ℓ - groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t) (hZ : Zh t ≠ 0) :
    ∃ i, 0 < Zh t i ∧ 1 + η ≤ deriv (fun s => Dh s i) t / alpha i := by
  set Y := groupAggregate dat.grp (Zh t) with hYdef
  have hZnn : ∀ i, 0 ≤ Zh t i := fun i => hsol.2.1 t ht.le i
  have hYnn : ∀ ℓ, 0 ≤ Y ℓ := fun ℓ => Finset.sum_nonneg (fun i _ => hZnn i)
  have hYge : ∀ i, Zh t i ≤ Y (dat.grp i) := fun i => by
    rw [hYdef]; unfold groupAggregate
    exact Finset.single_le_sum (f := fun j => Zh t j) (fun j _ => hZnn j)
      (by simp : i ∈ Finset.univ.filter (fun j => dat.grp j = dat.grp i))
  obtain ⟨x, hxm, hpx⟩ := PF_psi_eq dat.TildeAllocSet hdom Y hYnn
  have hxpos : ∀ ℓ, 0 < Y ℓ → 0 < x ℓ := fun ℓ hℓ => by
    rw [← hpx ℓ hℓ]; exact PF_psi_pos dat hdom Ah Dh Th Zh hsol t ht ℓ hℓ
  have hvi := PF_vi dat.TildeAllocSet hdom Y x hYnn hxm a haA
  obtain ⟨i1, hi1⟩ : ∃ i, Zh t i ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hZ (funext hno)
  have hZi1 : 0 < Zh t i1 := lt_of_le_of_ne (hZnn i1) (Ne.symm hi1)
  obtain ⟨ℓ, hYℓ, haℓ⟩ : ∃ ℓ, 0 < Y ℓ ∧ a ℓ ≤ x ℓ := by
    by_contra hno
    push Not at hno
    have hpos : 0 < ∑ ℓ, Y ℓ * ((a ℓ - x ℓ) / x ℓ) := by
      refine Finset.sum_pos' (fun ℓ _ => ?_) ⟨dat.grp i1, Finset.mem_univ _, ?_⟩
      · rcases eq_or_lt_of_le (hYnn ℓ) with h0 | hp
        · rw [← h0, zero_mul]
        · exact (mul_pos hp (div_pos (by linarith [hno ℓ hp]) (hxpos ℓ hp))).le
      · have hp := lt_of_lt_of_le hZi1 (hYge i1)
        exact mul_pos hp (div_pos (by linarith [hno _ hp]) (hxpos _ hp))
    linarith
  by_contra hno
  push Not at hno
  set ρ := groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ with hρ
  set G := Finset.univ.filter (fun i => dat.grp i = ℓ) with hG
  have hxℓ := hxpos ℓ hYℓ
  -- each class of group ℓ: x Z / Y < (1+η) α m
  have hterm : ∀ i ∈ G, x ℓ * Zh t i / Y ℓ < (1 + η) * (alpha i * dat.m i) := by
    intro i hi
    have hgi : dat.grp i = ℓ := (Finset.mem_filter.mp hi).2
    have hpos : 0 < (1 + η) * (alpha i * dat.m i) := by
      have := hα i; have := dat.hm i; positivity
    rcases eq_or_lt_of_le (hZnn i) with h0 | hZp
    · rw [← h0, mul_zero, zero_div]; exact hpos
    · have hD := (PF_Ddot_formula dat Ah Dh Th Zh hsol t ht i hZp).deriv
      have hu := hno i hZp
      rw [hD, hgi, hpx ℓ hYℓ] at hu
      have hmi := dat.hm i
      have hai := hα i
      rw [div_lt_iff₀ hai] at hu
      have : x ℓ * Zh t i / Y ℓ = x ℓ * Zh t i / Y ℓ / dat.m i * dat.m i := by
        field_simp
      rw [this]
      calc x ℓ * Zh t i / Y ℓ / dat.m i * dat.m i < (1 + η) * alpha i * dat.m i :=
            mul_lt_mul_of_pos_right hu hmi
        _ = (1 + η) * (alpha i * dat.m i) := by ring
  have hGne : G.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : Y ℓ = 0 := by rw [hYdef]; unfold groupAggregate; rw [← hG, hne, Finset.sum_empty]
    linarith
  have hlt := Finset.sum_lt_sum_of_nonempty hGne hterm
  have hsumx : ∑ i ∈ G, x ℓ * Zh t i / Y ℓ = x ℓ := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
    have : ∑ i ∈ G, Zh t i = Y ℓ := by rw [hYdef]; rfl
    rw [this]; field_simp
  have hsumρ : ∑ i ∈ G, (1 + η) * (alpha i * dat.m i) = (1 + η) * ρ := by
    rw [← Finset.mul_sum]; rfl
  have hρnn : 0 ≤ ρ := Finset.sum_nonneg (fun i _ => (mul_pos (hα i) (dat.hm i)).le)
  have hb := hηl ℓ
  rw [hsumx, hsumρ] at hlt
  nlinarith

/-- K1 (= Open leaf a998de6a, Lemma 10.11): uniform drift bound at regular points. -/
theorem pf_K1_drift {I L : ℕ} (dat : PFUnitaryNetworkData I L) (alpha : Fin I → ℝ)
    (h : PFHyp dat alpha) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (Ah Dh Th Zh : ℝ → Fin I → ℝ), IsPFFluidModelSolution dat Ah Dh Th Zh →
        ∀ t : ℝ, 0 < t → RegularPoint Ah Dh Th Zh t → Zh t ≠ 0 →
          ∑ i, deriv (fun s => Zh s i) t * Real.log (deriv (fun s => Dh s i) t / alpha i) ≤ -ε := by
  obtain ⟨hdom, hlam, hP, hrow, htr, halpha, hα, a, haA, hlt⟩ := h
  have hαfix : ∀ i, alpha i = dat.lam i + ∑ k, dat.P k i * alpha k := fun i => congrFun halpha i
  have hpath : ∀ i, ∃ j : ℕ, ∃ k, 0 < dat.lam k ∧ 0 < (dat.P ^ j) k i :=
    fun i => PF_path_exists dat.lam dat.P alpha hlam hP htr hαfix i (hα i)
  choose jf kf hkf using hpath
  set N : ℕ := Finset.univ.sup jf + 1 with hNdef
  have hN : ∀ i, ∃ j < N, ∃ k, 0 < dat.lam k ∧ 0 < (dat.P ^ j) k i := fun i =>
    ⟨jf i, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i)), kf i, hkf i⟩
  obtain ⟨c1, hc1, hc1l⟩ := PF_exists_pos_lb dat.lam
  obtain ⟨c2, hc2, hc2l⟩ := PF_exists_pos_lb (fun p : Fin I × Fin I => dat.P p.1 p.2 * alpha p.1)
  set c : ℝ := min c1 c2 with hcdef
  have hc : 0 < c := lt_min hc1 hc2
  have hcl : ∀ k, 0 < dat.lam k → c ≤ dat.lam k := fun k hk => (min_le_left _ _).trans (hc1l k hk)
  have hcP : ∀ k i, 0 < dat.P k i → c ≤ dat.P k i * alpha k := fun k i hk =>
    (min_le_right _ _).trans (hc2l (k, i) (mul_pos hk (hα k)))
  set ρ : Fin L → ℝ := fun ℓ => groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ with hρ
  have hρnn : ∀ ℓ, 0 ≤ ρ ℓ := fun ℓ =>
    Finset.sum_nonneg (fun i _ => (mul_pos (hα i) (dat.hm i)).le)
  obtain ⟨η0, hη0, hη0l⟩ := PF_exists_pos_lb (fun ℓ => (a ℓ - ρ ℓ) / (ρ ℓ + 1))
  set η : ℝ := min η0 3 with hηdef
  have hη : 0 < η := lt_min hη0 (by norm_num)
  have hη3 : η ≤ 3 := min_le_right _ _
  have hηl : ∀ ℓ, η * (ρ ℓ + 1) ≤ a ℓ - ρ ℓ := by
    intro ℓ
    have hpos : 0 < (a ℓ - ρ ℓ) / (ρ ℓ + 1) :=
      div_pos (by linarith [hlt ℓ]) (by linarith [hρnn ℓ])
    have h1 := (min_le_left η0 3).trans (hη0l ℓ hpos)
    rw [le_div_iff₀ (by linarith [hρnn ℓ])] at h1
    exact h1
  refine ⟨c * (η / (3 * N)) ^ 2, by positivity, ?_⟩
  intro Ah Dh Th Zh hsol t ht hreg hZ
  obtain ⟨i0, -, hi0⟩ := PF_load_witness dat hdom alpha hα a haA η hη hηl Ah Dh Th Zh hsol t ht hZ
  set u : Fin I → ℝ := fun i => deriv (fun s => Dh s i) t / alpha i with hudef
  have hfacts := PF_regular_facts dat Ah Dh Th Zh hsol t ht hreg
  have hαu : ∀ k, alpha k * u k = deriv (fun s => Dh s k) t := fun k => by
    simp only [hudef]; field_simp [(hα k).ne']
  have hzdot : ∀ i, dat.lam i + ∑ k, dat.P k i * (alpha k * u k) - alpha i * u i =
      deriv (fun s => Zh s i) t := by
    intro i
    simp only [hαu]
    rw [(hfacts i).1]
  have hu : ∀ i, 0 ≤ u i := fun i => div_nonneg (hfacts i).2.1 (hα i).le
  have hz : ∀ i, 0 < u i ∨ dat.lam i + ∑ k, dat.P k i * (alpha k * u k) - alpha i * u i = 0 := by
    intro i
    have hZnn : 0 ≤ Zh t i := hsol.2.1 t ht.le i
    rcases eq_or_lt_of_le hZnn with h0 | hZp
    · right; rw [hzdot i]; exact (hfacts i).2.2 h0.symm
    · left
      have hD := (PF_Ddot_formula dat Ah Dh Th Zh hsol t ht i hZp).deriv
      have hYge : Zh t i ≤ groupAggregate dat.grp (Zh t) (dat.grp i) := by
        unfold groupAggregate
        exact Finset.single_le_sum (f := fun j => Zh t j) (fun j _ => hsol.2.1 t ht.le j)
          (by simp : i ∈ Finset.univ.filter (fun j => dat.grp j = dat.grp i))
      have hYp := lt_of_lt_of_le hZp hYge
      have hps := PF_psi_pos dat hdom Ah Dh Th Zh hsol t ht (dat.grp i) hYp
      simp only [hudef]
      rw [hD]
      have := dat.hm i; have := hα i
      positivity
  have hcore := PF_drift_core dat.lam dat.P alpha hlam hP hrow hα hαfix N hN c hc hcl hcP
    η hη hη3 u hu hz i0 hi0
  have heq : ∑ i, deriv (fun s => Zh s i) t * Real.log (deriv (fun s => Dh s i) t / alpha i) =
      ∑ i, (dat.lam i + ∑ k, dat.P k i * (alpha k * u k) - alpha i * u i) * Real.log (u i) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hzdot i]
  rw [heq]
  exact hcore


/-! ## P2: the one-sided "subgradient at the later time" inequality for the entropy -/

lemma PF_maxpos {I L : ℕ} (dat : PFUnitaryNetworkData I L) (hdom : IsPFDomain dat.TildeAllocSet)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (s : ℝ) (hs : 0 < s) :
    ∃ x, IsPFMaximizer dat.TildeAllocSet (groupAggregate dat.grp (Zh s)) x ∧
      (∀ ℓ, 0 < groupAggregate dat.grp (Zh s) ℓ →
        psi dat.TildeAllocSet (groupAggregate dat.grp (Zh s)) ℓ = x ℓ ∧ 0 < x ℓ) := by
  have hZnn : ∀ i, 0 ≤ Zh s i := fun i => hsol.2.1 s hs.le i
  have hYnn : ∀ ℓ, 0 ≤ groupAggregate dat.grp (Zh s) ℓ :=
    fun ℓ => Finset.sum_nonneg (fun i _ => hZnn i)
  obtain ⟨x, hxm, hpx⟩ := PF_psi_eq dat.TildeAllocSet hdom _ hYnn
  refine ⟨x, hxm, fun ℓ hℓ => ⟨hpx ℓ hℓ, ?_⟩⟩
  rw [← hpx ℓ hℓ]
  exact PF_psi_pos dat hdom Ah Dh Th Zh hsol s hs ℓ hℓ

lemma PF_Z_le_Y {I L : ℕ} (grp : Fin I → Fin L) (Z : Fin I → ℝ) (hZ : ∀ i, 0 ≤ Z i) (i : Fin I) :
    Z i ≤ groupAggregate grp Z (grp i) := by
  unfold groupAggregate
  exact Finset.single_le_sum (f := fun j => Z j) (fun j _ => hZ j)
    (by simp : i ∈ Finset.univ.filter (fun j => grp j = grp i))

lemma PF_fiber_mul {I L : ℕ} (grp : Fin I → Fin L) (Z : Fin I → ℝ) (w : Fin L → ℝ) :
    ∑ i, Z i * w (grp i) = ∑ ℓ, groupAggregate grp Z ℓ * w ℓ := by
  rw [PF_sum_fiber grp (fun i => Z i * w (grp i))]
  refine Finset.sum_congr rfl (fun ℓ _ => ?_)
  unfold groupAggregate
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [(Finset.mem_filter.mp hi).2]

/-- For `0 < u, z` with `supp Z(u) ⊆ supp Z(z)`:
`φ(z) - φ(u) ≤ Σ_i (Z_i(z) - Z_i(u)) log(Ḋ_i(z)/α_i)`. -/
lemma PF_phi_sub_le {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (alpha : Fin I → ℝ) (hα : ∀ i, 0 < alpha i)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (u z : ℝ) (hu : 0 < u) (hz : 0 < z) (hsupp : ∀ i, 0 < Zh u i → 0 < Zh z i) :
    phiF alpha Dh Zh z - phiF alpha Dh Zh u ≤
      ∑ i, (Zh z i - Zh u i) *
        Real.log (derivWithin (fun s => Dh s i) (Set.Ici z) z / alpha i) := by
  set Yu := groupAggregate dat.grp (Zh u) with hYu
  set Yz := groupAggregate dat.grp (Zh z) with hYz
  have hZu : ∀ i, 0 ≤ Zh u i := fun i => hsol.2.1 u hu.le i
  have hZz : ∀ i, 0 ≤ Zh z i := fun i => hsol.2.1 z hz.le i
  have hYunn : ∀ ℓ, 0 ≤ Yu ℓ := fun ℓ => Finset.sum_nonneg (fun i _ => hZu i)
  have hYznn : ∀ ℓ, 0 ≤ Yz ℓ := fun ℓ => Finset.sum_nonneg (fun i _ => hZz i)
  obtain ⟨xu, hxum, hxu⟩ := PF_maxpos dat hdom Ah Dh Th Zh hsol u hu
  obtain ⟨xz, hxzm, hxz⟩ := PF_maxpos dat hdom Ah Dh Th Zh hsol z hz
  have hYsupp : ∀ ℓ, 0 < Yu ℓ → 0 < Yz ℓ := by
    intro ℓ hℓ
    obtain ⟨i, hi, hZi⟩ : ∃ i, dat.grp i = ℓ ∧ 0 < Zh u i := by
      by_contra hno
      push Not at hno
      have : Yu ℓ ≤ 0 := by
        rw [hYu]; unfold groupAggregate
        exact Finset.sum_nonpos (fun i hi => hno i (Finset.mem_filter.mp hi).2)
      linarith
    have := PF_Z_le_Y dat.grp (Zh z) hZz i
    rw [hi] at this
    exact lt_of_lt_of_le (hsupp i hZi) this
  -- (a) optimality of xu tested at xz
  obtain ⟨-, -, hmax⟩ := PF_max_fwd dat.TildeAllocSet hdom Yu xu hYunn hxum
  have hopt : PFG Yu xz ≤ PFG Yu xu :=
    hmax xz hxzm.1 (fun ℓ hℓ => (hxz ℓ (hYsupp ℓ hℓ)).2.ne')
  -- per-class bound
  set G : ℝ → Fin I → ℝ := fun s i =>
    Real.log (derivWithin (fun r => Dh r i) (Set.Ici s) s / alpha i) with hG
  have hper : ∀ i, Zh u i * G z i ≤ Zh u i * G u i +
      Zh u i * (Real.log (xz (dat.grp i)) - Real.log (xu (dat.grp i))) +
      (Zh z i * Yu (dat.grp i) / Yz (dat.grp i) - Zh u i) := by
    intro i
    rcases eq_or_lt_of_le (hZu i) with h0 | hp
    · rw [← h0]; simp only [zero_mul, zero_add, sub_zero]
      exact div_nonneg (mul_nonneg (hZz i) (hYunn _)) (hYznn _)
    · have hpz := hsupp i hp
      have hYup : 0 < Yu (dat.grp i) := lt_of_lt_of_le hp (PF_Z_le_Y dat.grp (Zh u) hZu i)
      have hYzp : 0 < Yz (dat.grp i) := lt_of_lt_of_le hpz (PF_Z_le_Y dat.grp (Zh z) hZz i)
      obtain ⟨hpsu, hxup⟩ := hxu _ hYup
      obtain ⟨hpsz, hxzp⟩ := hxz _ hYzp
      have hmi := dat.hm i
      have hai := hα i
      have hDu := (PF_Ddot_formula dat Ah Dh Th Zh hsol u hu i hp).hasDerivWithinAt.derivWithin
        (uniqueDiffWithinAt_Ici u)
      have hDz := (PF_Ddot_formula dat Ah Dh Th Zh hsol z hz i hpz).hasDerivWithinAt.derivWithin
        (uniqueDiffWithinAt_Ici z)
      rw [← hYu] at hDu hpsu
      rw [← hYz] at hDz hpsz
      have eGu : G u i = Real.log (xu (dat.grp i)) + Real.log (Zh u i / Yu (dat.grp i)) -
          Real.log (dat.m i * alpha i) := by
        simp only [hG]
        rw [hDu, hpsu, ← Real.log_mul hxup.ne' (div_pos hp hYup).ne',
          ← Real.log_div (mul_pos hxup (div_pos hp hYup)).ne' (mul_pos hmi hai).ne']
        congr 1
        field_simp
      have eGz : G z i = Real.log (xz (dat.grp i)) + Real.log (Zh z i / Yz (dat.grp i)) -
          Real.log (dat.m i * alpha i) := by
        simp only [hG]
        rw [hDz, hpsz, ← Real.log_mul hxzp.ne' (div_pos hpz hYzp).ne',
          ← Real.log_div (mul_pos hxzp (div_pos hpz hYzp)).ne' (mul_pos hmi hai).ne']
        congr 1
        field_simp
      have hgibbs : Zh u i * (Real.log (Zh z i / Yz (dat.grp i)) -
          Real.log (Zh u i / Yu (dat.grp i))) ≤
          Zh z i * Yu (dat.grp i) / Yz (dat.grp i) - Zh u i := by
        rw [← Real.log_div (div_pos hpz hYzp).ne' (div_pos hp hYup).ne']
        have hr : 0 < Zh z i / Yz (dat.grp i) / (Zh u i / Yu (dat.grp i)) := by positivity
        have h1 := Real.log_le_sub_one_of_pos hr
        have h2 := mul_le_mul_of_nonneg_left h1 hp.le
        have h3 : Zh u i * (Zh z i / Yz (dat.grp i) / (Zh u i / Yu (dat.grp i)) - 1) =
            Zh z i * Yu (dat.grp i) / Yz (dat.grp i) - Zh u i := by
          field_simp
        linarith
      rw [eGu, eGz]
      nlinarith [hgibbs]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hper i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hA : ∑ i, Zh u i * (Real.log (xz (dat.grp i)) - Real.log (xu (dat.grp i))) =
      PFG Yu xz - PFG Yu xu := by
    rw [PF_fiber_mul dat.grp (Zh u) (fun ℓ => Real.log (xz ℓ) - Real.log (xu ℓ))]
    unfold PFG
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    ring
  have hB : ∑ i, (Zh z i * Yu (dat.grp i) / Yz (dat.grp i) - Zh u i) ≤ 0 := by
    have e1 : ∑ i, Zh z i * Yu (dat.grp i) / Yz (dat.grp i) =
        ∑ ℓ, Yz ℓ * (Yu ℓ / Yz ℓ) := by
      rw [← PF_fiber_mul dat.grp (Zh z) (fun ℓ => Yu ℓ / Yz ℓ)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    have e2 : ∑ i, Zh u i = ∑ ℓ, Yu ℓ := PF_sum_fiber dat.grp (Zh u)
    rw [Finset.sum_sub_distrib, e1, e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_nonpos (fun ℓ _ => ?_)
    rcases eq_or_lt_of_le (hYznn ℓ) with h0 | hp
    · rw [← h0]; simp [hYunn ℓ]
    · rw [mul_div_cancel₀ _ hp.ne']; simp
  have hphi : ∀ s, phiF alpha Dh Zh s = ∑ i, Zh s i * G s i := fun s => rfl
  rw [hphi z, hphi u, ← Finset.sum_sub_distrib]
  have hfin : ∑ i, Zh u i * G z i ≤ ∑ i, Zh u i * G u i := by linarith
  have : ∑ i, (Zh z i * G z i - Zh u i * G u i) =
      ∑ i, (Zh z i - Zh u i) * G z i + (∑ i, Zh u i * G z i - ∑ i, Zh u i * G u i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [this]
  linarith


/-- K5 (corrects the disproved ad9fc3b6: needs the load condition). -/
theorem pf_K5_nonneg {I L : ℕ} (dat : PFUnitaryNetworkData I L) (alpha : Fin I → ℝ)
    (h : PFHyp dat alpha) (Ah Dh Th Zh : ℝ → Fin I → ℝ)
    (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) (t : ℝ) (ht : 0 < t) :
    0 ≤ phiF alpha Dh Zh t ∧ (Zh t ≠ 0 → 0 < phiF alpha Dh Zh t) := by
  obtain ⟨hdom, -, -, -, -, -, hα, a, haA, hlt⟩ := h
  set Y := groupAggregate dat.grp (Zh t) with hYdef
  have hZnn : ∀ i, 0 ≤ Zh t i := fun i => hsol.2.1 t ht.le i
  have hYnn : ∀ ℓ, 0 ≤ Y ℓ := fun ℓ => Finset.sum_nonneg (fun i _ => hZnn i)
  obtain ⟨x, hxm, hpx⟩ := PF_psi_eq dat.TildeAllocSet hdom Y hYnn
  have hxpos : ∀ ℓ, 0 < Y ℓ → 0 < x ℓ := fun ℓ hℓ => by
    rw [← hpx ℓ hℓ]; exact PF_psi_pos dat hdom Ah Dh Th Zh hsol t ht ℓ hℓ
  set c : Fin L → ℝ := fun ℓ => Y ℓ / x ℓ with hc
  have hc_nn : ∀ ℓ, 0 ≤ c ℓ := fun ℓ => by
    rcases eq_or_lt_of_le (hYnn ℓ) with h0 | hpos
    · simp [hc, ← h0]
    · exact div_nonneg hpos.le (hxpos ℓ hpos).le
  have hYge : ∀ i, Zh t i ≤ Y (dat.grp i) := fun i => by
    rw [hYdef]; unfold groupAggregate
    exact Finset.single_le_sum (f := fun j => Zh t j) (fun j _ => hZnn j)
      (by simp : i ∈ Finset.univ.filter (fun j => dat.grp j = dat.grp i))
  -- termwise lower bound
  have hA : ∀ i, Zh t i - dat.m i * alpha i * c (dat.grp i) ≤
      Zh t i * Real.log (derivWithin (fun s => Dh s i) (Set.Ici t) t / alpha i) := by
    intro i
    have hmi := dat.hm i
    have hai := hα i
    by_cases hZ : Zh t i = 0
    · rw [hZ]; simp only [zero_mul, zero_sub]
      have := mul_nonneg (mul_pos hmi hai).le (hc_nn (dat.grp i))
      linarith
    · have hZpos : 0 < Zh t i := lt_of_le_of_ne (hZnn i) (Ne.symm hZ)
      have hYpos : 0 < Y (dat.grp i) := lt_of_lt_of_le hZpos (hYge i)
      have hxp := hxpos _ hYpos
      have hD := PF_Ddot_formula dat Ah Dh Th Zh hsol t ht i hZpos
      rw [hD.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici t)]
      rw [hpx _ hYpos]
      set u : ℝ := x (dat.grp i) * Zh t i / Y (dat.grp i) / dat.m i / alpha i with hu
      have hupos : 0 < u := by positivity
      have hlog := Real.one_sub_inv_le_log_of_pos hupos
      have hkey : Zh t i * u⁻¹ = dat.m i * alpha i * c (dat.grp i) := by
        simp only [hu, hc]
        field_simp
      calc Zh t i - dat.m i * alpha i * c (dat.grp i) = Zh t i * (1 - u⁻¹) := by
            rw [mul_sub, mul_one, hkey]
        _ ≤ Zh t i * Real.log u := mul_le_mul_of_nonneg_left hlog hZpos.le
  have hphi : ∑ i, Zh t i - ∑ i, dat.m i * alpha i * c (dat.grp i) ≤ phiF alpha Dh Zh t := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun i _ => hA i)
  -- group sums
  have hsumY : ∑ ℓ, Y ℓ = ∑ i, Zh t i := (PF_sum_fiber dat.grp (Zh t)).symm
  have hsumc : ∑ i, dat.m i * alpha i * c (dat.grp i) =
      ∑ ℓ, c ℓ * groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ := by
    rw [PF_sum_fiber dat.grp (fun i => dat.m i * alpha i * c (dat.grp i))]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    unfold groupAggregate
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [(Finset.mem_filter.mp hi).2]; ring
  have hvi := PF_vi dat.TildeAllocSet hdom Y x hYnn hxm a haA
  have hvi' : ∑ ℓ, c ℓ * a ℓ ≤ ∑ ℓ, Y ℓ := by
    have : ∀ ℓ, Y ℓ * ((a ℓ - x ℓ) / x ℓ) = c ℓ * a ℓ - Y ℓ := by
      intro ℓ
      rcases eq_or_lt_of_le (hYnn ℓ) with h0 | hpos
      · simp [hc, ← h0]
      · have := (hxpos ℓ hpos).ne'
        simp only [hc]
        field_simp
    simp only [this] at hvi
    rw [Finset.sum_sub_distrib] at hvi
    linarith
  have hcr : ∑ ℓ, c ℓ * groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ ≤ ∑ ℓ, c ℓ * a ℓ :=
    Finset.sum_le_sum (fun ℓ _ => mul_le_mul_of_nonneg_left (hlt ℓ).le (hc_nn ℓ))
  refine ⟨by linarith, fun hne => ?_⟩
  -- strictness
  obtain ⟨i, hi⟩ : ∃ i, Zh t i ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hne (funext hno)
  have hZpos : 0 < Zh t i := lt_of_le_of_ne (hZnn i) (Ne.symm hi)
  have hYpos : 0 < Y (dat.grp i) := lt_of_lt_of_le hZpos (hYge i)
  have hcpos : 0 < c (dat.grp i) := div_pos hYpos (hxpos _ hYpos)
  have hstrict : ∑ ℓ, c ℓ * groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ <
      ∑ ℓ, c ℓ * a ℓ :=
    Finset.sum_lt_sum (fun ℓ _ => mul_le_mul_of_nonneg_left (hlt ℓ).le (hc_nn ℓ))
      ⟨dat.grp i, Finset.mem_univ _, mul_lt_mul_of_pos_left (hlt _) hcpos⟩
  linarith

/-! ## C2 groundwork: zero-rate classes -/

/-- C2a: total arrival rates are nonnegative (α = Σₙ (P')ⁿ λ). -/
theorem pf_alpha_nonneg {I L : ℕ} (dat : PFUnitaryNetworkData I L) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0))
    (alpha : Fin I → ℝ) (halpha : IsTotalArrivalRates dat alpha) : ∀ i, 0 ≤ alpha i := by
  have hfix : ∀ i, alpha i = dat.lam i + ∑ k, dat.P k i * alpha k := fun i => congrFun halpha i
  have key : ∀ n : ℕ, ∀ i, alpha i = (∑ j ∈ Finset.range n, ∑ k, (dat.P ^ j) k i * dat.lam k) +
      ∑ k, (dat.P ^ n) k i * alpha k := by
    intro n
    induction n with
    | zero => intro i; simp [Matrix.one_apply]
    | succ n ih =>
      intro i
      rw [ih i, Finset.sum_range_succ]
      have h1 : ∑ k, (dat.P ^ n) k i * alpha k = ∑ k, (dat.P ^ n) k i * dat.lam k +
          ∑ k, (dat.P ^ (n + 1)) k i * alpha k := by
        have h2 : ∀ k, (dat.P ^ (n + 1)) k i = ∑ j, dat.P k j * (dat.P ^ n) j i := by
          intro k; rw [pow_succ', Matrix.mul_apply]
        simp_rw [h2]
        conv_lhs => arg 2; ext k; rw [hfix k]
        simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))
      rw [h1]; ring
  intro i
  have hR : Tendsto (fun n => ∑ k, (dat.P ^ n) k i * alpha k) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin I))
      (fun k _ => (hP_transient k i).mul_const (alpha k))
    simpa using this
  have hle : ∀ n, ∑ k, (dat.P ^ n) k i * alpha k ≤ alpha i := by
    intro n
    have hS : 0 ≤ ∑ j ∈ Finset.range n, ∑ k, (dat.P ^ j) k i * dat.lam k :=
      Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ =>
        mul_nonneg (PF_pow_nonneg dat.P hP_nonneg j k i) (hlam k)))
    linarith [key n i]
  exact le_of_tendsto' hR hle

/-- C2b: zero-rate classes are fed only by zero-rate classes. -/
theorem pf_zero_rate_closed {I L : ℕ} (dat : PFUnitaryNetworkData I L) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (alpha : Fin I → ℝ) (halpha : IsTotalArrivalRates dat alpha)
    (hα0 : ∀ i, 0 ≤ alpha i) (k i : Fin I) (hk : 0 < alpha k) (hi : alpha i = 0) :
    dat.P k i = 0 := by
  have hfix : alpha i = dat.lam i + ∑ j, dat.P j i * alpha j := congrFun halpha i
  have hterm : dat.P k i * alpha k ≤ ∑ j, dat.P j i * alpha j :=
    Finset.single_le_sum (f := fun j => dat.P j i * alpha j)
      (fun j _ => mul_nonneg (hP_nonneg j i) (hα0 j)) (Finset.mem_univ k)
  have h0 : dat.P k i * alpha k ≤ 0 := by linarith [hlam i]
  have h1 : dat.P k i ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hc hk
    linarith
  exact le_antisymm h1 (hP_nonneg k i)

/-! ## C2e: the PF value function `V(Y) = max_x Σ Y_ℓ log x_ℓ` is continuous on the orthant -/

noncomputable def PFV {L : ℕ} (A : Set (Fin L → ℝ)) (Y : Fin L → ℝ) : ℝ := PFG Y (psi A Y)

lemma PFV_eq {L : ℕ} (A : Set (Fin L → ℝ)) (hdom : IsPFDomain A) (Y : Fin L → ℝ)
    (hY : ∀ ℓ, 0 ≤ Y ℓ) :
    ∃ x, IsPFMaximizer A Y x ∧ (∀ ℓ, 0 < Y ℓ → psi A Y ℓ = x ℓ) ∧ PFV A Y = PFG Y x := by
  obtain ⟨x, hxm, hpx⟩ := PF_psi_eq A hdom Y hY
  refine ⟨x, hxm, hpx, ?_⟩
  unfold PFV PFG
  refine Finset.sum_congr rfl (fun ℓ _ => ?_)
  rcases eq_or_lt_of_le (hY ℓ) with h0 | hp
  · rw [← h0]; simp
  · rw [hpx ℓ hp]

lemma PFV_ge {L : ℕ} (A : Set (Fin L → ℝ)) (hdom : IsPFDomain A) (Y : Fin L → ℝ)
    (hY : ∀ ℓ, 0 ≤ Y ℓ) (y : Fin L → ℝ) (hy : y ∈ A) (hg : PFGood Y y) :
    PFG Y y ≤ PFV A Y := by
  obtain ⟨x, hxm, -, hV⟩ := PFV_eq A hdom Y hY
  obtain ⟨-, -, hmax⟩ := PF_max_fwd A hdom Y x hY hxm
  rw [hV]; exact hmax y hy hg

lemma PF_log_le_rho {L : ℕ} (A : Set (Fin L → ℝ)) (R : ℝ) (hR : ∀ x ∈ A, ‖x‖ ≤ R)
    (x : Fin L → ℝ) (hx : x ∈ A) (ℓ : Fin L) : Real.log (x ℓ) ≤ Real.log (max R 1) := by
  by_cases h0 : x ℓ = 0
  · simp [h0, Real.log_nonneg (le_max_right R 1)]
  · rw [← Real.log_abs]
    have habs : |x ℓ| ≤ max R 1 := by
      calc |x ℓ| = ‖x ℓ‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖x‖ := norm_le_pi_norm _ _
        _ ≤ R := hR x hx
        _ ≤ max R 1 := le_max_left _ _
    exact Real.log_le_log (abs_pos.mpr h0) habs

/-- Coordinates of a near-optimal point are bounded away from `0` on the support. -/
lemma PF_coord_lb {L : ℕ} (A : Set (Fin L → ℝ)) (R : ℝ) (hR : ∀ x ∈ A, ‖x‖ ≤ R)
    (x0 Y : Fin L → ℝ) (hY : ∀ ℓ, 0 ≤ Y ℓ) (y : Fin L → ℝ) (hy : y ∈ A)
    (hc : PFG Y x0 ≤ PFG Y y) (ℓ : Fin L) (hℓ : 0 < Y ℓ) :
    (PFG Y x0 - (∑ k, Y k) * Real.log (max R 1)) / Y ℓ ≤ Real.log |y ℓ| := by
  set ρ := Real.log (max R 1) with hρ
  have hρ0 : 0 ≤ ρ := Real.log_nonneg (le_max_right R 1)
  have hsplit : PFG Y y = Y ℓ * Real.log (y ℓ) +
      ∑ k ∈ Finset.univ.erase ℓ, Y k * Real.log (y k) := by
    unfold PFG
    exact (Finset.add_sum_erase Finset.univ (fun k => Y k * Real.log (y k))
      (Finset.mem_univ ℓ)).symm
  have hrest : ∑ k ∈ Finset.univ.erase ℓ, Y k * Real.log (y k) ≤ (∑ k, Y k) * ρ := by
    calc ∑ k ∈ Finset.univ.erase ℓ, Y k * Real.log (y k)
        ≤ ∑ k ∈ Finset.univ.erase ℓ, Y k * ρ :=
          Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
            (PF_log_le_rho A R hR y hy k) (hY k))
      _ ≤ ∑ k, Y k * ρ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun k _ _ => mul_nonneg (hY k) hρ0)
      _ = (∑ k, Y k) * ρ := by rw [Finset.sum_mul]
  rw [div_le_iff₀ hℓ, Real.log_abs]
  nlinarith

/-- Lower semicontinuity of `V` on the orthant. -/
lemma PFV_lsc {L : ℕ} (A : Set (Fin L → ℝ)) (hdom : IsPFDomain A) (Y0 : Fin L → ℝ)
    (hY0 : ∀ ℓ, 0 ≤ Y0 ℓ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ Y in 𝓝 Y0, (∀ ℓ, 0 ≤ Y ℓ) → PFV A Y0 - ε < PFV A Y := by
  obtain ⟨x, hxm, -, hV⟩ := PFV_eq A hdom Y0 hY0
  obtain ⟨hxA, hgx, -⟩ := PF_max_fwd A hdom Y0 x hY0 hxm
  obtain ⟨x0, hx0A, hx0pos⟩ := hdom.2.2.2.2
  set yθ : ℝ → Fin L → ℝ := fun θ ℓ => (1 - θ) * x ℓ + θ * x0 ℓ with hyθ
  have hne : ∀ᶠ θ in 𝓝[>] (0:ℝ), ∀ ℓ, yθ θ ℓ ≠ 0 := by
    refine Filter.eventually_all.mpr (fun ℓ => ?_)
    by_cases hxl : x ℓ = 0
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      have hθ' : (0:ℝ) < θ := hθ
      simp only [hyθ, hxl, mul_zero, zero_add]
      exact mul_ne_zero hθ'.ne' (hx0pos ℓ).ne'
    · have hc : Continuous fun θ : ℝ => (1 - θ) * x ℓ + θ * x0 ℓ := by fun_prop
      have h0 : (1 - (0:ℝ)) * x ℓ + 0 * x0 ℓ ≠ 0 := by simpa using hxl
      filter_upwards [nhdsWithin_le_nhds (hc.continuousAt.eventually_ne h0)] with θ hθ
      exact hθ
  have hcontθ : ContinuousAt (fun θ => PFG Y0 (yθ θ)) 0 := by
    unfold PFG
    refine tendsto_finsetSum _ (fun ℓ _ => ?_)
    rcases eq_or_lt_of_le (hY0 ℓ) with h0 | hp
    · simp only [← h0, zero_mul]; exact continuousAt_const
    · have hc : Continuous fun θ : ℝ => (1 - θ) * x ℓ + θ * x0 ℓ := by fun_prop
      have h0 : (1 - (0:ℝ)) * x ℓ + 0 * x0 ℓ ≠ 0 := by simpa using hgx ℓ hp
      exact continuousAt_const.mul (hc.continuousAt.log h0)
  have hy0 : PFG Y0 (yθ 0) = PFV A Y0 := by
    rw [hV]; simp [hyθ]
  have htend : Tendsto (fun θ => PFG Y0 (yθ θ)) (𝓝[>] 0) (𝓝 (PFV A Y0)) := by
    rw [← hy0]; exact tendsto_nhdsWithin_of_tendsto_nhds hcontθ.tendsto
  have hgt := htend.eventually (lt_mem_nhds (show PFV A Y0 - ε / 2 < PFV A Y0 by linarith))
  obtain ⟨θ, ⟨hθ1, hθ2⟩, hθ3⟩ := ((hne.and hgt).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  set y := yθ θ with hy
  have hyA : y ∈ A := by
    have : y = (1 - θ) • x + θ • x0 := by funext ℓ; simp [hy, hyθ]
    rw [this]
    exact hdom.2.2.1 hxA hx0A (by linarith [hθ3.2]) hθ3.1.le (by ring)
  have hcY : Continuous fun Y : Fin L → ℝ => PFG Y y := by
    unfold PFG; fun_prop
  have hev := hcY.continuousAt.eventually (lt_mem_nhds
    (show PFV A Y0 - ε < PFG Y0 y by linarith))
  filter_upwards [hev] with Y hY hYnn
  exact lt_of_lt_of_le hY (PFV_ge A hdom Y hYnn y hyA (fun ℓ _ => hθ1 ℓ))

/-- The local estimate behind upper semicontinuity: near `Y0`, every optimal point `y` for `Y`
has coordinates bounded away from `0` on `supp Y0`, and `PFG Y y - PFG Y0 y ≤ C Σ|Y - Y0|`. -/
lemma PF_near_est {L : ℕ} (A : Set (Fin L → ℝ)) (hdom : IsPFDomain A) (Y0 : Fin L → ℝ)
    (hY0 : ∀ ℓ, 0 ≤ Y0 ℓ) :
    ∃ δ : Fin L → ℝ, (∀ ℓ, 0 < δ ℓ) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Y in 𝓝 Y0, (∀ ℓ, 0 ≤ Y ℓ) →
      ∀ y ∈ A, PFGood Y y → PFV A Y ≤ PFG Y y →
        (∀ ℓ, 0 < Y0 ℓ → δ ℓ ≤ |y ℓ|) ∧
        PFG Y y - PFG Y0 y ≤ C * ∑ ℓ, |Y ℓ - Y0 ℓ| := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hdom.1
  obtain ⟨x0, hx0A, hx0pos⟩ := hdom.2.2.2.2
  set ρ := Real.log (max R 1) with hρ
  have hρ0 : 0 ≤ ρ := Real.log_nonneg (le_max_right R 1)
  set g : Fin L → (Fin L → ℝ) → ℝ := fun ℓ Y => (PFG Y x0 - (∑ k, Y k) * ρ) / Y ℓ with hg
  refine ⟨fun ℓ => Real.exp (g ℓ Y0 - 1), fun ℓ => Real.exp_pos _,
    ∑ ℓ, (ρ + |g ℓ Y0| + 1), Finset.sum_nonneg (fun ℓ _ => by positivity), ?_⟩
  have hev : ∀ᶠ Y in 𝓝 Y0, ∀ ℓ, 0 < Y0 ℓ → 0 < Y ℓ ∧ g ℓ Y0 - 1 < g ℓ Y := by
    refine Filter.eventually_all.mpr (fun ℓ => ?_)
    by_cases hℓ : 0 < Y0 ℓ
    · have hc1 : ContinuousAt (fun Y : Fin L → ℝ => Y ℓ) Y0 := (continuous_apply ℓ).continuousAt
      have hc2 : ContinuousAt (g ℓ) Y0 := by
        simp only [hg]
        refine ContinuousAt.div ?_ hc1 hℓ.ne'
        unfold PFG; fun_prop
      filter_upwards [hc1.eventually (lt_mem_nhds hℓ),
        hc2.eventually (lt_mem_nhds (show g ℓ Y0 - 1 < g ℓ Y0 by linarith))] with Y h1 h2 _
      exact ⟨h1, h2⟩
    · exact Filter.Eventually.of_forall (fun _ h => absurd h hℓ)
  filter_upwards [hev] with Y hY hYnn y hyA hgy hopt
  have hg0 : PFGood Y x0 := fun ℓ _ => (hx0pos ℓ).ne'
  have hc0 : PFG Y x0 ≤ PFG Y y := (PFV_ge A hdom Y hYnn x0 hx0A hg0).trans hopt
  have hlow : ∀ ℓ, 0 < Y0 ℓ → g ℓ Y0 - 1 ≤ Real.log |y ℓ| := by
    intro ℓ hℓ
    obtain ⟨hYp, hgl⟩ := hY ℓ hℓ
    exact hgl.le.trans (PF_coord_lb A R hR x0 Y hYnn y hyA hc0 ℓ hYp)
  refine ⟨fun ℓ hℓ => ?_, ?_⟩
  · have hy0 : y ℓ ≠ 0 := hgy ℓ (hY ℓ hℓ).1
    calc Real.exp (g ℓ Y0 - 1) ≤ Real.exp (Real.log |y ℓ|) := Real.exp_le_exp.mpr (hlow ℓ hℓ)
      _ = |y ℓ| := Real.exp_log (abs_pos.mpr hy0)
  · have hdiff : PFG Y y - PFG Y0 y = ∑ ℓ, (Y ℓ - Y0 ℓ) * Real.log (y ℓ) := by
      unfold PFG; rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun ℓ _ => by ring)
    rw [hdiff, Finset.mul_sum]
    refine Finset.sum_le_sum (fun ℓ _ => ?_)
    have hCl : ρ + |g ℓ Y0| + 1 ≤ ∑ k, (ρ + |g k Y0| + 1) :=
      Finset.single_le_sum (f := fun k => ρ + |g k Y0| + 1) (fun k _ => by positivity)
        (Finset.mem_univ ℓ)
    have hup := PF_log_le_rho A R hR y hyA ℓ
    rcases eq_or_lt_of_le (hY0 ℓ) with h0 | hp
    · rw [← h0, sub_zero, abs_of_nonneg (hYnn ℓ)]
      calc Y ℓ * Real.log (y ℓ) ≤ Y ℓ * ρ := mul_le_mul_of_nonneg_left hup (hYnn ℓ)
        _ ≤ Y ℓ * (∑ k, (ρ + |g k Y0| + 1)) :=
            mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (g ℓ Y0)]) (hYnn ℓ)
        _ = (∑ k, (ρ + |g k Y0| + 1)) * Y ℓ := by ring
    · have hlo := hlow ℓ hp
      rw [Real.log_abs] at hlo
      have habs : |Real.log (y ℓ)| ≤ ρ + |g ℓ Y0| + 1 := by
        rw [abs_le]; constructor
        · linarith [neg_abs_le (g ℓ Y0)]
        · linarith [abs_nonneg (g ℓ Y0)]
      calc (Y ℓ - Y0 ℓ) * Real.log (y ℓ) ≤ |Y ℓ - Y0 ℓ| * |Real.log (y ℓ)| := by
            rw [← abs_mul]; exact le_abs_self _
        _ ≤ |Y ℓ - Y0 ℓ| * (∑ k, (ρ + |g k Y0| + 1)) :=
            mul_le_mul_of_nonneg_left (habs.trans hCl) (abs_nonneg _)
        _ = (∑ k, (ρ + |g k Y0| + 1)) * |Y ℓ - Y0 ℓ| := by ring

lemma PF_sum_abs_tendsto {L : ℕ} (Y0 : Fin L → ℝ) :
    Tendsto (fun Y : Fin L → ℝ => ∑ ℓ, |Y ℓ - Y0 ℓ|) (𝓝 Y0) (𝓝 0) := by
  have hc : Continuous fun Y : Fin L → ℝ => ∑ ℓ, |Y ℓ - Y0 ℓ| := by fun_prop
  have := hc.tendsto Y0
  simpa using this

/-- Upper semicontinuity of `V` on the orthant. -/
lemma PFV_usc {L : ℕ} (A : Set (Fin L → ℝ)) (hdom : IsPFDomain A) (Y0 : Fin L → ℝ)
    (hY0 : ∀ ℓ, 0 ≤ Y0 ℓ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ Y in 𝓝 Y0, (∀ ℓ, 0 ≤ Y ℓ) → PFV A Y < PFV A Y0 + ε := by
  obtain ⟨δ, hδ, C, hC, hest⟩ := PF_near_est A hdom Y0 hY0
  have hsmall : ∀ᶠ Y in 𝓝 Y0, C * ∑ ℓ, |Y ℓ - Y0 ℓ| < ε := by
    have := (PF_sum_abs_tendsto Y0).const_mul C
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds hε)
  filter_upwards [hest, hsmall] with Y hY hYs hYnn
  obtain ⟨x, hxm, -, hV⟩ := PFV_eq A hdom Y hYnn
  obtain ⟨hxA, hgx, -⟩ := PF_max_fwd A hdom Y x hYnn hxm
  obtain ⟨hlb, hdiff⟩ := hY hYnn x hxA hgx hV.le
  have hgood0 : PFGood Y0 x := fun ℓ hℓ h => by
    have := hlb ℓ hℓ; rw [h, abs_zero] at this; linarith [hδ ℓ]
  have h0 := PFV_ge A hdom Y0 hY0 x hxA hgood0
  rw [hV]; linarith

lemma PFV_continuousWithinAt {L : ℕ} (A : Set (Fin L → ℝ)) (hdom : IsPFDomain A)
    (Y0 : Fin L → ℝ) (hY0 : ∀ ℓ, 0 ≤ Y0 ℓ) :
    ContinuousWithinAt (PFV A) {Y | ∀ ℓ, 0 ≤ Y ℓ} Y0 := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have h := PFV_lsc A hdom Y0 hY0 (PFV A Y0 - a) (by linarith)
    filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with Y hY hYm
    have := hY hYm; linarith
  · have h := PFV_usc A hdom Y0 hY0 (b - PFV A Y0) (by linarith)
    filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with Y hY hYm
    have := hY hYm; linarith

/-! ## C2e: the entropy for arbitrary positive weights `β` is continuous on `(0,∞)` -/

/-- The entropy in value-function form (valid for every `t > 0`, any weights `β > 0`). -/
lemma PF_phiF_eq_V {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (β : Fin I → ℝ) (hβ : ∀ i, 0 < β i)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t) :
    phiF β Dh Zh t = PFV dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) +
      (∑ i, Zh t i * Real.log (Zh t i) -
        ∑ ℓ, groupAggregate dat.grp (Zh t) ℓ * Real.log (groupAggregate dat.grp (Zh t) ℓ) -
        ∑ i, Zh t i * Real.log (dat.m i * β i)) := by
  set Y := groupAggregate dat.grp (Zh t) with hY
  have hZnn : ∀ i, 0 ≤ Zh t i := fun i => hsol.2.1 t ht.le i
  have hterm : ∀ i, Zh t i * Real.log (derivWithin (fun s => Dh s i) (Set.Ici t) t / β i) =
      Zh t i * Real.log (psi dat.TildeAllocSet Y (dat.grp i)) + Zh t i * Real.log (Zh t i) -
      Zh t i * Real.log (Y (dat.grp i)) - Zh t i * Real.log (dat.m i * β i) := by
    intro i
    rcases eq_or_lt_of_le (hZnn i) with h0 | hZp
    · rw [← h0]; simp
    · have hD := PF_Ddot_formula dat Ah Dh Th Zh hsol t ht i hZp
      rw [hD.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici t)]
      have hYp : 0 < Y (dat.grp i) := lt_of_lt_of_le hZp (PF_Z_le_Y dat.grp (Zh t) hZnn i)
      have hps := PF_psi_pos dat hdom Ah Dh Th Zh hsol t ht (dat.grp i) hYp
      have hm := dat.hm i
      have hb := hβ i
      rw [show psi dat.TildeAllocSet Y (dat.grp i) * Zh t i / Y (dat.grp i) / dat.m i / β i =
        psi dat.TildeAllocSet Y (dat.grp i) * Zh t i / (Y (dat.grp i) * (dat.m i * β i)) by
          field_simp]
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul hps.ne' hZp.ne',
        Real.log_mul hYp.ne' (by positivity)]
      ring
  unfold phiF
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have h1 : ∑ i, Zh t i * Real.log (psi dat.TildeAllocSet Y (dat.grp i)) =
      PFV dat.TildeAllocSet Y := by
    rw [PF_fiber_mul dat.grp (Zh t) (fun ℓ => Real.log (psi dat.TildeAllocSet Y ℓ))]
    rfl
  have h2 : ∑ i, Zh t i * Real.log (Y (dat.grp i)) = ∑ ℓ, Y ℓ * Real.log (Y ℓ) :=
    PF_fiber_mul dat.grp (Zh t) (fun ℓ => Real.log (Y ℓ))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2]
  ring

lemma PF_T_contAt {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t) (i : Fin I) : ContinuousAt (fun s => Th s i) t := by
  obtain ⟨-, -, -, -, ⟨-, -, Kc, hK⟩, -⟩ := hsol
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun s : ℝ => |Kc| * |s - t|) (𝓝 t) (𝓝 0) := by
    have : Continuous fun s : ℝ => |Kc| * |s - t| := by fun_prop
    simpa using this.tendsto t
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [Ioi_mem_nhds ht] with s hs
  have hs0 : (0:ℝ) ≤ s := le_of_lt hs
  simp only [norm_norm, Real.norm_eq_abs, abs_abs]
  rcases le_total s t with hst | hst
  · have h1 := hK s t hs0 hst i
    have h2 := mul_le_mul_of_nonneg_right (le_abs_self Kc) (by linarith : (0:ℝ) ≤ t - s)
    rw [abs_sub_comm, abs_of_nonpos (by linarith : s - t ≤ 0)]
    linarith
  · have h1 := hK t s ht.le hst i
    have h2 := mul_le_mul_of_nonneg_right (le_abs_self Kc) (by linarith : (0:ℝ) ≤ s - t)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s - t)]
    linarith

lemma PF_Z_contAt {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t) (i : Fin I) : ContinuousAt (fun s => Zh s i) t := by
  have hev : (fun s => Zh s i) =ᶠ[𝓝 t] fun s => Zh 0 i + (dat.lam i * s +
      ∑ k, dat.P k i * (Th s k / dat.m k)) - Th s i / dat.m i := by
    filter_upwards [Ici_mem_nhds ht] with s hs
    rw [congrFun (hsol.1 s hs) i, hsol.2.2.1 s hs i]
    simp only [hsol.2.2.2.1 s hs]
  refine ContinuousAt.congr ?_ hev.symm
  have hT := fun k => PF_T_contAt dat Ah Dh Th Zh hsol t ht k
  have hS : ContinuousAt (fun s => ∑ k, dat.P k i * (Th s k / dat.m k)) t :=
    tendsto_finsetSum _ (fun k _ => continuousAt_const.mul ((hT k).div_const _))
  exact (continuousAt_const.add ((continuousAt_const.mul continuousAt_id).add hS)).sub
    ((hT i).div_const _)

lemma PF_Y_contAt {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t) : ContinuousAt (fun s => groupAggregate dat.grp (Zh s)) t := by
  rw [continuousAt_pi]
  intro ℓ
  unfold groupAggregate
  exact tendsto_finsetSum _ (fun i _ => PF_Z_contAt dat Ah Dh Th Zh hsol t ht i)

lemma PF_Y_nonneg {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (s : ℝ) (hs : 0 ≤ s) (ℓ : Fin L) : 0 ≤ groupAggregate dat.grp (Zh s) ℓ :=
  Finset.sum_nonneg (fun i _ => hsol.2.1 s hs i)

lemma PF_V_contAt {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun s => PFV dat.TildeAllocSet (groupAggregate dat.grp (Zh s))) t := by
  have h1 := PFV_continuousWithinAt dat.TildeAllocSet hdom _
    (PF_Y_nonneg dat Ah Dh Th Zh hsol t ht.le)
  have h2 : Tendsto (fun s => groupAggregate dat.grp (Zh s)) (𝓝 t)
      (𝓝[{Y | ∀ ℓ, 0 ≤ Y ℓ}] (groupAggregate dat.grp (Zh t))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨PF_Y_contAt dat Ah Dh Th Zh hsol t ht, ?_⟩
    filter_upwards [Ici_mem_nhds ht] with s hs
    exact PF_Y_nonneg dat Ah Dh Th Zh hsol s hs
  exact h1.tendsto.comp h2

/-- R1: the entropy with arbitrary positive weights is continuous on `(0,∞)`. -/
theorem PF_phiF_cont {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (β : Fin I → ℝ) (hβ : ∀ i, 0 < β i)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) :
    ContinuousOn (phiF β Dh Zh) (Set.Ioi 0) := by
  intro t ht
  have ht' : (0:ℝ) < t := ht
  refine ContinuousAt.continuousWithinAt ?_
  have hev : phiF β Dh Zh =ᶠ[𝓝 t] fun s =>
      PFV dat.TildeAllocSet (groupAggregate dat.grp (Zh s)) +
      (∑ i, Zh s i * Real.log (Zh s i) -
        ∑ ℓ, groupAggregate dat.grp (Zh s) ℓ * Real.log (groupAggregate dat.grp (Zh s) ℓ) -
        ∑ i, Zh s i * Real.log (dat.m i * β i)) := by
    filter_upwards [Ioi_mem_nhds ht'] with s hs
    exact PF_phiF_eq_V dat hdom β hβ Ah Dh Th Zh hsol s hs
  refine ContinuousAt.congr ?_ hev.symm
  have hY := PF_Y_contAt dat Ah Dh Th Zh hsol t ht'
  have hZ := fun i => PF_Z_contAt dat Ah Dh Th Zh hsol t ht' i
  have hYl : ∀ ℓ, ContinuousAt (fun s => groupAggregate dat.grp (Zh s) ℓ) t :=
    fun ℓ => (continuousAt_pi.mp hY) ℓ
  have hzl : ∀ i, ContinuousAt (fun s => Zh s i * Real.log (Zh s i)) t := fun i =>
    (Real.continuous_mul_log.continuousAt).comp (f := fun s => Zh s i) (hZ i)
  have hyl : ∀ ℓ, ContinuousAt (fun s => groupAggregate dat.grp (Zh s) ℓ *
      Real.log (groupAggregate dat.grp (Zh s) ℓ)) t := fun ℓ =>
    (Real.continuous_mul_log.continuousAt).comp (f := fun s => groupAggregate dat.grp (Zh s) ℓ)
      (hYl ℓ)
  have hA : ContinuousAt (fun s => ∑ i, Zh s i * Real.log (Zh s i)) t :=
    tendsto_finsetSum _ (fun i _ => hzl i)
  have hB : ContinuousAt (fun s => ∑ ℓ, groupAggregate dat.grp (Zh s) ℓ *
      Real.log (groupAggregate dat.grp (Zh s) ℓ)) t :=
    tendsto_finsetSum _ (fun ℓ _ => hyl ℓ)
  have hC : ContinuousAt (fun s => ∑ i, Zh s i * Real.log (dat.m i * β i)) t :=
    tendsto_finsetSum _ (fun i _ => (hZ i).mul continuousAt_const)
  exact (PF_V_contAt dat hdom Ah Dh Th Zh hsol t ht').add ((hA.sub hB).sub hC)

/-- Strict concavity: two maximizers that are positive on `supp Y` agree there. -/
lemma PF_unique_pos_max {L : ℕ} (A : Set (Fin L → ℝ)) (hdom : IsPFDomain A)
    (Y : Fin L → ℝ) (hY : ∀ ℓ, 0 ≤ Y ℓ) (x y : Fin L → ℝ) (hxA : x ∈ A) (hyA : y ∈ A)
    (hxp : ∀ ℓ, 0 < Y ℓ → 0 < x ℓ) (hyp : ∀ ℓ, 0 < Y ℓ → 0 < y ℓ)
    (hx : PFV A Y ≤ PFG Y x) (hy : PFV A Y ≤ PFG Y y) :
    ∀ ℓ, 0 < Y ℓ → x ℓ = y ℓ := by
  by_contra hne
  push Not at hne
  obtain ⟨ℓ0, hℓ0, hxy⟩ := hne
  set w : Fin L → ℝ := fun ℓ => (x ℓ + y ℓ) / 2 with hw
  have hwA : w ∈ A := by
    have : w = (1/2 : ℝ) • x + (1/2 : ℝ) • y := by funext ℓ; simp [hw]; ring
    rw [this]; exact hdom.2.2.1 hxA hyA (by norm_num) (by norm_num) (by norm_num)
  have hwp : ∀ ℓ, 0 < Y ℓ → 0 < w ℓ := fun ℓ hℓ => by
    simp only [hw]; linarith [hxp ℓ hℓ, hyp ℓ hℓ]
  have hwV := PFV_ge A hdom Y hY w hwA (fun ℓ hℓ => (hwp ℓ hℓ).ne')
  have hterm : ∀ ℓ, Y ℓ * (Real.log (x ℓ) + Real.log (y ℓ)) / 2 ≤ Y ℓ * Real.log (w ℓ) := by
    intro ℓ
    rcases eq_or_lt_of_le (hY ℓ) with h0 | hp
    · rw [← h0]; simp
    · have hx0 := hxp ℓ hp; have hy0 := hyp ℓ hp
      have hle : x ℓ * y ℓ ≤ w ℓ ^ 2 := by simp only [hw]; nlinarith [sq_nonneg (x ℓ - y ℓ)]
      have h1 : Real.log (x ℓ) + Real.log (y ℓ) ≤ 2 * Real.log (w ℓ) := by
        rw [← Real.log_mul hx0.ne' hy0.ne', show 2 * Real.log (w ℓ) = Real.log (w ℓ ^ 2) by
          rw [Real.log_pow]; push_cast; ring]
        exact Real.log_le_log (mul_pos hx0 hy0) hle
      nlinarith
  have hstrict : Y ℓ0 * (Real.log (x ℓ0) + Real.log (y ℓ0)) / 2 < Y ℓ0 * Real.log (w ℓ0) := by
    have hx0 := hxp ℓ0 hℓ0; have hy0 := hyp ℓ0 hℓ0
    have hlt : x ℓ0 * y ℓ0 < w ℓ0 ^ 2 := by
      have : 0 < (x ℓ0 - y ℓ0) ^ 2 := by
        have : x ℓ0 - y ℓ0 ≠ 0 := sub_ne_zero.mpr hxy
        positivity
      simp only [hw]; nlinarith
    have h1 : Real.log (x ℓ0) + Real.log (y ℓ0) < 2 * Real.log (w ℓ0) := by
      rw [← Real.log_mul hx0.ne' hy0.ne', show 2 * Real.log (w ℓ0) = Real.log (w ℓ0 ^ 2) by
        rw [Real.log_pow]; push_cast; ring]
      exact Real.log_lt_log (mul_pos hx0 hy0) hlt
    nlinarith
  have hsum : (PFG Y x + PFG Y y) / 2 < PFG Y w := by
    have : (PFG Y x + PFG Y y) / 2 = ∑ ℓ, Y ℓ * (Real.log (x ℓ) + Real.log (y ℓ)) / 2 := by
      unfold PFG; rw [← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl (fun ℓ _ => by ring)
    rw [this]
    exact Finset.sum_lt_sum (fun ℓ _ => hterm ℓ) ⟨ℓ0, Finset.mem_univ _, hstrict⟩
  linarith

/-- Right-continuity of the PF allocation along a solution, on the support. -/
lemma PF_psi_tendsto {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (u : ℝ) (hu : 0 < u) (ℓ : Fin L) (hℓ : 0 < groupAggregate dat.grp (Zh u) ℓ) :
    Tendsto (fun z => psi dat.TildeAllocSet (groupAggregate dat.grp (Zh z)) ℓ) (𝓝[>] u)
      (𝓝 (psi dat.TildeAllocSet (groupAggregate dat.grp (Zh u)) ℓ)) := by
  set A := dat.TildeAllocSet with hA
  set Y0 := groupAggregate dat.grp (Zh u) with hY0def
  have hY0 : ∀ k, 0 ≤ Y0 k := PF_Y_nonneg dat Ah Dh Th Zh hsol u hu.le
  obtain ⟨x, hxm, hpx, hV⟩ := PFV_eq A hdom Y0 hY0
  have hxpos : ∀ k, 0 < Y0 k → 0 < x k := fun k hk => by
    rw [← hpx k hk]; exact PF_psi_pos dat hdom Ah Dh Th Zh hsol u hu k hk
  rw [hpx ℓ hℓ, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, C, hC, hest⟩ := PF_near_est A hdom Y0 hY0
  set K : Set (Fin L → ℝ) := {y | y ∈ A ∧ (∀ k, 0 < Y0 k → δ k ≤ y k) ∧ ε ≤ |y ℓ - x ℓ|} with hK
  -- a uniform gap on K
  obtain ⟨gap, hgap, hgapK⟩ : ∃ gap : ℝ, 0 < gap ∧ ∀ y ∈ K, PFG Y0 y ≤ PFV A Y0 - gap := by
    by_cases hne : K.Nonempty
    · have hKc : IsCompact K := by
        refine Metric.isCompact_of_isClosed_isBounded ?_ (hdom.1.subset (fun y hy => hy.1))
        have hc1 : IsClosed {y : Fin L → ℝ | ∀ k, 0 < Y0 k → δ k ≤ y k} := by
          have : {y : Fin L → ℝ | ∀ k, 0 < Y0 k → δ k ≤ y k} =
              ⋂ k, {y : Fin L → ℝ | 0 < Y0 k → δ k ≤ y k} := by ext y; simp
          rw [this]
          refine isClosed_iInter (fun k => ?_)
          by_cases hk : 0 < Y0 k
          · simp only [hk, forall_true_left]
            exact isClosed_le continuous_const (continuous_apply k)
          · simp [hk]
        have hc2 : IsClosed {y : Fin L → ℝ | ε ≤ |y ℓ - x ℓ|} :=
          isClosed_le continuous_const ((continuous_apply ℓ).sub continuous_const).abs
        exact hdom.2.1.inter (hc1.inter hc2)
      have hcont : ContinuousOn (PFG Y0) K := by
        unfold PFG
        refine continuousOn_finsetSum _ (fun k _ => ?_)
        rcases eq_or_lt_of_le (hY0 k) with h0 | hk
        · simp only [← h0, zero_mul]; exact continuousOn_const
        · refine continuousOn_const.mul ?_
          intro y hy
          have : y k ≠ 0 := (lt_of_lt_of_le (hδ k) (hy.2.1 k hk)).ne'
          exact ((Real.continuousAt_log this).comp (f := fun p : Fin L → ℝ => p k)
            (continuous_apply k).continuousAt).continuousWithinAt
      obtain ⟨ys, hysK, hysmax⟩ := hKc.exists_isMaxOn hne hcont
      have hlt : PFG Y0 ys < PFV A Y0 := by
        by_contra hge
        push Not at hge
        have hys_pos : ∀ k, 0 < Y0 k → 0 < ys k := fun k hk =>
          lt_of_lt_of_le (hδ k) (hysK.2.1 k hk)
        have heq := PF_unique_pos_max A hdom Y0 hY0 x ys hxm.1 hysK.1 hxpos hys_pos hV.le hge
          ℓ hℓ
        have := hysK.2.2
        rw [← heq, sub_self, abs_zero] at this
        linarith
      refine ⟨PFV A Y0 - PFG Y0 ys, by linarith, fun y hy => ?_⟩
      have := hysmax hy
      simp only [Set.mem_ofPred_eq] at this
      linarith
    · refine ⟨1, one_pos, fun y hy => absurd ⟨y, hy⟩ hne⟩
  -- pull everything back along the solution
  have hYc := PF_Y_contAt dat Ah Dh Th Zh hsol u hu
  have h1 : ∀ᶠ z in 𝓝 u, ∀ k, 0 < Y0 k → 0 < groupAggregate dat.grp (Zh z) k := by
    refine Filter.eventually_all.mpr (fun k => ?_)
    by_cases hk : 0 < Y0 k
    · filter_upwards [(continuousAt_pi.mp hYc k).eventually (lt_mem_nhds hk)] with z hz _
      exact hz
    · exact Filter.Eventually.of_forall (fun _ h => absurd h hk)
  have h2 := hYc.eventually hest
  have h3 := hYc.eventually (PFV_lsc A hdom Y0 hY0 (gap / 3) (by linarith))
  have h4 : ∀ᶠ z in 𝓝 u, C * ∑ k, |groupAggregate dat.grp (Zh z) k - Y0 k| < gap / 3 := by
    have := ((PF_sum_abs_tendsto Y0).comp hYc).const_mul C
    simp only [Function.comp_def, sub_self, abs_zero, Finset.sum_const_zero, mul_zero] at this
    exact this.eventually (gt_mem_nhds (by linarith))
  filter_upwards [nhdsWithin_le_nhds (h1.and (h2.and (h3.and h4))), self_mem_nhdsWithin]
    with z ⟨hz1, hz2, hz3, hz4⟩ hzu
  have hz : 0 < z := lt_trans hu hzu
  set Yz := groupAggregate dat.grp (Zh z) with hYz
  have hYznn : ∀ k, 0 ≤ Yz k := PF_Y_nonneg dat Ah Dh Th Zh hsol z hz.le
  obtain ⟨xz, hxzm, hpxz, hVz⟩ := PFV_eq A hdom Yz hYznn
  obtain ⟨hxzA, hgxz, -⟩ := PF_max_fwd A hdom Yz xz hYznn hxzm
  obtain ⟨hlb, hdiff⟩ := hz2 hYznn xz hxzA hgxz hVz.le
  have hxzpos : ∀ k, 0 < Y0 k → 0 < xz k := fun k hk => by
    rw [← hpxz k (hz1 k hk)]; exact PF_psi_pos dat hdom Ah Dh Th Zh hsol z hz k (hz1 k hk)
  rw [hpxz ℓ (hz1 ℓ hℓ), Real.dist_eq]
  by_contra hfar
  push Not at hfar
  have hxzK : xz ∈ K := ⟨hxzA, fun k hk => by
    have := hlb k hk; rwa [abs_of_pos (hxzpos k hk)] at this, hfar⟩
  have hg := hgapK xz hxzK
  have hl := hz3 hYznn
  rw [hVz] at hl
  linarith

/-! ## C2e: Dini bounds for the entropy with arbitrary positive weights -/

lemma PF_logD_le {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (β : Fin I → ℝ) (hβ : ∀ i, 0 < β i) :
    ∃ C : Fin I → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ (Ah Dh Th Zh : ℝ → Fin I → ℝ),
      IsPFFluidModelSolution dat Ah Dh Th Zh → ∀ z, 0 < z → ∀ i, 0 < Zh z i →
        Real.log (derivWithin (fun s => Dh s i) (Set.Ici z) z / β i) ≤ C i := by
  obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le.mp hdom.1)
  set R0 : ℝ := max R 0 with hR0
  have hR0nn : 0 ≤ R0 := le_max_right _ _
  refine ⟨fun i => max 0 (Real.log (R0 / (dat.m i * β i))), fun i => le_max_left _ _, ?_⟩
  intro Ah Dh Th Zh hsol z hz i hZpos
  have hZnn : ∀ j, 0 ≤ Zh z j := fun j => hsol.2.1 z hz.le j
  have hD := PF_Ddot_formula dat Ah Dh Th Zh hsol z hz i hZpos
  rw [hD.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici z)]
  set Y := groupAggregate dat.grp (Zh z) (dat.grp i) with hY
  have hYge : Zh z i ≤ Y := PF_Z_le_Y dat.grp (Zh z) hZnn i
  have hYpos : 0 < Y := lt_of_lt_of_le hZpos hYge
  have hpsi := PF_psi_abs_le dat.TildeAllocSet R hR (groupAggregate dat.grp (Zh z)) (dat.grp i)
  set ps := psi dat.TildeAllocSet (groupAggregate dat.grp (Zh z)) (dat.grp i) with hps
  have hmi := dat.hm i
  have hai := hβ i
  have habs : |ps * Zh z i / Y / dat.m i / β i| ≤ R0 / (dat.m i * β i) := by
    have hq : Zh z i / Y ≤ 1 := (div_le_one hYpos).mpr hYge
    have hq0 : 0 ≤ Zh z i / Y := div_nonneg hZpos.le hYpos.le
    have : ps * Zh z i / Y / dat.m i / β i = ps * (Zh z i / Y) / (dat.m i * β i) := by
      field_simp
    rw [this, abs_div, abs_mul, abs_of_nonneg hq0, abs_of_pos (mul_pos hmi hai)]
    apply div_le_div_of_nonneg_right _ (mul_pos hmi hai).le
    calc |ps| * (Zh z i / Y) ≤ R0 * 1 := mul_le_mul hpsi hq hq0 hR0nn
      _ = R0 := mul_one _
  exact PF_log_le_of_abs_le _ _ (div_nonneg hR0nn (mul_pos hmi hai).le) habs

lemma PF_Ddot_tendsto {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (u : ℝ) (hu : 0 < u) (i : Fin I) (hZ : 0 < Zh u i) :
    Tendsto (fun z => derivWithin (fun s => Dh s i) (Set.Ici z) z) (𝓝[>] u)
      (𝓝 (psi dat.TildeAllocSet (groupAggregate dat.grp (Zh u)) (dat.grp i) * Zh u i /
        groupAggregate dat.grp (Zh u) (dat.grp i) / dat.m i)) := by
  have hZnn : ∀ j, 0 ≤ Zh u j := fun j => hsol.2.1 u hu.le j
  have hYp : 0 < groupAggregate dat.grp (Zh u) (dat.grp i) :=
    lt_of_lt_of_le hZ (PF_Z_le_Y dat.grp (Zh u) hZnn i)
  have hZc := PF_Z_contAt dat Ah Dh Th Zh hsol u hu i
  have hYc := (continuousAt_pi.mp (PF_Y_contAt dat Ah Dh Th Zh hsol u hu)) (dat.grp i)
  have hlim : Tendsto (fun z => psi dat.TildeAllocSet (groupAggregate dat.grp (Zh z)) (dat.grp i) *
      Zh z i / groupAggregate dat.grp (Zh z) (dat.grp i) / dat.m i) (𝓝[>] u)
      (𝓝 (psi dat.TildeAllocSet (groupAggregate dat.grp (Zh u)) (dat.grp i) * Zh u i /
        groupAggregate dat.grp (Zh u) (dat.grp i) / dat.m i)) :=
    (((PF_psi_tendsto dat hdom Ah Dh Th Zh hsol u hu (dat.grp i) hYp).mul
      (tendsto_nhdsWithin_of_tendsto_nhds hZc)).div
      (tendsto_nhdsWithin_of_tendsto_nhds hYc) hYp.ne').div_const _
  refine hlim.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (hZc.eventually (lt_mem_nhds hZ)), self_mem_nhdsWithin]
    with z hz hzu
  have hz0 : 0 < z := lt_trans hu hzu
  exact ((PF_Ddot_formula dat Ah Dh Th Zh hsol z hz0 i hz).hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_Ici z)).symm

lemma PF_slope_right (f : ℝ → ℝ) (f' t : ℝ) (hf : HasDerivAt f f' t) :
    Tendsto (fun z => (f z - f t) / (z - t)) (𝓝[>] t) (𝓝 f') := by
  have := (hasDerivAt_iff_tendsto_slope.mp hf).mono_left
    (nhdsWithin_mono t (fun y (hy : t < y) => ne_of_gt hy))
  refine this.congr (fun z => ?_)
  rw [slope_def_field]

lemma PF_neg_mul_log_le (q b : ℝ) (hq : 0 < q) (hb : 0 < b) : q * (-Real.log (q / b)) ≤ b := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hq hb)
  rw [inv_div] at h
  calc q * (-Real.log (q / b)) ≤ q * (b / q - 1) := mul_le_mul_of_nonneg_left (by linarith) hq.le
    _ = b - q := by field_simp
    _ ≤ b := by linarith

/-- R2: Dini bound at regular points, any positive weights `β`. -/
theorem PF_dini_regular {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (β : Fin I → ℝ) (hβ : ∀ i, 0 < β i)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t) (hreg : RegularPoint Ah Dh Th Zh t) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ z in 𝓝[>] t, phiF β Dh Zh z - phiF β Dh Zh t ≤
      (∑ i, deriv (fun s => Zh s i) t * Real.log (deriv (fun s => Dh s i) t / β i) + η) *
        (z - t) := by
  obtain ⟨C, hC0, hC⟩ := PF_logD_le dat hdom β hβ
  have hfacts := PF_regular_facts dat Ah Dh Th Zh hsol t ht hreg
  set η' : ℝ := η / ((I : ℝ) + 1) with hη'
  have hη'pos : 0 < η' := by positivity
  have hIη : (I : ℝ) * η' ≤ η := by
    have hI1 : (0:ℝ) < (I : ℝ) + 1 := by positivity
    have : (I : ℝ) * η' = η * ((I : ℝ) / ((I : ℝ) + 1)) := by rw [hη']; ring
    rw [this]
    have : (I : ℝ) / ((I : ℝ) + 1) ≤ 1 := (div_le_one hI1).mpr (by linarith)
    nlinarith
  have hsupp : ∀ᶠ z in 𝓝[>] t, ∀ i, 0 < Zh t i → 0 < Zh z i := by
    refine Filter.eventually_all.mpr (fun i => ?_)
    by_cases hi : 0 < Zh t i
    · filter_upwards [nhdsWithin_le_nhds ((PF_Z_contAt dat Ah Dh Th Zh hsol t ht i).eventually
        (lt_mem_nhds hi))] with z hz _ using hz
    · exact Filter.Eventually.of_forall (fun _ h => absurd h hi)
  have hslopeZ : ∀ i, Tendsto (fun z => (Zh z i - Zh t i) / (z - t)) (𝓝[>] t)
      (𝓝 (deriv (fun s => Zh s i) t)) := fun i =>
    PF_slope_right (fun s => Zh s i) _ t ((differentiableAt_pi.mp hreg.2.2.2) i).hasDerivAt
  have hterm : ∀ i, ∀ᶠ z in 𝓝[>] t, (Zh z i - Zh t i) *
      Real.log (derivWithin (fun s => Dh s i) (Set.Ici z) z / β i) ≤
      (deriv (fun s => Zh s i) t * Real.log (deriv (fun s => Dh s i) t / β i) + η') * (z - t) := by
    intro i
    have hZnn := hsol.2.1 t ht.le i
    rcases eq_or_lt_of_le hZnn with h0 | hZp
    · have hdz : deriv (fun s => Zh s i) t = 0 := (hfacts i).2.2 h0.symm
      have hsl := hslopeZ i
      rw [hdz] at hsl
      have hc1 : 0 < C i + 1 := by linarith [hC0 i]
      have hev := hsl.eventually (gt_mem_nhds (show (0:ℝ) < η' / (C i + 1) by positivity))
      filter_upwards [hev, self_mem_nhdsWithin] with z hz hzt
      have hzt' : t < z := hzt
      have hz0 : 0 < z := lt_trans ht hzt'
      rw [hdz, zero_mul, zero_add, ← h0, sub_zero]
      rw [← h0, sub_zero, div_lt_iff₀ (by linarith)] at hz
      have hZz := hsol.2.1 z hz0.le i
      rcases eq_or_lt_of_le hZz with hz0' | hzp
      · rw [← hz0', zero_mul]; exact mul_nonneg hη'pos.le (by linarith)
      · have hl := hC Ah Dh Th Zh hsol z hz0 i hzp
        have hpos := mul_pos hη'pos (sub_pos.mpr hzt')
        calc Zh z i * Real.log (derivWithin (fun s => Dh s i) (Set.Ici z) z / β i)
            ≤ Zh z i * C i := mul_le_mul_of_nonneg_left hl hZz
          _ ≤ η' / (C i + 1) * (z - t) * C i := mul_le_mul_of_nonneg_right hz.le (hC0 i)
          _ ≤ η' * (z - t) := by
              rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hc1]
              nlinarith [hC0 i]
    · have hD := PF_Ddot_formula dat Ah Dh Th Zh hsol t ht i hZp
      rw [hD.deriv]
      have hZnn' : ∀ j, 0 ≤ Zh t j := fun j => hsol.2.1 t ht.le j
      have hYp : 0 < groupAggregate dat.grp (Zh t) (dat.grp i) :=
        lt_of_lt_of_le hZp (PF_Z_le_Y dat.grp (Zh t) hZnn' i)
      have hps := PF_psi_pos dat hdom Ah Dh Th Zh hsol t ht (dat.grp i) hYp
      set q0 := psi dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) (dat.grp i) * Zh t i /
        groupAggregate dat.grp (Zh t) (dat.grp i) / dat.m i with hq0
      have hq0pos : 0 < q0 := by have := dat.hm i; positivity
      have hlog : Tendsto (fun z => Real.log (derivWithin (fun s => Dh s i) (Set.Ici z) z / β i))
          (𝓝[>] t) (𝓝 (Real.log (q0 / β i))) :=
        ((PF_Ddot_tendsto dat hdom Ah Dh Th Zh hsol t ht i hZp).div_const (β i)).log
          (div_pos hq0pos (hβ i)).ne'
      have hprod := (hslopeZ i).mul hlog
      have hev := hprod.eventually (gt_mem_nhds (show deriv (fun s => Zh s i) t *
        Real.log (q0 / β i) < deriv (fun s => Zh s i) t * Real.log (q0 / β i) + η' by linarith))
      filter_upwards [hev, self_mem_nhdsWithin] with z hz hzt
      have hzt' : 0 < z - t := sub_pos.mpr hzt
      have heq : (Zh z i - Zh t i) * Real.log (derivWithin (fun s => Dh s i) (Set.Ici z) z / β i) =
          ((Zh z i - Zh t i) / (z - t) *
            Real.log (derivWithin (fun s => Dh s i) (Set.Ici z) z / β i)) * (z - t) := by
        field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_right hz.le hzt'.le
  filter_upwards [hsupp, self_mem_nhdsWithin, Filter.eventually_all.mpr hterm] with z hz hzt hzi
  have hzt' : t < z := hzt
  have hz0 : 0 < z := lt_trans ht hzt'
  have hsub := PF_phi_sub_le dat hdom β hβ Ah Dh Th Zh hsol t z ht hz0 hz
  refine hsub.trans ?_
  set a : Fin I → ℝ := fun i => deriv (fun s => Zh s i) t *
    Real.log (deriv (fun s => Dh s i) t / β i) with ha
  have hs : ∑ i, (a i + η') * (z - t) = (∑ i, a i + (I : ℝ) * η') * (z - t) := by
    rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  calc _ ≤ ∑ i, (a i + η') * (z - t) := Finset.sum_le_sum (fun i _ => hzi i)
    _ = (∑ i, a i + (I : ℝ) * η') * (z - t) := hs
    _ ≤ (∑ i, a i + η) * (z - t) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)

/-- R3: a global Dini bound on `(0,∞)`, any positive weights `β`. -/
theorem PF_dini_bdd {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP : ∀ i j, 0 ≤ dat.P i j) (β : Fin I → ℝ) (hβ : ∀ i, 0 < β i)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u, 0 < u → ∀ᶠ z in 𝓝[>] u,
      phiF β Dh Zh z - phiF β Dh Zh u ≤ M * (z - u) := by
  obtain ⟨C, hC0, hC⟩ := PF_logD_le dat hdom β hβ
  have hZeq := hsol.1
  have hA := hsol.2.2.1
  have hDT := hsol.2.2.2.1
  have hmono := hsol.2.2.2.2.1.2.1
  obtain ⟨Kc, hK⟩ := hsol.2.2.2.2.1.2.2
  set K : Fin I → ℝ := fun i => dat.lam i + ∑ k, dat.P k i * (|Kc| / dat.m k) with hKdef
  have hKnn : ∀ i, 0 ≤ K i := fun i => add_nonneg (hlam i) (Finset.sum_nonneg (fun k _ =>
    mul_nonneg (hP k i) (div_nonneg (abs_nonneg _) (dat.hm k).le)))
  set Mi : Fin I → ℝ := fun i => K i * C i + β i + 1 with hMi
  have hMinn : ∀ i, 0 ≤ Mi i := fun i => by
    have := mul_nonneg (hKnn i) (hC0 i); have := hβ i; simp only [hMi]; linarith
  refine ⟨∑ i, Mi i, Finset.sum_nonneg (fun i _ => hMinn i), fun u hu => ?_⟩
  -- increments on [u, z]
  have hDinc : ∀ z, u ≤ z → ∀ k, 0 ≤ Dh z k - Dh u k ∧ Dh z k - Dh u k ≤ |Kc| / dat.m k * (z - u) := by
    intro z huz k
    have hz0 : 0 ≤ z := le_trans hu.le huz
    rw [hDT z hz0 k, hDT u hu.le k, ← sub_div]
    have hmk := dat.hm k
    have hT1 : 0 ≤ Th z k - Th u k := by linarith [hmono huz k]
    have hT2 : Th z k - Th u k ≤ |Kc| * (z - u) := by
      have := hK u z hu.le huz k
      have h3 := mul_le_mul_of_nonneg_right (le_abs_self Kc) (by linarith : (0:ℝ) ≤ z - u)
      linarith [le_abs_self (Th z k - Th u k)]
    refine ⟨div_nonneg hT1 hmk.le, ?_⟩
    rw [div_le_iff₀ hmk]
    have : |Kc| / dat.m k * (z - u) * dat.m k = |Kc| * (z - u) := by field_simp
    linarith
  have hZinc : ∀ z, u ≤ z → ∀ i, -(Dh z i - Dh u i) ≤ Zh z i - Zh u i ∧
      Zh z i - Zh u i ≤ K i * (z - u) := by
    intro z huz i
    have hz0 : 0 ≤ z := le_trans hu.le huz
    have hdiff : Zh z i - Zh u i = dat.lam i * (z - u) +
        ∑ k, dat.P k i * (Dh z k - Dh u k) - (Dh z i - Dh u i) := by
      rw [congrFun (hZeq z hz0) i, congrFun (hZeq u hu.le) i, hA z hz0 i, hA u hu.le i]
      have : ∑ k, dat.P k i * (Dh z k - Dh u k) =
          ∑ k, dat.P k i * Dh z k - ∑ k, dat.P k i * Dh u k := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [this]; ring
    have hS0 : 0 ≤ ∑ k, dat.P k i * (Dh z k - Dh u k) :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (hP k i) (hDinc z huz k).1)
    have hS1 : ∑ k, dat.P k i * (Dh z k - Dh u k) ≤ ∑ k, dat.P k i * (|Kc| / dat.m k) * (z - u) :=
      Finset.sum_le_sum (fun k _ => by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hDinc z huz k).2 (hP k i))
    have hS2 : ∑ k, dat.P k i * (|Kc| / dat.m k) * (z - u) =
        (∑ k, dat.P k i * (|Kc| / dat.m k)) * (z - u) := by rw [Finset.sum_mul]
    have hl := mul_nonneg (hlam i) (show (0:ℝ) ≤ z - u by linarith)
    have hDi := (hDinc z huz i).1
    refine ⟨by rw [hdiff]; linarith, ?_⟩
    rw [hdiff]
    simp only [hKdef]
    nlinarith
  have hterm : ∀ i, ∀ᶠ z in 𝓝[>] u, (Zh z i - Zh u i) *
      Real.log (derivWithin (fun s => Dh s i) (Set.Ici z) z / β i) ≤ Mi i * (z - u) := by
    intro i
    have hKC := mul_nonneg (hKnn i) (hC0 i)
    have hβi := hβ i
    rcases eq_or_lt_of_le (hsol.2.1 u hu.le i) with h0 | hZp
    · filter_upwards [self_mem_nhdsWithin] with z hzu
      have hzu' : u < z := hzu
      have hz0 : 0 < z := lt_trans hu hzu'
      have hzu0 : 0 ≤ z - u := by linarith
      rw [← h0, sub_zero]
      have hinc := (hZinc z hzu'.le i).2
      rw [← h0, sub_zero] at hinc
      rcases eq_or_lt_of_le (hsol.2.1 z hz0.le i) with hz0' | hzp
      · rw [← hz0', zero_mul]; exact mul_nonneg (hMinn i) hzu0
      · have hl := hC Ah Dh Th Zh hsol z hz0 i hzp
        calc Zh z i * Real.log (derivWithin (fun s => Dh s i) (Set.Ici z) z / β i)
            ≤ Zh z i * C i := mul_le_mul_of_nonneg_left hl hzp.le
          _ ≤ K i * (z - u) * C i := mul_le_mul_of_nonneg_right hinc (hC0 i)
          _ ≤ Mi i * (z - u) := by simp only [hMi]; nlinarith
    · have hD := PF_Ddot_formula dat Ah Dh Th Zh hsol u hu i hZp
      have hZnn' : ∀ j, 0 ≤ Zh u j := fun j => hsol.2.1 u hu.le j
      have hYp : 0 < groupAggregate dat.grp (Zh u) (dat.grp i) :=
        lt_of_lt_of_le hZp (PF_Z_le_Y dat.grp (Zh u) hZnn' i)
      have hps := PF_psi_pos dat hdom Ah Dh Th Zh hsol u hu (dat.grp i) hYp
      set q0 := psi dat.TildeAllocSet (groupAggregate dat.grp (Zh u)) (dat.grp i) * Zh u i /
        groupAggregate dat.grp (Zh u) (dat.grp i) / dat.m i with hq0
      have hq0pos : 0 < q0 := by have := dat.hm i; positivity
      have hslD := PF_slope_right (fun s => Dh s i) q0 u hD
      have hlog : Tendsto (fun z => Real.log (derivWithin (fun s => Dh s i) (Set.Ici z) z / β i))
          (𝓝[>] u) (𝓝 (Real.log (q0 / β i))) :=
        ((PF_Ddot_tendsto dat hdom Ah Dh Th Zh hsol u hu i hZp).div_const (β i)).log
          (div_pos hq0pos hβi).ne'
      have hprod := hslD.mul hlog.neg
      have hbound : q0 * -Real.log (q0 / β i) < β i + 1 := by
        linarith [PF_neg_mul_log_le q0 (β i) hq0pos hβi]
      have hev := hprod.eventually (gt_mem_nhds hbound)
      filter_upwards [hev, self_mem_nhdsWithin, nhdsWithin_le_nhds
        ((PF_Z_contAt dat Ah Dh Th Zh hsol u hu i).eventually (lt_mem_nhds hZp))] with z hz hzu hzp
      have hzu1 : u < z := hzu
      have hzu' : 0 < z - u := sub_pos.mpr hzu1
      have hz0 : 0 < z := lt_trans hu hzu1
      obtain ⟨hlo, hhi⟩ := hZinc z hzu1.le i
      have hl := hC Ah Dh Th Zh hsol z hz0 i hzp
      set lv := Real.log (derivWithin (fun s => Dh s i) (Set.Ici z) z / β i) with hlv
      have hdz : (Dh z i - Dh u i) / (z - u) * -lv < β i + 1 := hz
      have heq : (Dh z i - Dh u i) / (z - u) * -lv * (z - u) = (Dh z i - Dh u i) * -lv := by
        field_simp
      have hdz' : (Dh z i - Dh u i) * -lv < (β i + 1) * (z - u) := by
        rw [← heq]; exact mul_lt_mul_of_pos_right hdz hzu'
      by_cases hsign : 0 ≤ lv
      · calc (Zh z i - Zh u i) * lv ≤ K i * (z - u) * lv := mul_le_mul_of_nonneg_right hhi hsign
          _ ≤ K i * (z - u) * C i := mul_le_mul_of_nonneg_left hl (mul_nonneg (hKnn i) hzu'.le)
          _ ≤ Mi i * (z - u) := by simp only [hMi]; nlinarith
      · push Not at hsign
        calc (Zh z i - Zh u i) * lv ≤ (-(Dh z i - Dh u i)) * lv :=
              mul_le_mul_of_nonpos_right hlo hsign.le
          _ = (Dh z i - Dh u i) * -lv := by ring
          _ ≤ (β i + 1) * (z - u) := hdz'.le
          _ ≤ Mi i * (z - u) := mul_le_mul_of_nonneg_right (by simp only [hMi]; linarith) hzu'.le
  have hsupp : ∀ᶠ z in 𝓝[>] u, ∀ i, 0 < Zh u i → 0 < Zh z i := by
    refine Filter.eventually_all.mpr (fun i => ?_)
    by_cases hi : 0 < Zh u i
    · filter_upwards [nhdsWithin_le_nhds ((PF_Z_contAt dat Ah Dh Th Zh hsol u hu i).eventually
        (lt_mem_nhds hi))] with z hz _ using hz
    · exact Filter.Eventually.of_forall (fun _ h => absurd h hi)
  filter_upwards [hsupp, self_mem_nhdsWithin, Filter.eventually_all.mpr hterm] with z hz hzu hzi
  have hzu1 : u < z := hzu
  have hz0 : 0 < z := lt_trans hu hzu1
  have hsub := PF_phi_sub_le dat hdom β hβ Ah Dh Th Zh hsol u z hu hz0 hz
  refine hsub.trans ?_
  calc _ ≤ ∑ i, Mi i * (z - u) := Finset.sum_le_sum (fun i _ => hzi i)
    _ = (∑ i, Mi i) * (z - u) := by rw [Finset.sum_mul]

/-! ## C2d: drift of the perturbed entropy plus the zero-rate work -/

lemma PF_alpha_ge_pow {I : ℕ} (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ) (α : Fin I → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hP : ∀ i j, 0 ≤ P i j) (hα0 : ∀ i, 0 ≤ α i)
    (hα : ∀ i, α i = lam i + ∑ k, P k i * α k) :
    ∀ j : ℕ, ∀ k i, (P ^ j) k i * lam k ≤ α i := by
  intro j
  induction j with
  | zero =>
    intro k i
    by_cases h : k = i
    · subst h
      simp only [pow_zero, Matrix.one_apply_eq, one_mul]
      have : 0 ≤ ∑ m, P m k * α m := Finset.sum_nonneg (fun m _ => mul_nonneg (hP m k) (hα0 m))
      linarith [hα k]
    · simp only [pow_zero, Matrix.one_apply_ne h, zero_mul]; exact hα0 i
  | succ j ih =>
    intro k i
    rw [pow_succ, Matrix.mul_apply, Finset.sum_mul]
    calc ∑ m, (P ^ j) k m * P m i * lam k = ∑ m, P m i * ((P ^ j) k m * lam k) :=
          Finset.sum_congr rfl (fun m _ => by ring)
      _ ≤ ∑ m, P m i * α m :=
          Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left (ih k m) (hP m i))
      _ ≤ α i := by linarith [hα i, hlam i]

/-- The Bregman penalty is nonnegative, and large when some `u i0 ≥ 1+η` is reachable from an
exogenous source along edges carrying positive `α`-flow (weights `β ≥ α`). -/
lemma PF_pen_lb {I : ℕ} (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ) (α β : Fin I → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hP : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j ≤ 1)
    (hα0 : ∀ i, 0 ≤ α i) (hαβ : ∀ i, α i ≤ β i)
    (hα : ∀ i, α i = lam i + ∑ k, P k i * α k)
    (c : ℝ) (hc : 0 < c) (hcl : ∀ k, 0 < lam k → c ≤ lam k)
    (hcP : ∀ k i, 0 < P k i * α k → c ≤ P k i * α k)
    (u : Fin I → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hzero : ∀ i, u i = 0 → lam i = 0 ∧ ∀ k, P k i * (β k * u k) = 0)
    (N : ℕ) (η : ℝ) (hη : 0 < η) (hη3 : η ≤ 3) (i0 : Fin I) :
    0 ≤ ∑ i, lam i * PFB 1 (u i) +
        ∑ k, β k * (1 - ∑ i, P k i) * (u k * Real.log (u k) - u k + 1) +
        ∑ k, ∑ i, P k i * β k * PFB (u k) (u i) ∧
    (1 + η ≤ u i0 → (∃ j < N, ∃ k, 0 < lam k ∧ 0 < (P ^ j) k i0) →
      c * (η / (3 * N)) ^ 2 ≤ ∑ i, lam i * PFB 1 (u i) +
        ∑ k, β k * (1 - ∑ i, P k i) * (u k * Real.log (u k) - u k + 1) +
        ∑ k, ∑ i, P k i * β k * PFB (u k) (u i)) := by
  have hβ0 : ∀ i, 0 ≤ β i := fun i => (hα0 i).trans (hαβ i)
  have hge := PF_alpha_ge_pow lam P α hlam hP hα0 hα
  set tl : Fin I → ℝ := fun i => lam i * PFB 1 (u i) with htl
  set tq : Fin I → ℝ := fun k => β k * (1 - ∑ i, P k i) * (u k * Real.log (u k) - u k + 1) with htq
  set tB : Fin I → Fin I → ℝ := fun k i => P k i * β k * PFB (u k) (u i) with htB
  have htl_lb : ∀ i, 0 < u i → lam i * (√(u i) - 1) ^ 2 ≤ tl i := by
    intro i hi
    have := PFB_sqrt 1 (u i) zero_le_one hi
    rw [Real.sqrt_one] at this
    exact mul_le_mul_of_nonneg_left this (hlam i)
  have htl_nn : ∀ i, 0 ≤ tl i := by
    intro i
    rcases eq_or_lt_of_le (hu i) with h0 | hp
    · simp [htl, (hzero i h0.symm).1]
    · exact le_trans (mul_nonneg (hlam i) (sq_nonneg _)) (htl_lb i hp)
  have htq_nn : ∀ k, 0 ≤ tq k := fun k =>
    mul_nonneg (mul_nonneg (hβ0 k) (by linarith [hrow k])) (PF_e_nonneg _ (hu k))
  have htB_lb : ∀ k i, 0 < u i → P k i * β k * (√(u i) - √(u k)) ^ 2 ≤ tB k i := by
    intro k i hi
    exact mul_le_mul_of_nonneg_left (PFB_sqrt (u k) (u i) (hu k) hi)
      (mul_nonneg (hP k i) (hβ0 k))
  have htB_nn : ∀ k i, 0 ≤ tB k i := by
    intro k i
    rcases eq_or_lt_of_le (hu i) with h0 | hp
    · have h1 := (hzero i h0.symm).2 k
      rcases mul_eq_zero.mp h1 with h2 | h2
      · simp [htB, h2]
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · simp [htB, h3]
        · simp [htB, h3, ← h0, PFB_zero_left]
    · exact le_trans (mul_nonneg (mul_nonneg (hP k i) (hβ0 k)) (sq_nonneg _)) (htB_lb k i hp)
  have hS1 : 0 ≤ ∑ i, tl i := Finset.sum_nonneg (fun i _ => htl_nn i)
  have hS2 : 0 ≤ ∑ k, tq k := Finset.sum_nonneg (fun k _ => htq_nn k)
  have hS3 : 0 ≤ ∑ k, ∑ i, tB k i :=
    Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun i _ => htB_nn k i))
  refine ⟨by linarith, fun hi0 hN => ?_⟩
  set Pen : ℝ := ∑ i, tl i + ∑ k, tq k + ∑ k, ∑ i, tB k i with hPen
  by_contra hlt
  push Not at hlt
  have hN0 : 0 < N := by
    obtain ⟨j, hj, -⟩ := hN
    omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  set δ : ℝ := η / (3 * N) with hδ
  have hδpos : 0 < δ := by positivity
  have htl_le : ∀ i, tl i ≤ Pen := by
    intro i
    have := Finset.single_le_sum (f := tl) (fun j _ => htl_nn j) (Finset.mem_univ i)
    linarith
  have htB_le : ∀ k i, tB k i ≤ Pen := by
    intro k i
    have h1 := Finset.single_le_sum (f := fun i => tB k i) (fun j _ => htB_nn k j)
      (Finset.mem_univ i)
    have h2 := Finset.single_le_sum (f := fun k => ∑ i, tB k i)
      (fun j _ => Finset.sum_nonneg (fun i _ => htB_nn j i)) (Finset.mem_univ k)
    linarith
  have hchain : ∀ j : ℕ, ∀ k i, 0 < lam k → 0 < (P ^ j) k i → √(u i) < 1 + (j + 1) * δ := by
    intro j
    induction j with
    | zero =>
      intro k i hk hki
      have hki' : k = i := by
        by_contra hne
        simp [Matrix.one_apply_ne hne] at hki
      subst hki'
      have hupos : 0 < u k := by
        rcases eq_or_lt_of_le (hu k) with h0 | hp
        · exact absurd (hzero k h0.symm).1 hk.ne'
        · exact hp
      have h1 := htl_lb k hupos
      have h2 : c * (√(u k) - 1) ^ 2 ≤ lam k * (√(u k) - 1) ^ 2 :=
        mul_le_mul_of_nonneg_right (hcl k hk) (sq_nonneg _)
      have h3 : c * (√(u k) - 1) ^ 2 < c * δ ^ 2 := by linarith [htl_le k]
      have h4 : (√(u k) - 1) ^ 2 < δ ^ 2 := lt_of_mul_lt_mul_left h3 hc.le
      have := PF_sqrt_lt_of_sq_lt _ _ δ hδpos h4
      push_cast
      linarith
    | succ j ih =>
      intro k i hk hki
      rw [pow_succ, Matrix.mul_apply] at hki
      obtain ⟨m, -, hm⟩ := Finset.exists_lt_of_sum_lt
        (show ∑ m, (0 : ℝ) < ∑ m, (P ^ j) k m * P m i by simpa using hki)
      have hPmi : 0 < P m i := by
        rcases lt_or_eq_of_le (hP m i) with h | h
        · exact h
        · rw [← h, mul_zero] at hm; exact absurd hm (lt_irrefl 0)
      have hPj : 0 < (P ^ j) k m := by
        by_contra hneg
        push Not at hneg
        have : (P ^ j) k m * P m i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hPmi.le
        linarith
      have hαm : 0 < α m := lt_of_lt_of_le (mul_pos hPj hk) (hge j k m)
      have hcPm : c ≤ P m i * β m :=
        (hcP m i (mul_pos hPmi hαm)).trans (mul_le_mul_of_nonneg_left (hαβ m) (hP m i))
      have him := ih k m hk hPj
      rcases eq_or_lt_of_le (hu i) with h0 | hp
      · rw [← h0, Real.sqrt_zero]; push_cast; positivity
      · have h1 := htB_lb m i hp
        have h2 : c * (√(u i) - √(u m)) ^ 2 ≤ P m i * β m * (√(u i) - √(u m)) ^ 2 :=
          mul_le_mul_of_nonneg_right hcPm (sq_nonneg _)
        have h3 : c * (√(u i) - √(u m)) ^ 2 < c * δ ^ 2 := by linarith [htB_le m i]
        have h4 : (√(u i) - √(u m)) ^ 2 < δ ^ 2 := lt_of_mul_lt_mul_left h3 hc.le
        have := PF_sqrt_lt_of_sq_lt _ _ δ hδpos h4
        push_cast
        linarith
  obtain ⟨j, hjN, k, hk, hki⟩ := hN
  have hfin := hchain j k i0 hk hki
  have hjN' : ((j : ℝ) + 1) ≤ N := by exact_mod_cast hjN
  have hNδ : ((j : ℝ) + 1) * δ ≤ η / 3 := by
    have : (N : ℝ) * δ = η / 3 := by rw [hδ]; field_simp
    nlinarith
  have hsq : 1 + η / 3 ≤ √(u i0) := by
    rw [Real.le_sqrt (by positivity) (by linarith)]
    nlinarith
  linarith

/-- The drift identity for perturbed weights `β = total rates of λ + ε w`. -/
lemma PF_drift_eps {I : ℕ} (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ)
    (β w u : Fin I → ℝ) (eps : ℝ) (hfix : ∀ i, β i = (lam i + eps * w i) + ∑ k, P k i * β k) :
    ∑ i, (lam i + ∑ k, P k i * (β k * u k) - β i * u i) * Real.log (u i) =
      -(∑ i, lam i * PFB 1 (u i) +
        ∑ k, β k * (1 - ∑ i, P k i) * (u k * Real.log (u k) - u k + 1) +
        ∑ k, ∑ i, P k i * β k * PFB (u k) (u i)) + eps * ∑ i, w i * (1 - u i) := by
  have hid := PF_drift_identity (fun i => lam i + eps * w i) P β u hfix
  have e1 : ∑ i, (lam i + ∑ k, P k i * (β k * u k) - β i * u i) * Real.log (u i) =
      ∑ i, ((lam i + eps * w i) + ∑ k, P k i * (β k * u k) - β i * u i) * Real.log (u i) -
        eps * ∑ i, w i * Real.log (u i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have e2 : ∑ i, (lam i + eps * w i) * PFB 1 (u i) =
      ∑ i, lam i * PFB 1 (u i) + eps * ∑ i, w i * (u i - 1 - Real.log (u i)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by simp only [PFB, Real.log_one]; ring)
  have e3 : ∑ i, w i * (u i - 1 - Real.log (u i)) + ∑ i, w i * Real.log (u i) =
      -∑ i, w i * (1 - u i) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [e1, hid, e2]
  linear_combination (-eps) * e3

/-- A positive supersolution for a transient nonnegative matrix (truncated Neumann series). -/
lemma PF_supersol {I : ℕ} (Q : Matrix (Fin I) (Fin I) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (htr : ∀ i j, Tendsto (fun n => (Q ^ n) i j) atTop (𝓝 0))
    (b : Fin I → ℝ) (hb : ∀ i, 0 < b i) :
    ∃ v : Fin I → ℝ, (∀ i, b i ≤ v i) ∧ ∀ i, ∑ j, Q i j * v j + b i / 2 ≤ v i := by
  set w : ℕ → Fin I → ℝ := fun n i => ∑ k ∈ Finset.range n, ∑ j, (Q ^ k) i j * b j with hw
  have hpn := PF_pow_nonneg Q hQ
  have h1 : ∀ k i, ∑ j, (Q ^ (k + 1)) i j * b j = ∑ l, Q i l * ∑ j, (Q ^ k) l j * b j := by
    intro k i
    simp only [pow_succ', Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hrec : ∀ n i, ∑ l, Q i l * w n l + b i = w (n + 1) i := by
    intro n i
    simp only [hw]
    rw [Finset.sum_range_succ']
    simp only [h1, pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_comm (s := Finset.range n)]
    congr 1
    exact Finset.sum_congr rfl (fun l _ => by rw [Finset.mul_sum])
  have hstep : ∀ n i, w (n + 1) i = w n i + ∑ j, (Q ^ n) i j * b j := by
    intro n i; simp only [hw]; rw [Finset.sum_range_succ]
  have hlim : ∀ i, Tendsto (fun n => ∑ j, (Q ^ n) i j * b j) atTop (𝓝 0) := by
    intro i
    have := tendsto_finsetSum (Finset.univ : Finset (Fin I))
      (fun j _ => (htr i j).mul_const (b j))
    simpa using this
  have hev : ∀ᶠ n in atTop, ∀ i, ∑ j, (Q ^ n) i j * b j < b i / 2 :=
    Filter.eventually_all.mpr (fun i => (hlim i).eventually (gt_mem_nhds (by linarith [hb i])))
  obtain ⟨n, hn, hn1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  refine ⟨w n, fun i => ?_, fun i => ?_⟩
  · have hmem : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr (by omega)
    have := Finset.single_le_sum (f := fun k => ∑ j, (Q ^ k) i j * b j)
      (fun k _ => Finset.sum_nonneg (fun j _ => mul_nonneg (hpn k i j) (hb j).le)) hmem
    simp only [pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at this
    exact this
  · have := hrec n i
    rw [hstep n i] at this
    linarith [hn i]

/-- Regime A: if the zero-rate work is small, the load condition forces a fast positive-rate class. -/
lemma PF_pos_witness {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (alpha : Fin I → ℝ) (hα0 : ∀ i, 0 ≤ alpha i)
    (a : Fin L → ℝ) (haA : a ∈ dat.TildeAllocSet) (δ : ℝ)
    (hδa : ∀ ℓ, (1 + δ) * groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ ≤ a ℓ)
    (η κ : ℝ) (hη : 0 < η) (hκ : 0 ≤ κ) (hηκ : (1 + κ) * (1 + η) ≤ 1 + δ)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t)
    (hsmall : ∑ i, (if alpha i = 0 then Zh t i else 0) ≤
      κ * ∑ i, (if alpha i = 0 then 0 else Zh t i))
    (hne : ∃ i, 0 < alpha i ∧ 0 < Zh t i) :
    ∃ i, 0 < alpha i ∧ 0 < Zh t i ∧ (1 + η) * alpha i ≤ deriv (fun s => Dh s i) t := by
  by_contra hno
  push Not at hno
  set Y := groupAggregate dat.grp (Zh t) with hYdef
  have hZnn : ∀ i, 0 ≤ Zh t i := fun i => hsol.2.1 t ht.le i
  have hYnn : ∀ ℓ, 0 ≤ Y ℓ := fun ℓ => Finset.sum_nonneg (fun i _ => hZnn i)
  obtain ⟨x, hxm, hpx⟩ := PF_psi_eq dat.TildeAllocSet hdom Y hYnn
  have hxpos : ∀ ℓ, 0 < Y ℓ → 0 < x ℓ := fun ℓ hℓ => by
    rw [← hpx ℓ hℓ]; exact PF_psi_pos dat hdom Ah Dh Th Zh hsol t ht ℓ hℓ
  set c : Fin L → ℝ := fun ℓ => Y ℓ / x ℓ with hc
  have hc_nn : ∀ ℓ, 0 ≤ c ℓ := fun ℓ => by
    rcases eq_or_lt_of_le (hYnn ℓ) with h0 | hpos
    · simp [hc, ← h0]
    · exact div_nonneg hpos.le (hxpos ℓ hpos).le
  -- per positive-rate class: Z_i ≤ (1+η) α_i m_i c_ℓ, strictly if Z_i > 0
  have hcls : ∀ i, (if alpha i = 0 then 0 else Zh t i) ≤
      (1 + η) * (alpha i * dat.m i * c (dat.grp i)) := by
    intro i
    have hrhs : 0 ≤ (1 + η) * (alpha i * dat.m i * c (dat.grp i)) :=
      mul_nonneg (by linarith) (mul_nonneg (mul_nonneg (hα0 i) (dat.hm i).le) (hc_nn _))
    by_cases ha : alpha i = 0
    · rw [if_pos ha]; exact hrhs
    · rw [if_neg ha]
      rcases eq_or_lt_of_le (hZnn i) with h0 | hZp
      · rw [← h0]; exact hrhs
      · exact (le_of_lt (by
          have hap : 0 < alpha i := lt_of_le_of_ne (hα0 i) (Ne.symm ha)
          have hD := (PF_Ddot_formula dat Ah Dh Th Zh hsol t ht i hZp).deriv
          have hlt := hno i hap hZp
          rw [hD] at hlt
          have hYp : 0 < Y (dat.grp i) := lt_of_lt_of_le hZp (PF_Z_le_Y dat.grp (Zh t) hZnn i)
          rw [hpx _ hYp] at hlt
          have hxp := hxpos _ hYp
          have hm := dat.hm i
          rw [div_div, div_lt_iff₀ (by positivity)] at hlt
          have key : Zh t i * x (dat.grp i) < (1 + η) * alpha i * dat.m i * Y (dat.grp i) := by
            nlinarith [hlt]
          rw [show (1 + η) * (alpha i * dat.m i * c (dat.grp i)) =
            ((1 + η) * alpha i * dat.m i * Y (dat.grp i)) / x (dat.grp i) by simp only [hc]; ring]
          rw [lt_div_iff₀ hxp]
          linarith : Zh t i < (1 + η) * (alpha i * dat.m i * c (dat.grp i))))
  have hstrict : ∑ i, (if alpha i = 0 then 0 else Zh t i) <
      ∑ i, (1 + η) * (alpha i * dat.m i * c (dat.grp i)) := by
    obtain ⟨i1, hai1, hZi1⟩ := hne
    refine Finset.sum_lt_sum (fun i _ => hcls i) ⟨i1, Finset.mem_univ _, ?_⟩
    have hD := (PF_Ddot_formula dat Ah Dh Th Zh hsol t ht i1 hZi1).deriv
    have hlt := hno i1 hai1 hZi1
    rw [hD] at hlt
    have hYp : 0 < Y (dat.grp i1) := lt_of_lt_of_le hZi1 (PF_Z_le_Y dat.grp (Zh t) hZnn i1)
    rw [hpx _ hYp] at hlt
    have hxp := hxpos _ hYp
    have hm := dat.hm i1
    rw [if_neg hai1.ne']
    rw [div_div, div_lt_iff₀ (by positivity)] at hlt
    have key : Zh t i1 * x (dat.grp i1) < (1 + η) * alpha i1 * dat.m i1 * Y (dat.grp i1) := by
      nlinarith [hlt]
    rw [show (1 + η) * (alpha i1 * dat.m i1 * c (dat.grp i1)) =
      ((1 + η) * alpha i1 * dat.m i1 * Y (dat.grp i1)) / x (dat.grp i1) by simp only [hc]; ring]
    rw [lt_div_iff₀ hxp]
    linarith
  have hfib : ∑ i, alpha i * dat.m i * c (dat.grp i) =
      ∑ ℓ, groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ * c ℓ :=
    PF_fiber_mul dat.grp (fun i => alpha i * dat.m i) c
  set X := ∑ ℓ, groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ * c ℓ with hX
  have hXnn : 0 ≤ X := Finset.sum_nonneg (fun ℓ _ => mul_nonneg
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hα0 i) (dat.hm i).le)) (hc_nn ℓ))
  have hP1 : ∑ i, (if alpha i = 0 then 0 else Zh t i) < (1 + η) * X := by
    rw [← Finset.mul_sum, hfib] at hstrict; exact hstrict
  -- VI with the load point
  have hvi := PF_vi dat.TildeAllocSet hdom Y x hYnn hxm a haA
  have hvi' : ∑ ℓ, c ℓ * a ℓ ≤ ∑ ℓ, Y ℓ := by
    have : ∀ ℓ, Y ℓ * ((a ℓ - x ℓ) / x ℓ) = c ℓ * a ℓ - Y ℓ := by
      intro ℓ
      rcases eq_or_lt_of_le (hYnn ℓ) with h0 | hpos
      · simp [hc, ← h0]
      · have := (hxpos ℓ hpos).ne'
        simp only [hc]
        field_simp
    simp only [this] at hvi
    rw [Finset.sum_sub_distrib] at hvi
    linarith
  have hsumY : ∑ ℓ, Y ℓ = ∑ i, Zh t i := (PF_sum_fiber dat.grp (Zh t)).symm
  have hsplit : ∑ i, Zh t i = ∑ i, (if alpha i = 0 then Zh t i else 0) +
      ∑ i, (if alpha i = 0 then 0 else Zh t i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> ring)
  have hδX : (1 + δ) * X ≤ ∑ ℓ, c ℓ * a ℓ := by
    rw [hX, Finset.mul_sum]
    exact Finset.sum_le_sum (fun ℓ _ => by
      have := mul_le_mul_of_nonneg_right (hδa ℓ) (hc_nn ℓ)
      linarith)
  set ZP := ∑ i, (if alpha i = 0 then 0 else Zh t i) with hZP
  have h1 : (1 + δ) * X ≤ (1 + κ) * ZP := by linarith
  have h2 : (1 + κ) * ZP < (1 + κ) * ((1 + η) * X) :=
    mul_lt_mul_of_pos_left hP1 (by linarith)
  have h3 : (1 + κ) * ((1 + η) * X) ≤ (1 + δ) * X := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hηκ hXnn
  linarith

/-- The zero-rate work `W = Σ_{α_i=0} v_i Z_i` decreases at rate `≥ ½ Σ_{α_k=0} m_k Ḋ_k`. -/
lemma PF_W_drift {I L : ℕ} (dat : PFUnitaryNetworkData I L) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP : ∀ i j, 0 ≤ dat.P i j) (alpha : Fin I → ℝ) (halpha : IsTotalArrivalRates dat alpha)
    (hα0 : ∀ i, 0 ≤ alpha i) (v : Fin I → ℝ) (hvnn : ∀ i, 0 ≤ v i)
    (hv : ∀ i, ∑ j, dat.P i j * v j + dat.m i / 2 ≤ v i)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t) (hreg : RegularPoint Ah Dh Th Zh t) :
    ∑ i, (if alpha i = 0 then v i else 0) * deriv (fun s => Zh s i) t ≤
      -(1 / 2) * ∑ i, (if alpha i = 0 then dat.m i else 0) * deriv (fun s => Dh s i) t := by
  have hfacts := PF_regular_facts dat Ah Dh Th Zh hsol t ht hreg
  set Dd : Fin I → ℝ := fun k => deriv (fun s => Dh s k) t with hDd
  have hDnn : ∀ k, 0 ≤ Dd k := fun k => (hfacts k).2.1
  have hfix : ∀ i, alpha i = dat.lam i + ∑ k, dat.P k i * alpha k := fun i => congrFun halpha i
  have hlam0 : ∀ i, alpha i = 0 → dat.lam i = 0 := by
    intro i hi
    have hs : 0 ≤ ∑ k, dat.P k i * alpha k :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (hP k i) (hα0 k))
    linarith [hfix i, hlam i]
  have hclosed : ∀ k i, 0 < alpha k → alpha i = 0 → dat.P k i = 0 := fun k i hk hi =>
    pf_zero_rate_closed dat hlam hP alpha halpha hα0 k i hk hi
  set vN : Fin I → ℝ := fun i => if alpha i = 0 then v i else 0 with hvN
  set mN : Fin I → ℝ := fun i => if alpha i = 0 then dat.m i else 0 with hmN
  have hZd : ∀ i, vN i * deriv (fun s => Zh s i) t =
      vN i * (∑ k, dat.P k i * Dd k) - vN i * Dd i := by
    intro i
    rw [(hfacts i).1]
    by_cases hi : alpha i = 0
    · simp only [hvN, if_pos hi, hlam0 i hi]; ring
    · simp only [hvN, if_neg hi]; ring
  have hk : ∀ k, Dd k * ∑ i, dat.P k i * vN i ≤ Dd k * (vN k - mN k / 2) := by
    intro k
    by_cases hka : alpha k = 0
    · have h1 : ∑ i, dat.P k i * vN i ≤ ∑ i, dat.P k i * v i := by
        refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_ (hP k i))
        simp only [hvN]; split_ifs
        · exact le_rfl
        · exact hvnn i
      have h2 := hv k
      simp only [hvN, hmN, if_pos hka]
      exact mul_le_mul_of_nonneg_left (by linarith) (hDnn k)
    · have hk0 : 0 < alpha k := lt_of_le_of_ne (hα0 k) (Ne.symm hka)
      have h1 : ∑ i, dat.P k i * vN i = 0 := Finset.sum_eq_zero (fun i _ => by
        simp only [hvN]; split_ifs with hi
        · rw [hclosed k i hk0 hi, zero_mul]
        · rw [mul_zero])
      rw [h1]; simp [hvN, hmN, hka]
  calc ∑ i, vN i * deriv (fun s => Zh s i) t
      = ∑ k, Dd k * ∑ i, dat.P k i * vN i - ∑ i, vN i * Dd i := by
        rw [Finset.sum_congr rfl (fun i _ => hZd i), Finset.sum_sub_distrib]
        congr 1
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => by ring))
    _ ≤ ∑ k, Dd k * (vN k - mN k / 2) - ∑ i, vN i * Dd i := by
        linarith [Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hk k)]
    _ = -(1 / 2) * ∑ i, mN i * Dd i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)

/-- K5 for arbitrary positive weights `β` under the load condition for `β`. -/
theorem PF_K5_gen {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (β : Fin I → ℝ) (hβ : ∀ i, 0 < β i)
    (a : Fin L → ℝ) (haA : a ∈ dat.TildeAllocSet)
    (hlt : ∀ ℓ, groupAggregate dat.grp (fun i => β i * dat.m i) ℓ < a ℓ)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ)
    (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) (t : ℝ) (ht : 0 < t) :
    0 ≤ phiF β Dh Zh t ∧ (Zh t ≠ 0 → 0 < phiF β Dh Zh t) := by
  set Y := groupAggregate dat.grp (Zh t) with hYdef
  have hZnn : ∀ i, 0 ≤ Zh t i := fun i => hsol.2.1 t ht.le i
  have hYnn : ∀ ℓ, 0 ≤ Y ℓ := fun ℓ => Finset.sum_nonneg (fun i _ => hZnn i)
  obtain ⟨x, hxm, hpx⟩ := PF_psi_eq dat.TildeAllocSet hdom Y hYnn
  have hxpos : ∀ ℓ, 0 < Y ℓ → 0 < x ℓ := fun ℓ hℓ => by
    rw [← hpx ℓ hℓ]; exact PF_psi_pos dat hdom Ah Dh Th Zh hsol t ht ℓ hℓ
  set c : Fin L → ℝ := fun ℓ => Y ℓ / x ℓ with hc
  have hc_nn : ∀ ℓ, 0 ≤ c ℓ := fun ℓ => by
    rcases eq_or_lt_of_le (hYnn ℓ) with h0 | hpos
    · simp [hc, ← h0]
    · exact div_nonneg hpos.le (hxpos ℓ hpos).le
  have hYge : ∀ i, Zh t i ≤ Y (dat.grp i) := fun i => by
    rw [hYdef]; unfold groupAggregate
    exact Finset.single_le_sum (f := fun j => Zh t j) (fun j _ => hZnn j)
      (by simp : i ∈ Finset.univ.filter (fun j => dat.grp j = dat.grp i))
  -- termwise lower bound
  have hA : ∀ i, Zh t i - dat.m i * β i * c (dat.grp i) ≤
      Zh t i * Real.log (derivWithin (fun s => Dh s i) (Set.Ici t) t / β i) := by
    intro i
    have hmi := dat.hm i
    have hai := hβ i
    by_cases hZ : Zh t i = 0
    · rw [hZ]; simp only [zero_mul, zero_sub]
      have := mul_nonneg (mul_pos hmi hai).le (hc_nn (dat.grp i))
      linarith
    · have hZpos : 0 < Zh t i := lt_of_le_of_ne (hZnn i) (Ne.symm hZ)
      have hYpos : 0 < Y (dat.grp i) := lt_of_lt_of_le hZpos (hYge i)
      have hxp := hxpos _ hYpos
      have hD := PF_Ddot_formula dat Ah Dh Th Zh hsol t ht i hZpos
      rw [hD.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici t)]
      rw [hpx _ hYpos]
      set u : ℝ := x (dat.grp i) * Zh t i / Y (dat.grp i) / dat.m i / β i with hu
      have hupos : 0 < u := by positivity
      have hlog := Real.one_sub_inv_le_log_of_pos hupos
      have hkey : Zh t i * u⁻¹ = dat.m i * β i * c (dat.grp i) := by
        simp only [hu, hc]
        field_simp
      calc Zh t i - dat.m i * β i * c (dat.grp i) = Zh t i * (1 - u⁻¹) := by
            rw [mul_sub, mul_one, hkey]
        _ ≤ Zh t i * Real.log u := mul_le_mul_of_nonneg_left hlog hZpos.le
  have hphi : ∑ i, Zh t i - ∑ i, dat.m i * β i * c (dat.grp i) ≤ phiF β Dh Zh t := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun i _ => hA i)
  -- group sums
  have hsumY : ∑ ℓ, Y ℓ = ∑ i, Zh t i := (PF_sum_fiber dat.grp (Zh t)).symm
  have hsumc : ∑ i, dat.m i * β i * c (dat.grp i) =
      ∑ ℓ, c ℓ * groupAggregate dat.grp (fun i => β i * dat.m i) ℓ := by
    rw [PF_sum_fiber dat.grp (fun i => dat.m i * β i * c (dat.grp i))]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    unfold groupAggregate
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [(Finset.mem_filter.mp hi).2]; ring
  have hvi := PF_vi dat.TildeAllocSet hdom Y x hYnn hxm a haA
  have hvi' : ∑ ℓ, c ℓ * a ℓ ≤ ∑ ℓ, Y ℓ := by
    have : ∀ ℓ, Y ℓ * ((a ℓ - x ℓ) / x ℓ) = c ℓ * a ℓ - Y ℓ := by
      intro ℓ
      rcases eq_or_lt_of_le (hYnn ℓ) with h0 | hpos
      · simp [hc, ← h0]
      · have := (hxpos ℓ hpos).ne'
        simp only [hc]
        field_simp
    simp only [this] at hvi
    rw [Finset.sum_sub_distrib] at hvi
    linarith
  have hcr : ∑ ℓ, c ℓ * groupAggregate dat.grp (fun i => β i * dat.m i) ℓ ≤ ∑ ℓ, c ℓ * a ℓ :=
    Finset.sum_le_sum (fun ℓ _ => mul_le_mul_of_nonneg_left (hlt ℓ).le (hc_nn ℓ))
  refine ⟨by linarith, fun hne => ?_⟩
  -- strictness
  obtain ⟨i, hi⟩ : ∃ i, Zh t i ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hne (funext hno)
  have hZpos : 0 < Zh t i := lt_of_le_of_ne (hZnn i) (Ne.symm hi)
  have hYpos : 0 < Y (dat.grp i) := lt_of_lt_of_le hZpos (hYge i)
  have hcpos : 0 < c (dat.grp i) := div_pos hYpos (hxpos _ hYpos)
  have hstrict : ∑ ℓ, c ℓ * groupAggregate dat.grp (fun i => β i * dat.m i) ℓ <
      ∑ ℓ, c ℓ * a ℓ :=
    Finset.sum_lt_sum (fun ℓ _ => mul_le_mul_of_nonneg_left (hlt ℓ).le (hc_nn ℓ))
      ⟨dat.grp i, Finset.mem_univ _, mul_lt_mul_of_pos_left (hlt _) hcpos⟩
  linarith

lemma PF_Z_inc {I L : ℕ} (dat : PFUnitaryNetworkData I L) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP : ∀ i j, 0 ≤ dat.P i j)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) :
    ∃ KZ : ℝ, 0 ≤ KZ ∧ ∀ u z, 0 ≤ u → u ≤ z → ∀ i, Zh z i - Zh u i ≤ KZ * (z - u) := by
  have hZeq := hsol.1
  have hA := hsol.2.2.1
  have hDT := hsol.2.2.2.1
  have hmono := hsol.2.2.2.2.1.2.1
  obtain ⟨Kc, hK⟩ := hsol.2.2.2.2.1.2.2
  set K : Fin I → ℝ := fun i => dat.lam i + ∑ k, dat.P k i * (|Kc| / dat.m k) with hKdef
  have hKnn : ∀ i, 0 ≤ K i := fun i => add_nonneg (hlam i) (Finset.sum_nonneg (fun k _ =>
    mul_nonneg (hP k i) (div_nonneg (abs_nonneg _) (dat.hm k).le)))
  refine ⟨∑ i, K i, Finset.sum_nonneg (fun i _ => hKnn i), fun u z hu huz i => ?_⟩
  have hDinc : ∀ k, 0 ≤ Dh z k - Dh u k ∧ Dh z k - Dh u k ≤ |Kc| / dat.m k * (z - u) := by
    intro k
    have hz0 : 0 ≤ z := le_trans hu huz
    rw [hDT z hz0 k, hDT u hu k, ← sub_div]
    have hmk := dat.hm k
    have hT1 : 0 ≤ Th z k - Th u k := by linarith [hmono huz k]
    have hT2 : Th z k - Th u k ≤ |Kc| * (z - u) := by
      have := hK u z hu huz k
      have h3 := mul_le_mul_of_nonneg_right (le_abs_self Kc) (by linarith : (0:ℝ) ≤ z - u)
      linarith [le_abs_self (Th z k - Th u k)]
    refine ⟨div_nonneg hT1 hmk.le, ?_⟩
    rw [div_le_iff₀ hmk]
    have : |Kc| / dat.m k * (z - u) * dat.m k = |Kc| * (z - u) := by field_simp
    linarith
  have hz0 : 0 ≤ z := le_trans hu huz
  have hdiff : Zh z i - Zh u i = dat.lam i * (z - u) +
      ∑ k, dat.P k i * (Dh z k - Dh u k) - (Dh z i - Dh u i) := by
    rw [congrFun (hZeq z hz0) i, congrFun (hZeq u hu) i, hA z hz0 i, hA u hu i]
    have : ∑ k, dat.P k i * (Dh z k - Dh u k) =
        ∑ k, dat.P k i * Dh z k - ∑ k, dat.P k i * Dh u k := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [this]; ring
  have hS1 : ∑ k, dat.P k i * (Dh z k - Dh u k) ≤ ∑ k, dat.P k i * (|Kc| / dat.m k) * (z - u) :=
    Finset.sum_le_sum (fun k _ => by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hDinc k).2 (hP k i))
  have hS2 : ∑ k, dat.P k i * (|Kc| / dat.m k) * (z - u) =
      (∑ k, dat.P k i * (|Kc| / dat.m k)) * (z - u) := by rw [Finset.sum_mul]
  have hDi := (hDinc i).1
  have hKi : K i ≤ ∑ j, K j :=
    Finset.single_le_sum (f := K) (fun j _ => hKnn j) (Finset.mem_univ i)
  have hzu : 0 ≤ z - u := by linarith
  have hKz : K i * (z - u) ≤ (∑ j, K j) * (z - u) := mul_le_mul_of_nonneg_right hKi hzu
  have : Zh z i - Zh u i ≤ K i * (z - u) := by
    rw [hdiff]; simp only [hKdef]; nlinarith
  linarith

/-- Drain of the zero-rate classes: `a_min · Σ_{α=0} Z ≤ (Σ Z) · Σ_{α=0} m Ḋ`. -/
lemma PF_drain_lb {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (alpha : Fin I → ℝ)
    (a : Fin L → ℝ) (haA : a ∈ dat.TildeAllocSet) (amin : ℝ) (hamin_le : ∀ ℓ, amin ≤ a ℓ)
    (hamin : 0 ≤ amin)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t) (hreg : RegularPoint Ah Dh Th Zh t) :
    amin * ∑ i, (if alpha i = 0 then Zh t i else 0) ≤
      (∑ i, Zh t i) * ∑ i, (if alpha i = 0 then dat.m i else 0) * deriv (fun s => Dh s i) t := by
  have hfacts := PF_regular_facts dat Ah Dh Th Zh hsol t ht hreg
  set Y := groupAggregate dat.grp (Zh t) with hYdef
  have hZnn : ∀ i, 0 ≤ Zh t i := fun i => hsol.2.1 t ht.le i
  have hYnn : ∀ ℓ, 0 ≤ Y ℓ := fun ℓ => Finset.sum_nonneg (fun i _ => hZnn i)
  obtain ⟨x, hxm, hpx⟩ := PF_psi_eq dat.TildeAllocSet hdom Y hYnn
  have hxpos : ∀ ℓ, 0 < Y ℓ → 0 < x ℓ := fun ℓ hℓ => by
    rw [← hpx ℓ hℓ]; exact PF_psi_pos dat hdom Ah Dh Th Zh hsol t ht ℓ hℓ
  set c : Fin L → ℝ := fun ℓ => Y ℓ / x ℓ with hc
  have hc_nn : ∀ ℓ, 0 ≤ c ℓ := fun ℓ => by
    rcases eq_or_lt_of_le (hYnn ℓ) with h0 | hpos
    · simp [hc, ← h0]
    · exact div_nonneg hpos.le (hxpos ℓ hpos).le
  have hvi := PF_vi dat.TildeAllocSet hdom Y x hYnn hxm a haA
  have hvi' : ∑ ℓ, c ℓ * a ℓ ≤ ∑ ℓ, Y ℓ := by
    have : ∀ ℓ, Y ℓ * ((a ℓ - x ℓ) / x ℓ) = c ℓ * a ℓ - Y ℓ := by
      intro ℓ
      rcases eq_or_lt_of_le (hYnn ℓ) with h0 | hpos
      · simp [hc, ← h0]
      · have := (hxpos ℓ hpos).ne'
        simp only [hc]
        field_simp
    simp only [this] at hvi
    rw [Finset.sum_sub_distrib] at hvi
    linarith
  have hsumY : ∑ ℓ, Y ℓ = ∑ i, Zh t i := (PF_sum_fiber dat.grp (Zh t)).symm
  have ha_nn : ∀ ℓ, 0 ≤ a ℓ := fun ℓ => le_trans hamin (hamin_le ℓ)
  have hca : ∀ ℓ, c ℓ * a ℓ ≤ ∑ i, Zh t i := by
    intro ℓ
    have := Finset.single_le_sum (f := fun k => c k * a k)
      (fun k _ => mul_nonneg (hc_nn k) (ha_nn k)) (Finset.mem_univ ℓ)
    linarith
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hDnn := (hfacts i).2.1
  have hSnn : 0 ≤ ∑ j, Zh t j := Finset.sum_nonneg (fun j _ => hZnn j)
  by_cases ha : alpha i = 0
  · rw [if_pos ha, if_pos ha]
    rcases eq_or_lt_of_le (hZnn i) with h0 | hZp
    · rw [← h0, mul_zero]
      exact mul_nonneg hSnn (mul_nonneg (dat.hm i).le hDnn)
    · have hD := (PF_Ddot_formula dat Ah Dh Th Zh hsol t ht i hZp).deriv
      rw [hD]
      have hYp : 0 < Y (dat.grp i) := lt_of_lt_of_le hZp (PF_Z_le_Y dat.grp (Zh t) hZnn i)
      rw [hpx _ hYp]
      have hxp := hxpos _ hYp
      have hm := dat.hm i
      have hcal := hca (dat.grp i)
      simp only [hc] at hcal
      rw [div_mul_eq_mul_div, div_le_iff₀ hxp] at hcal
      have heq : dat.m i * (x (dat.grp i) * Zh t i / Y (dat.grp i) / dat.m i) =
          x (dat.grp i) * Zh t i / Y (dat.grp i) := by field_simp
      rw [heq]
      have h1 : amin * Zh t i ≤ a (dat.grp i) * Zh t i :=
        mul_le_mul_of_nonneg_right (hamin_le _) hZp.le
      have h2 : a (dat.grp i) * Zh t i ≤ (∑ j, Zh t j) * (x (dat.grp i) * Zh t i / Y (dat.grp i)) := by
        rw [mul_div_assoc', le_div_iff₀ hYp]
        nlinarith
      linarith
  · rw [if_neg ha, if_neg ha]; simp

/-- C2 drift: the perturbed entropy plus `K ×` the zero-rate work has drift `≤ -c_A/2`. -/
lemma PF_C2_drift {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP : ∀ i j, 0 ≤ dat.P i j) (hrow : ∀ i, ∑ j, dat.P i j ≤ 1)
    (alpha : Fin I → ℝ) (halpha : IsTotalArrivalRates dat alpha) (hα0 : ∀ i, 0 ≤ alpha i)
    (a : Fin L → ℝ) (haA : a ∈ dat.TildeAllocSet) (δ : ℝ)
    (hδa : ∀ ℓ, (1 + δ) * groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ ≤ a ℓ)
    (η κ : ℝ) (hη : 0 < η) (hη2 : η ≤ 2) (hκ : 0 < κ) (hηκ : (1 + κ) * (1 + η) ≤ 1 + δ)
    (amin : ℝ) (hamin : 0 < amin) (hamin_le : ∀ ℓ, amin ≤ a ℓ)
    (N : ℕ) (hN : ∀ i, 0 < alpha i → ∃ j < N, ∃ k, 0 < dat.lam k ∧ 0 < (dat.P ^ j) k i)
    (c : ℝ) (hc : 0 < c) (hcl : ∀ k, 0 < dat.lam k → c ≤ dat.lam k)
    (hcP : ∀ k i, 0 < dat.P k i * alpha k → c ≤ dat.P k i * alpha k)
    (β w : Fin I → ℝ) (eps : ℝ) (heps : 0 ≤ eps) (hw0 : ∀ i, 0 ≤ w i)
    (hβfix : ∀ i, β i = (dat.lam i + eps * w i) + ∑ k, dat.P k i * β k)
    (hαβ : ∀ i, alpha i ≤ β i) (hβpos : ∀ i, 0 < β i)
    (hβη : ∀ i, 0 < alpha i → (1 + η / 2) * β i ≤ (1 + η) * alpha i)
    (hE1 : eps * ∑ i, w i ≤ c * (η / 2 / (3 * N)) ^ 2 / 2)
    (v : Fin I → ℝ) (hvnn : ∀ i, 0 ≤ v i) (hv : ∀ i, ∑ j, dat.P i j * v j + dat.m i / 2 ≤ v i)
    (K : ℝ) (hK0 : 0 ≤ K)
    (hKB : eps * ∑ i, w i - K * (amin * κ / (2 * (1 + κ))) ≤ -(c * (η / 2 / (3 * N)) ^ 2 / 2))
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t) (hreg : RegularPoint Ah Dh Th Zh t) (hZ : Zh t ≠ 0) :
    ∑ i, deriv (fun s => Zh s i) t * Real.log (deriv (fun s => Dh s i) t / β i) +
      K * ∑ i, (if alpha i = 0 then v i else 0) * deriv (fun s => Zh s i) t ≤
      -(c * (η / 2 / (3 * N)) ^ 2 / 2) := by
  have hfacts := PF_regular_facts dat Ah Dh Th Zh hsol t ht hreg
  have hfix : ∀ i, alpha i = dat.lam i + ∑ k, dat.P k i * alpha k := fun i => congrFun halpha i
  set u : Fin I → ℝ := fun i => deriv (fun s => Dh s i) t / β i with hudef
  have hβu : ∀ k, β k * u k = deriv (fun s => Dh s k) t := fun k => by
    simp only [hudef]; field_simp [(hβpos k).ne']
  have hzdot : ∀ i, dat.lam i + ∑ k, dat.P k i * (β k * u k) - β i * u i =
      deriv (fun s => Zh s i) t := by
    intro i; simp only [hβu]; rw [(hfacts i).1]
  have hu : ∀ i, 0 ≤ u i := fun i => div_nonneg (hfacts i).2.1 (hβpos i).le
  have hDpos : ∀ i, 0 < Zh t i → 0 < deriv (fun s => Dh s i) t := by
    intro i hZp
    have hD := (PF_Ddot_formula dat Ah Dh Th Zh hsol t ht i hZp).deriv
    rw [hD]
    have hZnn' : ∀ j, 0 ≤ Zh t j := fun j => hsol.2.1 t ht.le j
    have hYp := lt_of_lt_of_le hZp (PF_Z_le_Y dat.grp (Zh t) hZnn' i)
    have hps := PF_psi_pos dat hdom Ah Dh Th Zh hsol t ht (dat.grp i) hYp
    have := dat.hm i
    positivity
  have hzero : ∀ i, u i = 0 → dat.lam i = 0 ∧ ∀ k, dat.P k i * (β k * u k) = 0 := by
    intro i hi
    have hD0 : deriv (fun s => Dh s i) t = 0 := by
      have := hβu i; rw [hi, mul_zero] at this; exact this.symm
    have hZ0 : Zh t i = 0 := by
      by_contra hne
      have := hDpos i (lt_of_le_of_ne (hsol.2.1 t ht.le i) (Ne.symm hne))
      linarith
    have hzd := (hfacts i).2.2 hZ0
    rw [← hzdot i, hi, mul_zero, sub_zero] at hzd
    have hs : 0 ≤ ∑ k, dat.P k i * (β k * u k) :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (hP k i) (mul_nonneg (hβpos k).le (hu k)))
    have := (add_eq_zero_iff_of_nonneg (hlam i) hs).mp hzd
    refine ⟨this.1, fun k => ?_⟩
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      mul_nonneg (hP k i) (mul_nonneg (hβpos k).le (hu k)))).mp this.2 k (Finset.mem_univ k)
  have hdr := PF_drift_eps dat.lam dat.P β w u eps hβfix
  have hT1 : ∑ i, deriv (fun s => Zh s i) t * Real.log (deriv (fun s => Dh s i) t / β i) =
      ∑ i, (dat.lam i + ∑ k, dat.P k i * (β k * u k) - β i * u i) * Real.log (u i) :=
    Finset.sum_congr rfl (fun i _ => by rw [hzdot i])
  rw [hT1, hdr]
  have herr : eps * ∑ i, w i * (1 - u i) ≤ eps * ∑ i, w i :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => by nlinarith [hw0 i, hu i])) heps
  obtain ⟨i1, hi1⟩ : ∃ i, Zh t i ≠ 0 := by
    by_contra hno; push Not at hno; exact hZ (funext hno)
  have hpen := PF_pen_lb dat.lam dat.P alpha β hlam hP hrow hα0 hαβ hfix c hc hcl hcP u hu hzero
    N (η / 2) (by positivity) (by linarith) i1
  have hW := PF_W_drift dat hlam hP alpha halpha hα0 v hvnn hv Ah Dh Th Zh hsol t ht hreg
  set S := ∑ i, (if alpha i = 0 then dat.m i else 0) * deriv (fun s => Dh s i) t with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun i _ => by
    split_ifs
    · exact mul_nonneg (dat.hm i).le (hfacts i).2.1
    · simp)
  set ZN := ∑ i, (if alpha i = 0 then Zh t i else 0) with hZN
  set ZP := ∑ i, (if alpha i = 0 then 0 else Zh t i) with hZP
  have hZnn : ∀ i, 0 ≤ Zh t i := fun i => hsol.2.1 t ht.le i
  by_cases hA : ZN ≤ κ * ZP
  · have hne : ∃ i, 0 < alpha i ∧ 0 < Zh t i := by
      by_contra hno
      push Not at hno
      have hZP0 : ZP = 0 := Finset.sum_eq_zero (fun i _ => by
        split_ifs with h
        · rfl
        · exact le_antisymm (hno i (lt_of_le_of_ne (hα0 i) (Ne.symm h))) (hZnn i))
      rw [hZP0, mul_zero] at hA
      apply hZ
      funext i
      by_cases h : alpha i = 0
      · have := Finset.single_le_sum (f := fun j => if alpha j = 0 then Zh t j else 0)
          (fun j _ => by split_ifs; exact hZnn j; exact le_rfl) (Finset.mem_univ i)
        simp only [if_pos h] at this
        show Zh t i = 0
        exact le_antisymm (by linarith) (hZnn i)
      · exact le_antisymm (hno i (lt_of_le_of_ne (hα0 i) (Ne.symm h))) (hZnn i)
    obtain ⟨i0, hai0, -, hDi0⟩ := PF_pos_witness dat hdom alpha hα0 a haA δ hδa η κ hη hκ.le hηκ
      Ah Dh Th Zh hsol t ht hA hne
    have hui0 : 1 + η / 2 ≤ u i0 := by
      simp only [hudef]; rw [le_div_iff₀ (hβpos i0)]; linarith [hβη i0 hai0]
    have hpen0 := (PF_pen_lb dat.lam dat.P alpha β hlam hP hrow hα0 hαβ hfix c hc hcl hcP u hu
      hzero N (η / 2) (by positivity) (by linarith) i0).2 hui0 (hN i0 hai0)
    have hWle : K * ∑ i, (if alpha i = 0 then v i else 0) * deriv (fun s => Zh s i) t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hK0 (by linarith)
    linarith
  · push Not at hA
    have hdrain := PF_drain_lb dat hdom alpha a haA amin hamin_le hamin.le Ah Dh Th Zh hsol t ht hreg
    have hsumZ : ∑ i, Zh t i = ZN + ZP := by
      rw [hZN, hZP, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> ring)
    rw [hsumZ] at hdrain
    have hZPnn : 0 ≤ ZP := Finset.sum_nonneg (fun i _ => by split_ifs; exact le_rfl; exact hZnn i)
    have hZNpos : 0 < ZN := lt_of_le_of_lt (mul_nonneg hκ.le hZPnn) hA
    have h1 : κ * (amin * ZN) ≤ κ * ((ZN + ZP) * S) := mul_le_mul_of_nonneg_left hdrain hκ.le
    have h2 : κ * ZP * S ≤ ZN * S := mul_le_mul_of_nonneg_right hA.le hSnn
    have h3 : ZN * (amin * κ) ≤ ZN * ((1 + κ) * S) := by nlinarith
    have h4 : amin * κ ≤ (1 + κ) * S := le_of_mul_le_mul_left h3 hZNpos
    have h5 : amin * κ / (2 * (1 + κ)) ≤ S / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hWle : K * ∑ i, (if alpha i = 0 then v i else 0) * deriv (fun s => Zh s i) t ≤
        -(K * (amin * κ / (2 * (1 + κ)))) := by
      have := mul_le_mul_of_nonneg_left hW hK0
      have h6 := mul_le_mul_of_nonneg_left h5 hK0
      linarith
    linarith [hpen.1]

/-- C2: the degenerate case, some class has zero total arrival rate. Lyapunov function
`φ_β + K·W` with `β = α + ε γ` (perturbed total rates) and `W` the zero-rate work. -/
theorem pf_fluid_model_stable_core
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0))
    (alpha : Fin I → ℝ) (halpha : IsTotalArrivalRates dat alpha)
    (hload : ∃ a ∈ dat.TildeAllocSet, ∀ ℓ, groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ < a ℓ) :
    PFFluidStable dat := by
  have hα0 := pf_alpha_nonneg dat hlam hP_nonneg hP_transient alpha halpha
  have hfix : ∀ i, alpha i = dat.lam i + ∑ k, dat.P k i * alpha k := fun i => congrFun halpha i
  obtain ⟨a, haA, hlt⟩ := hload
  set ρ : Fin L → ℝ := fun ℓ => groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ with hρ
  have hρnn : ∀ ℓ, 0 ≤ ρ ℓ := fun ℓ =>
    Finset.sum_nonneg (fun i _ => mul_nonneg (hα0 i) (dat.hm i).le)
  -- load slack
  obtain ⟨δ0, hδ0, hδ0l⟩ := PF_exists_pos_lb (fun ℓ => (a ℓ - ρ ℓ) / (ρ ℓ + 1))
  set δ : ℝ := min δ0 3 with hδdef
  have hδ : 0 < δ := lt_min hδ0 (by norm_num)
  have hδ3 : δ ≤ 3 := min_le_right _ _
  have hδa : ∀ ℓ, (1 + δ) * ρ ℓ ≤ a ℓ := by
    intro ℓ
    have hpos : 0 < (a ℓ - ρ ℓ) / (ρ ℓ + 1) :=
      div_pos (by linarith [hlt ℓ]) (by linarith [hρnn ℓ])
    have h1 := (min_le_left δ0 3).trans (hδ0l ℓ hpos)
    rw [le_div_iff₀ (by linarith [hρnn ℓ])] at h1
    nlinarith [hρnn ℓ]
  have hapos : ∀ ℓ, 0 < a ℓ := fun ℓ => lt_of_le_of_lt (hρnn ℓ) (hlt ℓ)
  obtain ⟨amin, hamin, haminl⟩ := PF_exists_pos_lb a
  have hamin_le : ∀ ℓ, amin ≤ a ℓ := fun ℓ => haminl ℓ (hapos ℓ)
  set η : ℝ := δ / 3 with hηdef
  have hη : 0 < η := by positivity
  have hη2 : η ≤ 2 := by rw [hηdef]; linarith
  have hηκ : (1 + η) * (1 + η) ≤ 1 + δ := by rw [hηdef]; nlinarith
  -- paths from exogenous sources to positive-rate classes
  have hex : ∀ i, ∃ n : ℕ, 0 < alpha i → ∃ j < n, ∃ k, 0 < dat.lam k ∧ 0 < (dat.P ^ j) k i := by
    intro i
    by_cases h : 0 < alpha i
    · obtain ⟨j, k, hk, hjk⟩ :=
        PF_path_exists dat.lam dat.P alpha hlam hP_nonneg hP_transient hfix i h
      exact ⟨j + 1, fun _ => ⟨j, by omega, k, hk, hjk⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose nf hnf using hex
  set N : ℕ := Finset.univ.sup nf + 1 with hNdef
  have hN : ∀ i, 0 < alpha i → ∃ j < N, ∃ k, 0 < dat.lam k ∧ 0 < (dat.P ^ j) k i := by
    intro i hi
    obtain ⟨j, hj, k, hk⟩ := hnf i hi
    exact ⟨j, by have := Finset.le_sup (f := nf) (Finset.mem_univ i); omega, k, hk⟩
  have hNpos : (0 : ℝ) < N := by rw [hNdef]; positivity
  obtain ⟨c1, hc1, hc1l⟩ := PF_exists_pos_lb dat.lam
  obtain ⟨c2, hc2, hc2l⟩ := PF_exists_pos_lb (fun p : Fin I × Fin I => dat.P p.1 p.2 * alpha p.1)
  set c : ℝ := min c1 c2 with hcdef
  have hc : 0 < c := lt_min hc1 hc2
  have hcl : ∀ k, 0 < dat.lam k → c ≤ dat.lam k := fun k hk => (min_le_left _ _).trans (hc1l k hk)
  have hcP : ∀ k i, 0 < dat.P k i * alpha k → c ≤ dat.P k i * alpha k := fun k i hk =>
    (min_le_right _ _).trans (hc2l (k, i) hk)
  set cA : ℝ := c * (η / 2 / (3 * N)) ^ 2 with hcA
  have hcApos : 0 < cA := by positivity
  -- supersolutions
  have htrT : ∀ i j, Tendsto (fun n => (dat.P.transpose ^ n) i j) atTop (𝓝 0) := by
    intro i j
    simp only [← Matrix.transpose_pow, Matrix.transpose_apply]
    exact hP_transient j i
  obtain ⟨γ, hγ1, hγ⟩ := PF_supersol dat.P.transpose (fun i j => hP_nonneg j i) htrT
    (fun _ => 1) (fun _ => one_pos)
  have hγ0 : ∀ i, 0 ≤ γ i := fun i => le_trans zero_le_one (hγ1 i)
  set w : Fin I → ℝ := fun i => γ i - ∑ k, dat.P k i * γ k with hw
  have hw0 : ∀ i, 0 ≤ w i := by
    intro i
    have := hγ i
    simp only [Matrix.transpose_apply] at this
    simp only [hw]; linarith
  have hwle : ∑ i, w i ≤ ∑ i, γ i := Finset.sum_le_sum (fun i _ => by
    have : 0 ≤ ∑ k, dat.P k i * γ k := Finset.sum_nonneg (fun k _ => mul_nonneg (hP_nonneg k i) (hγ0 k))
    simp only [hw]; linarith)
  obtain ⟨v, hvm, hv⟩ := PF_supersol dat.P hP_nonneg hP_transient dat.m dat.hm
  have hvnn : ∀ i, 0 ≤ v i := fun i => le_trans (dat.hm i).le (hvm i)
  -- the perturbation size
  set G : Fin L → ℝ := fun ℓ => groupAggregate dat.grp (fun i => γ i * dat.m i) ℓ with hG
  have ht0 : ∀ X : ℝ, Tendsto (fun e : ℝ => e * X) (𝓝[>] 0) (𝓝 0) := fun X => by
    have : Tendsto (fun e : ℝ => e * X) (𝓝 0) (𝓝 (0 * X)) := tendsto_id.mul_const X
    rw [zero_mul] at this; exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hev : ∀ᶠ e in 𝓝[>] (0:ℝ), e * ∑ i, γ i < cA / 2 ∧
      (∀ i, 0 < alpha i → e * γ i < η / 4 * alpha i) ∧ (∀ ℓ, e * G ℓ < a ℓ - ρ ℓ) := by
    refine ((ht0 _).eventually (gt_mem_nhds (by positivity))).and
      ((Filter.eventually_all.mpr fun i => ?_).and (Filter.eventually_all.mpr fun ℓ => ?_))
    · by_cases hi : 0 < alpha i
      · exact ((ht0 (γ i)).eventually (gt_mem_nhds (by positivity))).mono (fun e he _ => he)
      · exact Filter.Eventually.of_forall (fun e h => absurd h hi)
    · exact (ht0 (G ℓ)).eventually (gt_mem_nhds (by linarith [hlt ℓ]))
  obtain ⟨eps, ⟨hE1', hE2, hE3⟩, heps⟩ := (hev.and self_mem_nhdsWithin).exists
  have heps' : (0:ℝ) < eps := heps
  set β : Fin I → ℝ := fun i => alpha i + eps * γ i with hβ
  have hβpos : ∀ i, 0 < β i := fun i => by
    simp only [hβ]; have := hγ1 i; have := hα0 i; nlinarith
  have hαβ : ∀ i, alpha i ≤ β i := fun i => by
    simp only [hβ]; have := mul_nonneg heps'.le (hγ0 i); linarith
  have hβfix : ∀ i, β i = (dat.lam i + eps * w i) + ∑ k, dat.P k i * β k := by
    intro i
    have e1 : ∑ k, dat.P k i * β k = ∑ k, dat.P k i * alpha k + eps * ∑ k, dat.P k i * γ k := by
      simp only [hβ]; rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [e1]; simp only [hβ, hw]
    linear_combination hfix i
  have hβη : ∀ i, 0 < alpha i → (1 + η / 2) * β i ≤ (1 + η) * alpha i := by
    intro i hi
    simp only [hβ]
    have h1 := mul_le_mul_of_nonneg_left (hE2 i hi).le (by positivity : (0:ℝ) ≤ 1 + η / 2)
    have h2 : η * η ≤ 2 * η := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 hi.le
    nlinarith
  have hE1 : eps * ∑ i, w i ≤ cA / 2 :=
    le_trans (mul_le_mul_of_nonneg_left hwle heps'.le) hE1'.le
  have hloadβ : ∀ ℓ, groupAggregate dat.grp (fun i => β i * dat.m i) ℓ < a ℓ := by
    intro ℓ
    have : groupAggregate dat.grp (fun i => β i * dat.m i) ℓ = ρ ℓ + eps * G ℓ := by
      simp only [groupAggregate, hβ, hρ, hG]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this]; linarith [hE3 ℓ]
  -- the weight of the zero-rate work
  set q : ℝ := amin * η / (2 * (1 + η)) with hq
  have hqpos : 0 < q := by positivity
  have hwsum : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw0 i)
  set K : ℝ := (eps * ∑ i, w i + cA / 2) / q with hK
  have hK0 : 0 ≤ K := div_nonneg (by positivity) hqpos.le
  have hKB : eps * ∑ i, w i - K * q ≤ -(cA / 2) := by
    rw [hK, div_mul_cancel₀ _ hqpos.ne']; linarith
  set ε0 : ℝ := cA / 2 with hε0
  have hε0pos : 0 < ε0 := by positivity
  have hdrift : ∀ (Ah Dh Th Zh : ℝ → Fin I → ℝ), IsPFFluidModelSolution dat Ah Dh Th Zh →
      ∀ t : ℝ, 0 < t → RegularPoint Ah Dh Th Zh t → Zh t ≠ 0 →
      ∑ i, deriv (fun s => Zh s i) t * Real.log (deriv (fun s => Dh s i) t / β i) +
        K * ∑ i, (if alpha i = 0 then v i else 0) * deriv (fun s => Zh s i) t ≤ -ε0 :=
    fun Ah Dh Th Zh hsol t ht hreg hZ => PF_C2_drift dat hdom hlam hP_nonneg hP_rowsum alpha halpha hα0 a haA δ hδa η η hη hη2 hη hηκ
      amin hamin hamin_le N hN c hc hcl hcP β w eps heps'.le hw0 hβfix hαβ hβpos hβη hE1
      v hvnn hv K hK0 hKB Ah Dh Th Zh hsol t ht hreg hZ
  -- initial bound constant
  obtain ⟨cφ, hcφ0, hcφ⟩ := PF_entropy_le_const dat hdom β hβpos
  set V : ℝ := ∑ i, v i with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun i _ => hvnn i)
  set C0 : ℝ := cφ + K * V with hC0
  have hC00 : 0 ≤ C0 := by positivity
  clear_value ρ δ η N c cA w G β q K ε0 V C0
  have hγpos : 0 < C0 / ε0 + 1 := add_pos_of_nonneg_of_pos (div_nonneg hC00 hε0pos.le) one_pos
  refine ⟨C0 / ε0 + 1, hγpos, ?_⟩
  intro Ah Dh Th Zh hsol t ht
  have hZnn : ∀ s, 0 ≤ s → ∀ i, 0 ≤ Zh s i := hsol.2.1
  set W : ℝ → ℝ := fun s => ∑ i, (if alpha i = 0 then v i else 0) * Zh s i with hWdef
  set Lf : ℝ → ℝ := fun s => phiF β Dh Zh s + K * W s with hLf
  have hvN0 : ∀ i, 0 ≤ (if alpha i = 0 then v i else 0) := fun i => by
    split_ifs; exact hvnn i; exact le_rfl
  have hW0 : ∀ s, 0 ≤ s → 0 ≤ W s := fun s hs =>
    Finset.sum_nonneg (fun i _ => mul_nonneg (hvN0 i) (hZnn s hs i))
  have hWle : ∀ s, 0 ≤ s → W s ≤ V * ∑ i, Zh s i := by
    intro s hs
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right ?_ (hZnn s hs i))
    have : v i ≤ V := by
      rw [hV]; exact Finset.single_le_sum (f := v) (fun j _ => hvnn j) (Finset.mem_univ i)
    split_ifs; exact this; exact hV0
  have hS0 : 0 ≤ ∑ i, Zh 0 i := Finset.sum_nonneg (fun i _ => hZnn 0 le_rfl i)
  have hγS : 0 ≤ (C0 / ε0 + 1) * ∑ i, Zh 0 i := mul_nonneg hγpos.le hS0
  have ht0' : 0 ≤ t := le_trans hγS ht
  rcases eq_or_lt_of_le ht0' with ht0' | htpos
  · subst ht0'
    have hS : ∑ i, Zh 0 i = 0 := by
      have h2 : (C0 / ε0 + 1) * ∑ i, Zh 0 i ≤ (C0 / ε0 + 1) * 0 := by rw [mul_zero]; exact ht
      exact le_antisymm (le_of_mul_le_mul_left h2 hγpos) hS0
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hZnn 0 le_rfl i)).mp hS
    funext i; exact this i (Finset.mem_univ i)
  · set S0 := ∑ i, Zh 0 i with hS0def
    have hlim : C0 * S0 / ε0 < t := by
      rcases eq_or_lt_of_le hS0 with h0 | h0
      · rw [← h0]; simpa using htpos
      · have e : (C0 / ε0 + 1) * S0 = C0 * S0 / ε0 + S0 := by ring
        linarith
    have hT : Tendsto (fun s => s + C0 * (∑ i, Zh s i) / ε0) (𝓝[>] 0) (𝓝 (0 + C0 * S0 / ε0)) := by
      refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).add ?_
      refine Tendsto.div_const (Tendsto.const_mul C0 ?_) ε0
      exact tendsto_finsetSum _ (fun i _ => PF_Z_tendsto dat Ah Dh Th Zh hsol i)
    have hev := hT.eventually (gt_mem_nhds (by rw [zero_add]; exact hlim : 0 + C0 * S0 / ε0 < t))
    obtain ⟨s, hs, hspos⟩ := (hev.and self_mem_nhdsWithin).exists
    have hspos' : (0:ℝ) < s := hspos
    have hreg := PF_ae_regular dat Ah Dh Th Zh hsol
    obtain ⟨M1, hM10, hM1⟩ := PF_dini_bdd dat hdom hlam hP_nonneg β hβpos Ah Dh Th Zh hsol
    obtain ⟨KZ, hKZ0, hKZ⟩ := PF_Z_inc dat hlam hP_nonneg Ah Dh Th Zh hsol
    have hWinc : ∀ u z, 0 ≤ u → u ≤ z → W z - W u ≤ V * KZ * (z - u) := by
      intro u z hu huz
      have : W z - W u = ∑ i, (if alpha i = 0 then v i else 0) * (Zh z i - Zh u i) := by
        simp only [hWdef]; rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [this, hV, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have h1 := hKZ u z hu huz i
      have hvi : (if alpha i = 0 then v i else 0) ≤ v i := by split_ifs; exact le_rfl; exact hvnn i
      calc (if alpha i = 0 then v i else 0) * (Zh z i - Zh u i)
          ≤ (if alpha i = 0 then v i else 0) * (KZ * (z - u)) :=
            mul_le_mul_of_nonneg_left h1 (hvN0 i)
        _ ≤ v i * (KZ * (z - u)) :=
            mul_le_mul_of_nonneg_right hvi (mul_nonneg hKZ0 (by linarith))
        _ = v i * KZ * (z - u) := by ring
    have hWcont : ContinuousOn W (Set.Ioi 0) := by
      intro u hu
      refine ContinuousAt.continuousWithinAt ?_
      exact tendsto_finsetSum _ (fun i _ =>
        continuousAt_const.mul (PF_Z_contAt dat Ah Dh Th Zh hsol u hu i))
    have hext := dini_extinction_from Lf ε0 hε0pos s
      (fun u hu => add_nonneg
        (PF_K5_gen dat hdom β hβpos a haA hloadβ Ah Dh Th Zh hsol u (lt_of_lt_of_le hspos' hu)).1
        (mul_nonneg hK0 (hW0 u (le_trans hspos'.le hu))))
      (((PF_phiF_cont dat hdom β hβpos Ah Dh Th Zh hsol).add (continuousOn_const.mul hWcont)).mono
        (fun u hu => lt_of_lt_of_le hspos' hu))
      (fun b => ⟨M1 + K * (V * KZ), add_nonneg hM10 (mul_nonneg hK0 (mul_nonneg hV0 hKZ0)),
        fun u hu _ => by
        have hu0 : 0 < u := lt_of_lt_of_le hspos' hu
        filter_upwards [hM1 u hu0, self_mem_nhdsWithin] with z hz hzu
        have hzu' : u < z := hzu
        have h2 := mul_le_mul_of_nonneg_left (hWinc u z hu0.le hzu'.le) hK0
        calc Lf z - Lf u = (phiF β Dh Zh z - phiF β Dh Zh u) + K * (W z - W u) := by
              simp only [hLf]; ring
          _ ≤ M1 * (z - u) + K * (V * KZ * (z - u)) := add_le_add hz h2
          _ = (M1 + K * (V * KZ)) * (z - u) := by ring⟩)
      (by
        filter_upwards [hreg] with u hu hsu hpos η1 hη1
        have hu0 : 0 < u := lt_trans hspos' hsu
        have hreg_u := hu hu0
        have hZu : Zh u ≠ 0 := by
          intro hz
          have h1 : phiF β Dh Zh u = 0 := by simp [phiF, hz]
          have h2 : W u = 0 := by simp [hWdef, hz]
          have : Lf u = 0 := by simp only [hLf, h1, h2, mul_zero, add_zero]
          linarith
        have hd := hdrift Ah Dh Th Zh hsol u hu0 hreg_u hZu
        have h1 := PF_dini_regular dat hdom β hβpos Ah Dh Th Zh hsol u hu0 hreg_u (η1 / 2)
          (half_pos hη1)
        have hWd : HasDerivAt W (∑ i, (if alpha i = 0 then v i else 0) *
            deriv (fun s => Zh s i) u) u :=
          HasDerivAt.fun_sum (fun i _ =>
            ((differentiableAt_pi.mp hreg_u.2.2.2) i).hasDerivAt.const_mul _)
        have hsl := PF_slope_right W _ u hWd
        have hK1 : 0 < K + 1 := by linarith
        have h2 := hsl.eventually (gt_mem_nhds (show ∑ i, (if alpha i = 0 then v i else 0) *
            deriv (fun s => Zh s i) u < ∑ i, (if alpha i = 0 then v i else 0) *
            deriv (fun s => Zh s i) u + η1 / (2 * (K + 1)) by
          have : 0 < η1 / (2 * (K + 1)) := div_pos hη1 (by linarith)
          linarith))
        filter_upwards [h1, h2, self_mem_nhdsWithin] with z hz1 hz2 hzu
        have hzu' : 0 < z - u := sub_pos.mpr hzu
        rw [div_lt_iff₀ hzu'] at hz2
        set Wd := ∑ i, (if alpha i = 0 then v i else 0) * deriv (fun s => Zh s i) u with hWd'
        set Dφ := ∑ i, deriv (fun s => Zh s i) u * Real.log (deriv (fun s => Dh s i) u / β i)
          with hDφ
        have h3 : K * (W z - W u) ≤ K * ((Wd + η1 / (2 * (K + 1))) * (z - u)) :=
          mul_le_mul_of_nonneg_left hz2.le hK0
        have h4 : K * (η1 / (2 * (K + 1))) ≤ η1 / 2 := by
          have e : K * (η1 / (2 * (K + 1))) = η1 / 2 - η1 / (2 * (K + 1)) := by
            field_simp; ring
          have : 0 < η1 / (2 * (K + 1)) := div_pos hη1 (by linarith)
          linarith
        have h5 : K * (η1 / (2 * (K + 1))) * (z - u) ≤ η1 / 2 * (z - u) :=
          mul_le_mul_of_nonneg_right h4 hzu'.le
        have h6 : (Dφ + K * Wd) * (z - u) ≤ -ε0 * (z - u) :=
          mul_le_mul_of_nonneg_right hd hzu'.le
        calc Lf z - Lf u = (phiF β Dh Zh z - phiF β Dh Zh u) + K * (W z - W u) := by
              simp only [hLf]; ring
          _ ≤ (Dφ + η1 / 2) * (z - u) + K * ((Wd + η1 / (2 * (K + 1))) * (z - u)) :=
              add_le_add hz1 h3
          _ = (Dφ + K * Wd) * (z - u) + η1 / 2 * (z - u) +
              K * (η1 / (2 * (K + 1))) * (z - u) := by ring
          _ ≤ -ε0 * (z - u) + η1 / 2 * (z - u) + η1 / 2 * (z - u) :=
              add_le_add (add_le_add h6 le_rfl) h5
          _ = (-ε0 + η1) * (z - u) := by ring)
    have hφs := hcφ Ah Dh Th Zh hsol s hspos'
    have hLs : Lf s ≤ C0 * ∑ i, Zh s i := by
      have h1 : phiF β Dh Zh s ≤ cφ * ∑ i, Zh s i := hφs
      have h2 := mul_le_mul_of_nonneg_left (hWle s hspos'.le) hK0
      calc Lf s = phiF β Dh Zh s + K * W s := rfl
        _ ≤ cφ * ∑ i, Zh s i + K * (V * ∑ i, Zh s i) := add_le_add h1 h2
        _ = C0 * ∑ i, Zh s i := by rw [hC0]; ring
    have hts : s + Lf s / ε0 ≤ t := by
      have h1 : Lf s / ε0 ≤ C0 * (∑ i, Zh s i) / ε0 := div_le_div_of_nonneg_right hLs hε0pos.le
      have h2 : s + C0 * (∑ i, Zh s i) / ε0 < t := hs
      linarith
    have hLt : Lf t = 0 := hext t hts
    by_contra hne
    have h1 := (PF_K5_gen dat hdom β hβpos a haA hloadβ Ah Dh Th Zh hsol t htpos).2 hne
    have h2 := mul_nonneg hK0 (hW0 t htpos.le)
    have : Lf t = phiF β Dh Zh t + K * W t := rfl
    linarith

open ProcessingNetworks.ProportionalFairness in
theorem solution
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0))
    (alpha : Fin I → ℝ) (halpha : IsTotalArrivalRates dat alpha)
    (hload : ∃ a ∈ dat.TildeAllocSet, ∀ ℓ, groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ < a ℓ) :
    PFFluidStable dat := by
  exact pf_fluid_model_stable_core dat hdom hlam hP_nonneg hP_rowsum hP_transient alpha halpha hload
