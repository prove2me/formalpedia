-- Prove2me | solution 1 for OptStopC1.SpaceDeriv.theorem_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:52:45.587338+00:00
-- url     : https://prove2.me/submissions/684cfb49-c65e-4df7-8154-7c96bee9e1b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OptStopC1_SpaceDeriv_equation_4_16
import Theorems.Thm_OptStopC1_SpaceDeriv_equation_4_19

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval

theorem optStopT8_clm_rep {d : ℕ} (M : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    M = ∑ i, M (EuclideanSpace.single i (1:ℝ)) • EuclideanSpace.proj i := by
  ext x
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x]
  simp [map_sum, mul_comm]

theorem optStopT8_clm_tendsto {d : ℕ} {α : Type*} {l : Filter α}
    (f : α → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (h : ∀ i, Tendsto (fun a => f a (EuclideanSpace.single i (1:ℝ))) l
      (𝓝 (L (EuclideanSpace.single i (1:ℝ))))) : Tendsto f l (𝓝 L) := by
  have e1 : f = fun a => ∑ i, f a (EuclideanSpace.single i (1:ℝ)) • EuclideanSpace.proj i :=
    funext fun a => optStopT8_clm_rep (f a)
  rw [e1, optStopT8_clm_rep L]
  exact tendsto_finsetSum _ fun i _ => (h i).smul_const _

open OptStopC1.SpaceDeriv in
theorem solution
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (p : StoppingProblem d Ω P 𝔽)
    (hcommon : Theorem8Common p)
    (z : State d) (hz : z ∈ stoppingBoundary p)
    (hzreg : BoundaryHypotheses p z) :
    HasFDerivAt (value p) (fderiv ℝ p.G z) z ∧
    Tendsto (fderiv ℝ (value p)) (𝓝[continuationSet p] z)
      (𝓝 (fderiv ℝ p.G z)) := by
  obtain ⟨hwp, hgen, hVc, hVC1, hG1, hLip, hflow⟩ := id hcommon
  set V := value p with hVdef
  set C := continuationSet p with hCdef
  set D := stoppingSet p with hDdef
  -- V ≥ G everywhere (stop immediately).
  have hge : ∀ x, p.G x ≤ V x := by
    intro x
    have h0 : payoff p x (fun _ => 0) = p.G x := by
      have hX0 : ∀ ω, p.X x 0 ω = x := fun ω => p.standard.1 x ω
      simp [payoff, payoffRandom, discount, hX0]
    have hadm : Admissible 𝔽 (fun _ : Ω => (0 : ℝ≥0)) := by
      unfold Admissible
      exact isStoppingTime_const 𝔽 _
    have hbdd : BddAbove {v : ℝ | ∃ τ : Ω → ℝ≥0, Admissible 𝔽 τ ∧ v = payoff p x τ} := by
      refine ⟨payoff p x (finiteEntryTime p.X x (stoppingSet p)), ?_⟩
      rintro v ⟨τ, hτ, rfl⟩
      exact hwp.2.2.2.2.1 x τ hτ
    rw [← h0]
    exact le_csSup hbdd ⟨_, hadm, rfl⟩
  have hCD : ∀ x, x ∈ C ∨ x ∈ D := by
    intro x
    rcases (hge x).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  have hDC : ∀ x, x ∈ D → x ∉ C := by
    intro x hx hc
    have h1 : V x = p.G x := hx
    have h2 : p.G x < V x := hc
    linarith
  have hCopen : IsOpen C := isOpen_lt p.G_continuous hVc
  have hDeq : D = Cᶜ := by
    ext x; exact ⟨hDC x, fun h => (hCD x).resolve_left h⟩
  have hDclosed : IsClosed D := by rw [hDeq]; exact hCopen.isClosed_compl
  -- Part (b): derivative limit along C from (4.16) and (4.19).
  have hb : Tendsto (fderiv ℝ V) (𝓝[C] z) (𝓝 (fderiv ℝ p.G z)) := by
    rw [tendsto_iff_seq_tendsto]
    intro xs hxs
    have hev : ∀ᶠ n in atTop, xs n ∈ C := hxs.eventually self_mem_nhdsWithin
    have hconv : Tendsto xs atTop (𝓝 z) := tendsto_nhds_of_tendsto_nhdsWithin hxs
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine (tendsto_add_atTop_iff_nat N).1 ?_
    refine optStopT8_clm_tendsto (fun n => fderiv ℝ V (xs (n + N))) _ fun i => ?_
    have hys : ∀ n, xs (n + N) ∈ C := fun n => hN _ (by omega)
    have hysc : Tendsto (fun n => xs (n + N)) atTop (𝓝 z) :=
      hconv.comp (tendsto_add_atTop_nat N)
    rw [tendsto_order]
    exact ⟨OptStopC1.SpaceDeriv.equation_4_16 hd P 𝔽 p hcommon z hz hzreg _ hys hysc i,
      OptStopC1.SpaceDeriv.equation_4_19 hd P 𝔽 p hcommon z hz hzreg _ hys hysc i⟩
  refine ⟨?_, hb⟩
  -- Part (a): V - G = o(|y - z|) by the mean value theorem along segments.
  have hVz : V z = p.G z := hz.1
  have hGf : Continuous (fderiv ℝ p.G) := hG1.continuous_fderiv one_ne_zero
  have hGd : Differentiable ℝ p.G := hG1.differentiable one_ne_zero
  have hW : ∀ ε > 0, ∀ᶠ y in 𝓝 z, V y - p.G y ≤ ε * ‖y - z‖ := by
    intro ε hε
    have h0 : Tendsto (fun x => fderiv ℝ V x - fderiv ℝ p.G x) (𝓝[C] z) (𝓝 0) := by
      have := hb.sub ((hGf.tendsto z).mono_left nhdsWithin_le_nhds)
      simpa using this
    have h1 : ∀ᶠ x in 𝓝[C] z, ‖fderiv ℝ V x - fderiv ℝ p.G x‖ ≤ ε :=
      h0.norm.eventually (ge_mem_nhds (by simpa using hε))
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h1)
    filter_upwards [Metric.ball_mem_nhds z hδ] with y hy
    rcases hCD y with hyC | hyD
    · set g : ℝ → State d := fun t => z + t • (y - z) with hgdef
      have hg : Continuous g := by fun_prop
      set S := Icc (0:ℝ) 1 ∩ g ⁻¹' D with hSdef
      have hSc : IsClosed S := isClosed_Icc.inter (hDclosed.preimage hg)
      have h0S : (0:ℝ) ∈ S := ⟨⟨le_refl _, zero_le_one⟩, by simpa [g] using hz.1⟩
      have hSb : BddAbove S := ⟨1, fun t ht => ht.1.2⟩
      set s := sSup S with hsdef
      have hsS : s ∈ S := hSc.csSup_mem ⟨0, h0S⟩ hSb
      have hs0 : 0 ≤ s := le_csSup hSb h0S
      have hs1 : s < 1 := by
        rcases hsS.1.2.lt_or_eq with h | h
        · exact h
        · exfalso
          have : g 1 ∈ D := by rw [← h]; exact hsS.2
          exact hDC y (by simpa [g] using this) hyC
      have hCseg : ∀ t ∈ Ioc s 1, g t ∈ C := by
        intro t ht
        rcases hCD (g t) with h | h
        · exact h
        · exfalso
          have : t ≤ s := le_csSup hSb ⟨⟨hs0.trans ht.1.le, ht.2⟩, h⟩
          linarith [ht.1]
      set h : ℝ → ℝ := fun t => V (g t) - p.G (g t) with hhdef
      have hcont : ContinuousOn h (Icc s 1) :=
        ((hVc.comp hg).sub (p.G_continuous.comp hg)).continuousOn
      have hderiv : ∀ t ∈ Ioo s 1, HasDerivAt h
          (fderiv ℝ V (g t) (y - z) - fderiv ℝ p.G (g t) (y - z)) t := by
        intro t ht
        have hgd : HasDerivAt g (y - z) t := by
          have := ((hasDerivAt_id t).smul_const (y - z)).const_add z
          rw [one_smul] at this
          exact this
        have hgC : g t ∈ C := hCseg t ⟨ht.1, ht.2.le⟩
        have hVd : DifferentiableAt ℝ V (g t) :=
          (hVC1.contDiffAt (hCopen.mem_nhds hgC)).differentiableAt one_ne_zero
        exact (hVd.hasFDerivAt.comp_hasDerivAt t hgd).sub
          ((hGd (g t)).hasFDerivAt.comp_hasDerivAt t hgd)
      obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope h _ hs1 hcont hderiv
      have hhs : h s = 0 := by
        have : g s ∈ D := hsS.2
        simp only [h]
        rw [show V (g s) = p.G (g s) from this, sub_self]
      have hh1 : h 1 = V y - p.G y := by simp [h, g]
      have hgcC : g c ∈ C := hCseg c ⟨hc.1, hc.2.le⟩
      have hgcB : dist (g c) z < δ := by
        have hc0 : 0 ≤ c := hs0.trans hc.1.le
        rw [dist_eq_norm]
        simp only [g, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
        have : ‖y - z‖ < δ := by rw [← dist_eq_norm]; exact hy
        nlinarith [norm_nonneg (y - z), hc.2]
      have hnorm := hball hgcB hgcC
      have hbound : fderiv ℝ V (g c) (y - z) - fderiv ℝ p.G (g c) (y - z) ≤ ε * ‖y - z‖ := by
        have e : fderiv ℝ V (g c) (y - z) - fderiv ℝ p.G (g c) (y - z)
            = (fderiv ℝ V (g c) - fderiv ℝ p.G (g c)) (y - z) := by simp
        rw [e]
        calc _ ≤ ‖(fderiv ℝ V (g c) - fderiv ℝ p.G (g c)) (y - z)‖ := le_abs_self _
          _ ≤ ‖fderiv ℝ V (g c) - fderiv ℝ p.G (g c)‖ * ‖y - z‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ ε * ‖y - z‖ := by gcongr
      have hpos : 0 < 1 - s := by linarith
      rw [hhs, hh1, sub_zero] at hceq
      have : V y - p.G y = (fderiv ℝ V (g c) (y - z) - fderiv ℝ p.G (g c) (y - z)) * (1 - s) := by
        rw [hceq]; field_simp
      rw [this]
      have hnn : 0 ≤ ε * ‖y - z‖ := by positivity
      nlinarith
    · have : V y = p.G y := hyD
      rw [this, sub_self]
      positivity
  have hWo : (fun y => V y - p.G y) =o[𝓝 z] (fun y => y - z) := by
    refine Asymptotics.isLittleO_iff.2 fun ε hε => ?_
    filter_upwards [hW ε hε] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (hge y))]
    exact hy
  have hGo := (hGd z).hasFDerivAt.isLittleO
  refine HasFDerivAt.of_isLittleO ((hWo.add hGo).congr_left fun y => ?_)
  rw [hVz]; ring
