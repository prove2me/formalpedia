-- Prove2me | solution 1 for OptStopC1.SpaceDeriv.global_C1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:48:18.606813+00:00
-- url     : https://prove2.me/submissions/083e5798-9daf-4e91-a820-7912fd0dfd62
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OptStopC1_SpaceDeriv_theorem_8

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval

open OptStopC1.SpaceDeriv in
theorem solution
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (p : StoppingProblem d Ω P 𝔽)
    (hcommon : Theorem8Common p)
    (hall : ∀ z ∈ stoppingBoundary p, BoundaryHypotheses p z) :
    ContDiff ℝ 1 (value p) := by
  obtain ⟨hwp, hgen, hVc, hVC1, hG1, hLip, hflow⟩ := id hcommon
  set V := value p with hVdef
  set C := continuationSet p
  set D := stoppingSet p
  -- Step 1: V ≥ G everywhere (stop immediately).
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
  have hCopen : IsOpen C := isOpen_lt p.G_continuous hVc
  -- Step 2: on D, V is differentiable with derivative DG.
  have hGdiff : Differentiable ℝ p.G := hG1.differentiable one_ne_zero
  have hD : ∀ y ∈ D, HasFDerivAt V (fderiv ℝ p.G y) y := by
    intro y hy
    by_cases hyc : y ∈ closure C
    · exact (OptStopC1.SpaceDeriv.theorem_8 hd P 𝔽 p
        hcommon y ⟨hy, hyc⟩ (hall y ⟨hy, hyc⟩)).1
    · have hev : p.G =ᶠ[𝓝 y] V := by
        have : (closure C)ᶜ ∈ 𝓝 y := isClosed_closure.isOpen_compl.mem_nhds hyc
        filter_upwards [this] with w hw
        rcases hCD w with h | h
        · exact absurd (subset_closure h) hw
        · exact h.symm
      exact (hGdiff y).hasFDerivAt.congr_of_eventuallyEq hev.symm
  -- Step 3: global differentiability.
  have hdiff : Differentiable ℝ V := by
    intro x
    rcases hCD x with h | h
    · exact (hVC1.contDiffAt (hCopen.mem_nhds h)).differentiableAt one_ne_zero
    · exact (hD x h).differentiableAt
  have hfD : ∀ y ∈ D, fderiv ℝ V y = fderiv ℝ p.G y := fun y hy => (hD y hy).fderiv
  -- Step 4: continuity of the derivative.
  have hGf : Continuous (fderiv ℝ p.G) := hG1.continuous_fderiv one_ne_zero
  refine contDiff_one_iff_fderiv.2 ⟨hdiff, continuous_iff_continuousAt.2 fun x => ?_⟩
  rcases hCD x with h | h
  · exact ((hVC1.contDiffAt (hCopen.mem_nhds h)).fderiv_right (m := 0) (by norm_num)).continuousAt
  · show Tendsto (fderiv ℝ V) (𝓝 x) (𝓝 (fderiv ℝ V x))
    rw [hfD x h]
    have hsplit : 𝓝 x = 𝓝[C] x ⊔ 𝓝[D] x := by
      rw [← nhdsWithin_union]
      have : C ∪ D = univ := eq_univ_of_forall fun y => (hCD y).elim Or.inl Or.inr
      rw [this, nhdsWithin_univ]
    rw [hsplit]
    refine tendsto_sup.2 ⟨?_, ?_⟩
    · by_cases hxc : x ∈ closure C
      · exact (OptStopC1.SpaceDeriv.theorem_8 hd P 𝔽 p hcommon x ⟨h, hxc⟩
          (hall x ⟨h, hxc⟩)).2
      · have : 𝓝[C] x = ⊥ := by
          rw [mem_closure_iff_nhdsWithin_neBot] at hxc
          exact not_neBot.1 hxc
        rw [this]
        exact tendsto_bot
    · refine Tendsto.congr' ?_ (hGf.continuousAt.mono_left nhdsWithin_le_nhds)
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hfD y hy).symm
