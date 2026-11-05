-- Prove2me | solution 1 for OptStopC1.TimeDeriv.global_time_derivative_continuous
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:48:55.664909+00:00
-- url     : https://prove2.me/submissions/25b635ab-f059-462b-9ecc-9144d09ea713
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OptStopC1_TimeDeriv_Flow
import Definitions.Def_OptStopC1_TimeDeriv_Problem
import Definitions.Def_OptStopC1_TimeDeriv_Generator
import Definitions.Def_OptStopC1_TimeDeriv_Hypotheses
import Theorems.Thm_OptStopC1_TimeDeriv_theorem_15

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

open OptStopC1.TimeDeriv in
theorem solution {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : StoppingProblem m Ω) (c : GenCoeffs m)
    (hM : M.Thm15Global c)
    (hloc : ∀ z ∈ M.boundary, M.Thm15AtPoint c z)
    (hPR : ∀ z ∈ M.boundary, IsProbRegular M.P M.T M.X (interior M.stoppingSet) z) :
    (∀ p ∈ domain m M.T,
      DifferentiableWithinAt ℝ (fun s => M.value (s, p.2)) (Set.Icc 0 M.T) p.1) ∧
    ContinuousOn (timeDeriv M.T M.value) (domain m M.T) := by
  have hT : 0 < M.T := hM.standing.T_pos
  have : IsProbabilityMeasure M.P := hM.standing.prob
  -- Step 0: `G ≤ V` on the domain (stop immediately).
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
  -- every point of the domain lies in `C` or in `D`
  have hCD : ∀ p ∈ domain m M.T, p ∈ M.contSet ∨ p ∈ M.stoppingSet := by
    intro p hp
    by_cases h : M.G p < M.value p
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, le_antisymm (not_lt.1 h) (hVG p hp)⟩
  have hdomIcc : ∀ x : Space m, Set.MapsTo (fun s : ℝ => (s, x)) (Set.Icc 0 M.T)
      (domain m M.T) := fun x s hs => ⟨hs, Set.mem_univ _⟩
  have hgcont : ∀ x : Space m, Continuous (fun s : ℝ => (s, x)) := fun x =>
    continuous_id.prodMk continuous_const
  -- Step 1: on `D`, `∂_t V = ∂_t G` (as derivatives within `[0, T]`).
  have hD : ∀ q ∈ M.stoppingSet,
      HasDerivWithinAt (fun s => M.value (s, q.2)) (timeDeriv M.T M.G q) (Set.Icc 0 M.T) q.1 := by
    intro q hq
    by_cases hcl : q ∈ closure M.contSet
    · exact (theorem_15 M c hM q ⟨hq, hcl⟩ (hloc q ⟨hq, hcl⟩) (hPR q ⟨hq, hcl⟩)).1
    · have hev : ∀ᶠ r in 𝓝 q, r ∉ M.contSet := by
        exact eventually_nhds_iff.2 ⟨(closure M.contSet)ᶜ,
          fun r hr hrC => hr (subset_closure hrC), isClosed_closure.isOpen_compl, hcl⟩
      have hGd : HasDerivWithinAt (fun s => M.G (s, q.2)) (timeDeriv M.T M.G q)
          (Set.Icc 0 M.T) q.1 :=
        (hM.G_C12.1 q hq.1).hasDerivWithinAt
      refine hGd.congr_of_eventuallyEq ?_ ?_
      · have h1 : Tendsto (fun s : ℝ => (s, q.2)) (𝓝[Set.Icc 0 M.T] q.1) (𝓝 q) := by
          have := ((hgcont q.2).tendsto q.1).mono_left
            (nhdsWithin_le_nhds (s := Set.Icc 0 M.T))
          simpa using this
        have h2 : ∀ᶠ s in 𝓝[Set.Icc 0 M.T] q.1, s ∈ Set.Icc 0 M.T := self_mem_nhdsWithin
        filter_upwards [h1.eventually hev, h2] with s hs hs2
        rcases hCD _ (hdomIcc q.2 hs2) with h | h
        · exact absurd h hs
        · exact h.2
      · simpa using hq.2
  have hDeq : ∀ q ∈ M.stoppingSet, timeDeriv M.T M.value q = timeDeriv M.T M.G q := by
    intro q hq
    exact (hD q hq).derivWithin (uniqueDiffOn_Icc hT q.1 hq.1.1)
  -- Step 2: `C = domain ∩ U` with `U` open.
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
  have huniq : UniqueDiffOn ℝ M.contSet := by
    rw [hU]
    exact ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ).inter hUo
  have hC1 := hM.value_C1
  have hfd : ContinuousOn (fderivWithin ℝ M.value M.contSet) M.contSet :=
    hC1.continuousOn_fderivWithin huniq le_rfl
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
  have hCeq : ∀ q ∈ M.contSet, timeDeriv M.T M.value q =
      fderivWithin ℝ M.value M.contSet q ((1 : ℝ), (0 : Space m)) := by
    intro q hq
    exact (hCd q hq).derivWithin (uniqueDiffOn_Icc hT q.1 hq.1.1)
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · rcases hCD p hp with h | h
    · exact (hCd p h).differentiableWithinAt
    · exact (hD p h).differentiableWithinAt
  · rcases hCD p hp with h | h
    · -- continuity at a point of `C`
      have hcC : ContinuousWithinAt (timeDeriv M.T M.value) M.contSet p := by
        have := ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : Space m))).continuous.comp_continuousOn
          hfd) p h
        exact this.congr (fun y hy => hCeq y hy) (hCeq p h)
      have hpU : p ∈ U := by
        have : p ∈ domain m M.T ∩ U := hU ▸ h
        exact this.2
      rw [hU] at hcC
      exact (continuousWithinAt_inter (hUo.mem_nhds hpU)).1 hcC
    · -- continuity at a point of `D`
      have hdom : domain m M.T = M.contSet ∪ M.stoppingSet := by
        ext q
        constructor
        · intro hq; rcases hCD q hq with h' | h'
          · exact Or.inl h'
          · exact Or.inr h'
        · rintro (h' | h')
          · exact h'.1
          · exact h'.1
      rw [hdom]
      refine ContinuousWithinAt.union ?_ ?_
      · by_cases hcl : p ∈ closure M.contSet
        · have := (theorem_15 M c hM p ⟨h, hcl⟩ (hloc p ⟨h, hcl⟩) (hPR p ⟨h, hcl⟩)).2
          rw [ContinuousWithinAt, hDeq p h]
          exact this
        · rw [ContinuousWithinAt, notMem_closure_iff_nhdsWithin_eq_bot.1 hcl]
          exact tendsto_bot
      · have hG : ContinuousWithinAt (timeDeriv M.T M.G) M.stoppingSet p :=
          (hM.G_C12.2.1 p hp).mono (fun q hq => hq.1)
        exact hG.congr (fun y hy => hDeq y hy) (hDeq p h)
