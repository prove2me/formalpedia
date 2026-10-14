-- Prove2me | solution 1 for StochApproxDyn.LimitSet.isAsymptoticPseudotrajectory_characterization
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:45:01.832412+00:00
-- url     : https://prove2.me/submissions/76ba0525-9670-417c-b81e-aa6e41a6ddd6

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_LimitSet_TranslationSemiflow

open scoped NNReal


namespace StochApproxDyn.LimitSet

theorem d45c_translate_apply {M : Type*} [MetricSpace M] (t s : ℝ≥0) (X : C(ℝ≥0, M)) :
    translate t X s = X (t + s) := rfl

theorem d45c_traj_apply {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (p : M) (s : ℝ≥0) :
    trajectory Φ p s = Φ s p := rfl

theorem d45c_compact {M : Type*} [MetricSpace M] (X : C(ℝ≥0, M))
    (hX : IsCompact (closure (Set.range X))) (hU : UniformContinuous X) :
    IsCompact (closure (Set.range fun t : ℝ≥0 => translate t X)) := by
  have hemb : Topology.IsClosedEmbedding (UniformOnFun.ofFun {K : Set ℝ≥0 | IsCompact K} ∘
      (DFunLike.coe : C(ℝ≥0, M) → ℝ≥0 → M)) := by
    refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    have : Set.range (UniformOnFun.ofFun {K : Set ℝ≥0 | IsCompact K} ∘
        (DFunLike.coe : C(ℝ≥0, M) → ℝ≥0 → M)) =
        Set.range (ContinuousMap.toUniformOnFunIsCompact (α := ℝ≥0) (β := M)) := rfl
    rw [this, ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun K hK => hK) hemb
  · intro K _
    apply Equicontinuous.equicontinuousOn
    intro x0
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp hU ε hε
    filter_upwards [Metric.ball_mem_nhds x0 hδ] with x hx
    rintro ⟨_, t, rfl⟩
    show dist (X (t + x0)) (X (t + x)) < ε
    apply hd
    have e : dist (t + x0) (t + x) = dist x x0 := by
      rw [NNReal.dist_eq, NNReal.dist_eq, NNReal.coe_add, NNReal.coe_add, abs_sub_comm]
      congr 1; ring
    rw [e]; exact hx
  · intro K _ x _
    exact ⟨closure (Set.range X), hX, by
      rintro _ ⟨t, rfl⟩
      exact subset_closure ⟨_, rfl⟩⟩

theorem d45c_uc {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M))
    (hX : IsCompact (closure (Set.range X))) (hA : IsAsymptoticPseudotrajectory Φ X) :
    UniformContinuous X := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hc : IsCompact (Set.Icc (0:ℝ≥0) 1 ×ˢ closure (Set.range X)) := isCompact_Icc.prod hX
  have hu := hc.uniformContinuousOn_of_continuous
    (f := fun p : ℝ≥0 × M => Φ p.1 p.2) (Φ.continuous continuous_fst continuous_snd).continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ1, hδ1, h1⟩ := hu (ε/3) (by linarith)
  obtain ⟨t₀, ht₀⟩ := hA.2 1 one_pos (ε/3) (by linarith)
  have hu2 := (isCompact_Icc (a := (0:ℝ≥0)) (b := t₀ + 1)).uniformContinuousOn_of_continuous
    X.continuous.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu2
  obtain ⟨δ2, hδ2, h2⟩ := hu2 ε hε
  have hδpos : 0 < min (min δ1 δ2) 1 := lt_min (lt_min hδ1 hδ2) one_pos
  have key : ∀ a b : ℝ≥0, a ≤ b → dist a b < min (min δ1 δ2) 1 → dist (X a) (X b) < ε := by
    intro a b hab hd
    by_cases hb : b ≤ t₀ + 1
    · exact h2 a ⟨zero_le, le_trans hab hb⟩ b ⟨zero_le, hb⟩
        (lt_of_lt_of_le hd (le_trans (min_le_left _ _) (min_le_right _ _)))
    · push_neg at hb
      have habR : (a:ℝ) ≤ b := by exact_mod_cast hab
      have hdab : (b:ℝ) - a < min (min δ1 δ2) 1 := by
        rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)] at hd
        exact hd
      have hm1 : min (min δ1 δ2) 1 ≤ 1 := min_le_right _ _
      have hmd1 : min (min δ1 δ2) 1 ≤ δ1 := le_trans (min_le_left _ _) (min_le_left _ _)
      have hbR : (t₀:ℝ) + 1 < b := by exact_mod_cast hb
      have ha : t₀ ≤ a := by
        have : (t₀:ℝ) ≤ a := by linarith
        exact_mod_cast this
      have hh1 : b - a ≤ 1 := by
        have : ((b - a : ℝ≥0) : ℝ) ≤ 1 := by
          rw [NNReal.coe_sub hab]; linarith
        exact_mod_cast this
      have hbh : a + (b - a) = b := add_tsub_cancel_of_le hab
      have e1 := ht₀ a ha (b - a) hh1
      rw [hbh] at e1
      have e2 : dist (Φ (b - a) (X a)) (Φ 0 (X a)) < ε / 3 :=
        h1 (b - a, X a) ⟨⟨zero_le, hh1⟩, subset_closure ⟨a, rfl⟩⟩ (0, X a)
          ⟨⟨le_rfl, zero_le⟩, subset_closure ⟨a, rfl⟩⟩ (by
            rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, NNReal.dist_eq,
              NNReal.coe_zero, sub_zero, NNReal.coe_sub hab, abs_of_nonneg (by linarith)]
            linarith)
      rw [Flow.map_zero_apply] at e2
      calc dist (X a) (X b) = dist (X b) (X a) := dist_comm _ _
        _ ≤ dist (X b) (Φ (b - a) (X a)) + dist (Φ (b - a) (X a)) (X a) := dist_triangle _ _ _
        _ < ε / 3 + ε / 3 := add_lt_add e1 e2
        _ < ε := by linarith
  refine ⟨min (min δ1 δ2) 1, hδpos, ?_⟩
  intro a b hd
  rcases le_total a b with hab | hab
  · exact key a b hab hd
  · rw [dist_comm]; exact key b a hab (by rwa [dist_comm])

theorem d45c_lim {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M))
    (hA : IsAsymptoticPseudotrajectory Φ X) :
    ∀ Y : C(ℝ≥0, M), (∃ τ : ℕ → ℝ≥0, Filter.Tendsto τ Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun k => translate (τ k) X) Filter.atTop (nhds Y)) →
      Y ∈ trajectorySpace Φ := by
  rintro Y ⟨τ, hτ, hconv⟩
  refine ⟨Y 0, ?_⟩
  ext h
  rw [d45c_traj_apply]
  have hev : ∀ s : ℝ≥0, Filter.Tendsto (fun k => X (τ k + s)) Filter.atTop (nhds (Y s)) :=
    fun s => ((continuous_eval_const s).tendsto Y).comp hconv
  have h0 : Filter.Tendsto (fun k => X (τ k)) Filter.atTop (nhds (Y 0)) := by
    simpa using hev 0
  have hΦ : Filter.Tendsto (fun k => Φ h (X (τ k))) Filter.atTop (nhds (Φ h (Y 0))) :=
    ((Φ.continuous continuous_const continuous_id).tendsto (Y 0)).comp h0
  have hd : Filter.Tendsto (fun k => dist (Φ h (X (τ k))) (X (τ k + h))) Filter.atTop
      (nhds 0) := by
    rcases eq_or_ne h 0 with hh | hh
    · subst hh
      simp [Flow.map_zero_apply]
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨t₀, ht₀⟩ := hA.2 h (pos_iff_ne_zero.mpr hh) ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Filter.tendsto_atTop.mp hτ t₀)
    refine ⟨N, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, dist_comm]
    exact ht₀ (τ k) (hN k hk) h le_rfl
  have h2 := tendsto_of_tendsto_of_dist hΦ hd
  exact tendsto_nhds_unique h2 (hev h)

theorem d45c_back {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M))
    (hX : IsCompact (closure (Set.range X))) (hU : UniformContinuous X)
    (hL : ∀ Y : C(ℝ≥0, M), (∃ τ : ℕ → ℝ≥0, Filter.Tendsto τ Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun k => translate (τ k) X) Filter.atTop (nhds Y)) →
      Y ∈ trajectorySpace Φ) :
    IsAsymptoticPseudotrajectory Φ X := by
  refine ⟨X.continuous, fun T hT ε hε => ?_⟩
  by_contra hcon
  push_neg at hcon
  choose u hu1 hh hh1 hh2 using fun k : ℕ => hcon (k : ℝ≥0)
  have hK := d45c_compact X hX hU
  obtain ⟨Y, _, φ, hφ, hYc⟩ := hK.tendsto_subseq
    (x := fun k => translate (u k) X) (fun k => subset_closure ⟨u k, rfl⟩)
  obtain ⟨h0, _, ψ, hψ, hhc⟩ := (isCompact_Icc (a := (0:ℝ≥0)) (b := T)).tendsto_subseq
    (x := fun k => hh (φ k)) (fun k => ⟨zero_le, hh1 (φ k)⟩)
  have hτ : Filter.Tendsto (fun k => u (φ (ψ k))) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨Nat.ceil b, fun k hk => ?_⟩
    have hk' : Nat.ceil b ≤ φ (ψ k) := le_trans hk ((hφ.comp hψ).id_le k)
    calc b ≤ (Nat.ceil b : ℝ≥0) := Nat.le_ceil b
      _ ≤ (φ (ψ k) : ℝ≥0) := by exact_mod_cast hk'
      _ ≤ u (φ (ψ k)) := hu1 _
  have hconv : Filter.Tendsto (fun k => translate (u (φ (ψ k))) X) Filter.atTop (nhds Y) :=
    hYc.comp hψ.tendsto_atTop
  obtain ⟨p, hp⟩ := hL Y ⟨_, hτ, hconv⟩
  -- joint convergence
  have hA : Filter.Tendsto (fun k => X (u (φ (ψ k)) + hh (φ (ψ k)))) Filter.atTop
      (nhds (Y h0)) := by
    have := (continuous_eval.tendsto (Y, h0)).comp (hconv.prodMk_nhds hhc)
    exact this
  have hB0 : Filter.Tendsto (fun k => X (u (φ (ψ k)))) Filter.atTop (nhds (Y 0)) := by
    have := ((continuous_eval_const (0:ℝ≥0)).tendsto Y).comp hconv
    simpa [Function.comp_def, d45c_translate_apply] using this
  have hB : Filter.Tendsto (fun k => Φ (hh (φ (ψ k))) (X (u (φ (ψ k))))) Filter.atTop
      (nhds (Φ h0 (Y 0))) :=
    ((Φ.continuous continuous_fst continuous_snd).tendsto (h0, Y 0)).comp
      (hhc.prodMk_nhds hB0)
  have hY : Y h0 = Φ h0 (Y 0) := by
    rw [← hp, d45c_traj_apply, d45c_traj_apply, Flow.map_zero_apply]
  have hD := hA.dist hB
  rw [hY, dist_self] at hD
  have hge : ∀ k, ε ≤ dist (X (u (φ (ψ k)) + hh (φ (ψ k))))
      (Φ (hh (φ (ψ k))) (X (u (φ (ψ k))))) := fun k => hh2 _
  have := ge_of_tendsto' hD hge
  linarith

theorem d45c_core {M : Type*} [MetricSpace M]
    (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M)) (hX : IsCompact (closure (Set.range X))) :
    (IsAsymptoticPseudotrajectory Φ X ↔
      (UniformContinuous X ∧
        ∀ Y : C(ℝ≥0, M), (∃ τ : ℕ → ℝ≥0, Filter.Tendsto τ Filter.atTop Filter.atTop ∧
            Filter.Tendsto (fun k => translate (τ k) X) Filter.atTop (nhds Y)) →
          Y ∈ trajectorySpace Φ)) ∧
    (IsAsymptoticPseudotrajectory Φ X →
      IsCompact (closure (Set.range fun t : ℝ≥0 => translate t X))) :=
  ⟨⟨fun hA => ⟨d45c_uc Φ X hX hA, d45c_lim Φ X hA⟩,
    fun h => d45c_back Φ X hX h.1 h.2⟩,
   fun hA => d45c_compact X hX (d45c_uc Φ X hX hA)⟩

end StochApproxDyn.LimitSet

open StochApproxDyn.LimitSet


theorem solution {M : Type*} [MetricSpace M]
    (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M)) (hX : IsCompact (closure (Set.range X))) :
    (IsAsymptoticPseudotrajectory Φ X ↔
      (UniformContinuous X ∧
        ∀ Y : C(ℝ≥0, M), (∃ τ : ℕ → ℝ≥0, Filter.Tendsto τ Filter.atTop Filter.atTop ∧
            Filter.Tendsto (fun k => translate (τ k) X) Filter.atTop (nhds Y)) →
          Y ∈ trajectorySpace Φ)) ∧
    (IsAsymptoticPseudotrajectory Φ X →
      IsCompact (closure (Set.range fun t : ℝ≥0 => translate t X))) := by
  exact d45c_core Φ X hX
