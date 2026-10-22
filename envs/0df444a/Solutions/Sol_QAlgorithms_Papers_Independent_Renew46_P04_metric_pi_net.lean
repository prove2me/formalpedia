-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.metric_pi_net
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:34:05.080018+00:00
-- url     : https://prove2.me/submissions/7f7c26d5-2e7f-407b-a914-e7fea0a5d148

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04
noncomputable section

set_option synthInstance.maxSize 8192

open QAlgorithms.Papers.Independent.Renew46.P04

open Filter Set

open scoped Topology TensorProduct ENNReal

universe u v

variable {K : Type*} [RCLike K]

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

section Banach

variable {X Y Z : Type*}

variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]

variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

variable [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]

theorem solution [CompleteSpace X] : MetricPi K X ↔
    ∃ P : (OrderDual {eps : ℝ // 0 < eps} × Finset {x : X // ‖x‖ = 1}) → (X →L[K] X),
      (∀ i, (P i).comp (P i) = P i ∧ ‖P i‖ ≤ 1 ∧ FiniteDimensional K (P i).range) ∧
      ∀ x, Tendsto (fun i => P i x) atTop (𝓝 x) := by
  classical
  constructor
  · intro h
    have hc : ∀ i : OrderDual {eps : ℝ // 0 < eps} × Finset {x : X // ‖x‖ = 1},
        ∃ P : X →L[K] X, P.comp P = P ∧ ‖P‖ ≤ 1 ∧ FiniteDimensional K P.range ∧
          ∀ x ∈ i.2.map (Function.Embedding.subtype _), ∃ y ∈ P.range, ‖x - y‖ < (OrderDual.ofDual i.1).1 := by
      intro i
      refine h _ (OrderDual.ofDual i.1).2 _ ?_
      intro x hx
      obtain ⟨x', _, rfl⟩ := Finset.mem_map.1 hx
      exact x'.2
    choose P hP1 hP2 hP3 hP4 using hc
    refine ⟨P, fun i => ⟨hP1 i, hP2 i, hP3 i⟩, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp only [map_zero]; exact tendsto_const_nhds
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    set u : {x : X // ‖x‖ = 1} := ⟨((‖x‖ : K))⁻¹ • x, by
      rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hx0, inv_mul_cancel₀ hx0.ne']⟩ with hu
    have hxu : x = ((‖x‖ : K)) • (u : X) := by
      simp only [hu]
      rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hx0.ne'), one_smul]
    rw [Metric.tendsto_nhds]
    intro ε hε
    set δ : ℝ := ε / (3 * ‖x‖) with hδ
    have hδ0 : 0 < δ := by positivity
    refine (Filter.eventually_ge_atTop (OrderDual.toDual (⟨δ, hδ0⟩ : {eps : ℝ // 0 < eps}),
      ({u} : Finset {x : X // ‖x‖ = 1}))).mono fun i hi => ?_
    have hεi : (OrderDual.ofDual i.1).1 ≤ δ := hi.1
    have hui : u ∈ i.2 := hi.2 (Finset.mem_singleton_self u)
    obtain ⟨y, ⟨w, rfl⟩, hy⟩ := hP4 i (u : X) (Finset.mem_map.2 ⟨u, hui, rfl⟩)
    have hPy : P i (P i w) = P i w := by
      have := congrArg (fun T : X →L[K] X => T w) (hP1 i)
      simpa using this
    have hb : ‖P i (u : X) - u‖ < 2 * δ := by
      have e : P i (u : X) - u = P i ((u : X) - P i w) - ((u : X) - P i w) := by
        rw [map_sub, hPy]; abel
      rw [e]
      calc ‖P i ((u : X) - P i w) - ((u : X) - P i w)‖
          ≤ ‖P i ((u : X) - P i w)‖ + ‖(u : X) - P i w‖ := norm_sub_le _ _
        _ ≤ ‖(u : X) - P i w‖ + ‖(u : X) - P i w‖ := by
            gcongr
            exact ((P i).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hP2 i))
        _ < (OrderDual.ofDual i.1).1 + (OrderDual.ofDual i.1).1 := add_lt_add hy hy
        _ ≤ 2 * δ := by linarith
    rw [dist_eq_norm, hxu, map_smul, ← smul_sub, norm_smul, RCLike.norm_ofReal, abs_of_pos hx0]
    calc ‖x‖ * ‖P i (u : X) - u‖ ≤ ‖x‖ * (2 * δ) := mul_le_mul_of_nonneg_left hb.le hx0.le
      _ = 2 * ε / 3 := by rw [hδ]; field_simp
      _ < ε := by linarith
  · rintro ⟨P, hP, hconv⟩ ε hε s hs
    have hev : ∀ᶠ i in atTop, ∀ x ∈ s, ‖x - P i x‖ < ε := by
      rw [Filter.eventually_all_finset]
      intro x _
      have := (Metric.tendsto_nhds.1 (hconv x)) ε hε
      refine this.mono fun i hi => ?_
      rwa [dist_eq_norm, norm_sub_rev] at hi
    haveI : Nonempty (OrderDual {eps : ℝ // 0 < eps} × Finset {x : X // ‖x‖ = 1}) :=
      ⟨(OrderDual.toDual ⟨1, one_pos⟩, ∅)⟩
    obtain ⟨i, hi⟩ := hev.exists
    exact ⟨P i, (hP i).1, (hP i).2.1, (hP i).2.2, fun x hx => ⟨P i x, ⟨x, rfl⟩, hi x hx⟩⟩

end Banach

end
