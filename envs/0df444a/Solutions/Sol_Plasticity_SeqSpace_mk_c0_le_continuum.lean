-- Prove2me | solution 1 for Plasticity.SeqSpace.mk_c0_le_continuum
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-11-18T19:27:12.71191+00:00
-- url     : https://prove2.me/submissions/c61700fc-9554-4b48-9de7-6b3bd2c785f7

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Analysis.Real.Cardinality

namespace Sol_Plasticity_SeqSpace_mk_c0_le_continuum
open Plasticity Filter Topology

lemma support_countable (Γ : Type*) (x : c0 Γ) : (Function.support (x : Γ → ℝ)).Countable := by
  have hx : Tendsto (⇑(x : Linf Γ)) cofinite (𝓝 0) := x.2
  have : Function.support (x : Γ → ℝ) = ⋃ n : ℕ, {i | (1 : ℝ) / (n + 1) ≤ |(x : Γ → ℝ) i|} := by
    ext i
    simp only [Function.mem_support, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro h
      have hp : 0 < |(x : Γ → ℝ) i| := abs_pos.mpr h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hp
      exact ⟨n, hn.le⟩
    · rintro ⟨n, hn⟩ h
      rw [h] at hn
      simp at hn
      have : (0:ℝ) < 1 / (n + 1) := by positivity
      linarith
  rw [this]
  refine Set.countable_iUnion fun n => Set.Finite.countable ?_
  have hpos : (0:ℝ) < 1 / (n + 1) := by positivity
  have h1 := hx (Metric.ball_mem_nhds (0:ℝ) hpos)
  rw [Filter.mem_map, Filter.mem_cofinite] at h1
  refine h1.subset ?_
  intro i hi
  simp only [Set.mem_setOf_eq] at hi
  simp [Set.mem_preimage, Metric.mem_ball]
  simpa using hi

end Sol_Plasticity_SeqSpace_mk_c0_le_continuum

theorem solution (Γ : Type*) (hΓ : Cardinal.mk Γ ≤ Cardinal.continuum) :
    Cardinal.mk (Plasticity.c0 Γ) ≤ Cardinal.continuum := by
  open Plasticity Sol_Plasticity_SeqSpace_mk_c0_le_continuum in
  rcases isEmpty_or_nonempty Γ with hE | hN
  · have : Subsingleton (c0 Γ) := ⟨fun a b => Subtype.ext (Subtype.ext (funext fun i => isEmptyElim i))⟩
    have : Cardinal.mk (c0 Γ) ≤ 1 := Cardinal.le_one_iff_subsingleton.mpr this
    exact this.trans (Cardinal.one_lt_aleph0.le.trans Cardinal.aleph0_le_continuum)
  · open Plasticity Sol_Plasticity_SeqSpace_mk_c0_le_continuum in
    obtain ⟨g0⟩ := hN
    have hc : ∀ x : c0 Γ, ∃ e : ℕ → Γ, Function.support (x : Γ → ℝ) ⊆ Set.range e := by
      intro x
      have hcnt : (insert g0 (Function.support (x : Γ → ℝ))).Countable :=
        (support_countable Γ x).insert g0
      obtain ⟨e, he⟩ := hcnt.exists_eq_range (Set.insert_nonempty _ _)
      exact ⟨e, fun i hi => he ▸ Set.mem_insert_of_mem _ hi⟩
    choose e he using hc
    let F : c0 Γ → (ℕ → Γ) × (ℕ → ℝ) := fun x => (e x, fun n => (x : Γ → ℝ) (e x n))
    have hF : Function.Injective F := by
      intro x y hxy
      simp only [F, Prod.mk.injEq] at hxy
      obtain ⟨h1, h2⟩ := hxy
      apply Subtype.ext; apply Subtype.ext; funext i
      by_cases hi : i ∈ Set.range (e x)
      · obtain ⟨n, rfl⟩ := hi
        have := congrFun h2 n
        rw [← h1] at this
        exact this
      · have hx0 : (x : Γ → ℝ) i = 0 := by
          by_contra h; exact hi (he x h)
        have hy0 : (y : Γ → ℝ) i = 0 := by
          by_contra h; exact hi (h1 ▸ he y h)
        rw [hx0, hy0]
    have := Cardinal.mk_le_of_injective hF
    refine this.trans ?_
    rw [Cardinal.mk_prod]
    simp only [Cardinal.mk_arrow, Cardinal.mk_real, Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_continuum]
    simp only [Cardinal.lift_power, Cardinal.lift_continuum, Cardinal.lift_aleph0, Cardinal.lift_id'.{0,u_1}, Cardinal.lift_id.{u_1}]
    have h1 : Cardinal.mk Γ ^ Cardinal.aleph0 ≤ Cardinal.continuum := by
      calc _ ≤ Cardinal.continuum ^ Cardinal.aleph0 := Cardinal.power_le_power_right hΓ
        _ = _ := Cardinal.continuum_power_aleph0
    have h2 : Cardinal.continuum ^ Cardinal.aleph0 = Cardinal.continuum := Cardinal.continuum_power_aleph0
    calc _ ≤ Cardinal.continuum * Cardinal.continuum := mul_le_mul' h1 h2.le
      _ = _ := Cardinal.continuum_mul_self
