-- Prove2me | solution 1 for Plasticity.C0Sum.eq_zero_of_map_eq_zero.comparison
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:51.99621+00:00
-- url     : https://prove2.me/submissions/31c731a1-1063-4f6c-a524-4ea5cd4c7d87

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
The comparison inequality of CUB100 Lemma 4.5: for `x` in the ball, a block `i` and an extreme
point `w` of its ball, `‖F(x)_i - w‖ ≤ max 1 ‖x_i - w‖`.

Given `ε > 0`, the finitely many blocks `h` with `‖x_h‖ ≥ ε` receive extreme points `e_h` within
one of `x_h`, block `i` receives `w`, and the other blocks zero. The preimage `p` of this point
has `p_i = w` and `p_h = e_h` by the normalization (U), so `‖p - x‖ ≤ max (1 + ε) ‖x_i - w‖`,
and `F` is nonexpansive. No continuity of `F` is needed.

The helpers `norm_c0Sum_le`, `norm_apply_le` and `finite_big` are copied from the project's
solution `Sol_Plasticity_C0Sum_isometryOn_of_support`.
-/

open Plasticity

namespace Sol_Plasticity_C0Sum_eq_zero_of_map_eq_zero_comparison

open Classical

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- The function equal to `g` on `S` and to zero elsewhere. -/
noncomputable def ofFunFun (S : Finset ι) (g : ∀ i, E i) : ∀ i, E i :=
  fun i => if i ∈ S then g i else 0

omit [∀ i, NormedSpace ℝ (E i)] in
lemma norm_ofFunFun_le (S : Finset ι) (g : ∀ i, E i) (i : ι) :
    ‖ofFunFun S g i‖ ≤ ∑ j ∈ S, ‖g j‖ := by
  unfold ofFunFun
  split_ifs with h
  · exact Finset.single_le_sum (f := fun j => ‖g j‖) (fun j _ => norm_nonneg _) h
  · rw [norm_zero]
    exact Finset.sum_nonneg (fun j _ => norm_nonneg _)

omit [∀ i, NormedSpace ℝ (E i)] in
lemma memℓp_ofFunFun (S : Finset ι) (g : ∀ i, E i) : Memℓp (ofFunFun S g) ⊤ := by
  refine memℓp_infty ⟨∑ j ∈ S, ‖g j‖, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact norm_ofFunFun_le S g i

lemma mem_c0Sum_ofFunFun (S : Finset ι) (g : ∀ i, E i) :
    (⟨ofFunFun S g, memℓp_ofFunFun S g⟩ : lp E ⊤) ∈ c0Sum E := by
  show Filter.Tendsto (fun i => ‖ofFunFun S g i‖) Filter.cofinite (nhds 0)
  refine tendsto_nhds_of_eventually_eq ?_
  refine Filter.eventually_cofinite.2 (S.finite_toSet.subset ?_)
  intro i hi
  by_contra h
  have h' : i ∉ S := fun h'' => h (Finset.mem_coe.2 h'')
  exact hi (by simp [ofFunFun, h'])

/-- The point of `c0Sum E` with blocks `g` on `S` and zero elsewhere. -/
noncomputable def ofFun (S : Finset ι) (g : ∀ i, E i) : c0Sum E :=
  ⟨⟨ofFunFun S g, memℓp_ofFunFun S g⟩, mem_c0Sum_ofFunFun S g⟩

lemma ofFun_apply (S : Finset ι) (g : ∀ i, E i) (i : ι) :
    ((ofFun S g : c0Sum E) : lp E ⊤) i = if i ∈ S then g i else 0 := rfl

lemma norm_c0Sum_le {x : c0Sum E} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖(x : lp E ⊤) i‖ ≤ C) :
    ‖x‖ ≤ C := by
  rw [Submodule.coe_norm]
  exact lp.norm_le_of_forall_le hC h

lemma norm_apply_le (x : c0Sum E) (i : ι) : ‖(x : lp E ⊤) i‖ ≤ ‖x‖ := by
  rw [Submodule.coe_norm]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ i

lemma finite_big (x : c0Sum E) {ε : ℝ} (hε : 0 < ε) :
    {i | ¬ ‖(x : lp E ⊤) i‖ < ε}.Finite := by
  have hx : Filter.Tendsto (fun i => ‖(x : lp E ⊤) i‖) Filter.cofinite (nhds 0) := x.2
  exact Filter.eventually_cofinite.1 (hx.eventually_lt_const hε)

end Sol_Plasticity_C0Sum_eq_zero_of_map_eq_zero_comparison

open Sol_Plasticity_C0Sum_eq_zero_of_map_eq_zero_comparison in
theorem solution {ι : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (hcov : ∀ i, ∀ b : E i, ‖b‖ ≤ 1 → b ≠ 0 →
      ∃ e ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1), ‖b - e‖ ≤ 1)
    (F : c0Sum E → c0Sum E)
    (hsurj : Set.SurjOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (hext : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      (F x : lp E ⊤) i ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1) →
        (x : lp E ⊤) i = (F x : lp E ⊤) i)
    (x : c0Sum E) (hx : x ∈ Metric.closedBall (0 : c0Sum E) 1) (i : ι)
    (w : E i) (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)) :
    ‖(F x : lp E ⊤) i - w‖ ≤ max 1 ‖(x : lp E ⊤) i - w‖ := by
  classical
  have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hx
  refine le_of_forall_pos_le_add fun ε hε => ?_
  choose! e he hxe using fun h (hh : (x : lp E ⊤) h ≠ 0) =>
    hcov h ((x : lp E ⊤) h) ((norm_apply_le x h).trans hx1) hh
  set S : Finset ι := insert i (finite_big x hε).toFinset with hS
  have hSne : ∀ h ∈ S, h ≠ i → (x : lp E ⊤) h ≠ 0 := by
    intro h hh hhi h0
    rcases Finset.mem_insert.1 hh with rfl | hh
    · exact hhi rfl
    · have := (Set.Finite.mem_toFinset _).1 hh
      simp only [Set.mem_ofPred_eq, h0, norm_zero, not_lt] at this
      linarith
  set g : ∀ h, E h := Function.update e i w with hg
  have hgi : g i = w := by rw [hg, Function.update_self]
  have hgh : ∀ h, h ≠ i → g h = e h := fun h hh => by rw [hg, Function.update_of_ne hh]
  have hgext : ∀ h ∈ S, g h ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E h) 1) := by
    intro h hhS
    by_cases hh : h = i
    · subst hh; rw [hgi]; exact hw
    · rw [hgh h hh]; exact he h (hSne h hhS hh)
  set y : c0Sum E := ofFun S g with hy
  have hyB : y ∈ Metric.closedBall (0 : c0Sum E) 1 := by
    rw [mem_closedBall_zero_iff]
    refine norm_c0Sum_le zero_le_one fun h => ?_
    rw [hy, ofFun_apply]
    split_ifs with hhS
    · exact mem_closedBall_zero_iff.1 (hgext h hhS).1
    · simp
  obtain ⟨p, hp, hFp⟩ := hsurj hyB
  have hpS : ∀ h ∈ S, (p : lp E ⊤) h = g h := by
    intro h hh
    have hFph : (F p : lp E ⊤) h = g h := by rw [hFp, hy, ofFun_apply, if_pos hh]
    rw [hext p hp h (by rw [hFph]; exact hgext h hh), hFph]
  have hpi : (p : lp E ⊤) i = w := by rw [hpS i (Finset.mem_insert_self _ _), hgi]
  have hFpi : (F p : lp E ⊤) i = w := by
    rw [hFp, hy, ofFun_apply, if_pos (Finset.mem_insert_self _ _), hgi]
  have hdist : ‖x - p‖ ≤ max 1 ‖(x : lp E ⊤) i - w‖ + ε := by
    refine norm_c0Sum_le (by positivity) fun h => ?_
    rw [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply]
    by_cases hhi : h = i
    · subst hhi
      rw [hpi]
      linarith [le_max_right 1 ‖(x : lp E ⊤) h - w‖]
    by_cases hhS : h ∈ S
    · rw [hpS h hhS, hgh h hhi]
      linarith [hxe h (hSne h hhS hhi), le_max_left 1 ‖(x : lp E ⊤) i - w‖]
    · have hsmall : ‖(x : lp E ⊤) h‖ < ε := by
        by_contra hc
        exact hhS (Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 hc))
      have hp1 : ‖(p : lp E ⊤) h‖ ≤ 1 :=
        (norm_apply_le p h).trans (mem_closedBall_zero_iff.1 hp)
      calc ‖(x : lp E ⊤) h - (p : lp E ⊤) h‖ ≤ ‖(x : lp E ⊤) h‖ + ‖(p : lp E ⊤) h‖ :=
            norm_sub_le _ _
        _ ≤ max 1 ‖(x : lp E ⊤) i - w‖ + ε := by
            linarith [le_max_left 1 ‖(x : lp E ⊤) i - w‖]
  have hlipxp : ‖F x - F p‖ ≤ ‖x - p‖ := by
    simpa [dist_eq_norm] using hlip.dist_le_mul x hx p hp
  calc ‖(F x : lp E ⊤) i - w‖ = ‖((F x - F p : c0Sum E) : lp E ⊤) i‖ := by
        rw [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, hFpi]
    _ ≤ ‖F x - F p‖ := norm_apply_le _ i
    _ ≤ max 1 ‖(x : lp E ⊤) i - w‖ + ε := hlipxp.trans hdist
