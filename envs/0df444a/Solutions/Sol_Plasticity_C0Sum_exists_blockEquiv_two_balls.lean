-- Prove2me | solution 1 for Plasticity.C0Sum.exists_blockEquiv_two_balls
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:04:01.533216+00:00
-- url     : https://prove2.me/submissions/2524742f-c584-4b6c-89bd-f1e0b153a922

import Definitions.Def_Plasticity_C0Sum
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Theorems.Thm_Plasticity_Plane_closedBall_subset_union_two_iff

/-!
Two unit balls covering the ball of a c₀ sum of lines and planes (CUB93 Lemma 2.1, CUB99(1)).

The c₀-sum helpers `norm_c0Sum_le`, `norm_apply_le`, `c0_ext`, `ofFun`, `sg` are copied from the
project's solution `Solutions/Sol_Plasticity_C0Sum_exists_extremeRule.lean`.
-/

open Plasticity

namespace Sol_Plasticity_C0Sum_exists_blockEquiv_two_balls

open Classical

section C0

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

lemma norm_c0Sum_le {x : c0Sum E} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖(x : lp E ⊤) i‖ ≤ C) :
    ‖x‖ ≤ C := by
  rw [Submodule.coe_norm]
  exact lp.norm_le_of_forall_le hC h

lemma norm_apply_le (x : c0Sum E) (i : ι) : ‖(x : lp E ⊤) i‖ ≤ ‖x‖ := by
  rw [Submodule.coe_norm]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ i

lemma c0_ext {x y : c0Sum E} (h : ∀ m, (x : lp E ⊤) m = (y : lp E ⊤) m) : x = y :=
  Subtype.ext (lp.ext (funext h))

/-- The function with blocks `f m` on a finite set `S` and zero elsewhere. -/
noncomputable def ofFunFun (S : Finset ι) (f : ∀ m, E m) : ∀ m, E m :=
  fun m => if m ∈ S then f m else 0

omit [∀ i, NormedSpace ℝ (E i)] in
lemma norm_ofFunFun_le (S : Finset ι) (f : ∀ m, E m) (m : ι) :
    ‖ofFunFun S f m‖ ≤ ∑ n ∈ S, ‖f n‖ := by
  unfold ofFunFun
  split_ifs with h
  · exact Finset.single_le_sum (f := fun n => ‖f n‖) (fun n _ => norm_nonneg _) h
  · rw [norm_zero]
    exact Finset.sum_nonneg fun n _ => norm_nonneg _

omit [∀ i, NormedSpace ℝ (E i)] in
lemma memℓp_ofFunFun (S : Finset ι) (f : ∀ m, E m) : Memℓp (ofFunFun S f) ⊤ := by
  refine memℓp_infty ⟨∑ n ∈ S, ‖f n‖, ?_⟩
  rintro _ ⟨m, rfl⟩
  exact norm_ofFunFun_le S f m

lemma mem_c0Sum_ofFunFun (S : Finset ι) (f : ∀ m, E m) :
    (⟨ofFunFun S f, memℓp_ofFunFun S f⟩ : lp E ⊤) ∈ c0Sum E := by
  show Filter.Tendsto (fun m => ‖ofFunFun S f m‖) Filter.cofinite (nhds 0)
  refine tendsto_nhds_of_eventually_eq ?_
  refine Filter.eventually_cofinite.2 (S.finite_toSet.subset ?_)
  intro m hm
  by_contra h
  have h' : m ∉ S := fun h'' => h (Finset.mem_coe.2 h'')
  exact hm (by simp [ofFunFun, h'])

/-- The point of `c0Sum E` with blocks `f m` on `S` and zero elsewhere. -/
noncomputable def ofFun (S : Finset ι) (f : ∀ m, E m) : c0Sum E :=
  ⟨⟨ofFunFun S f, memℓp_ofFunFun S f⟩, mem_c0Sum_ofFunFun S f⟩

lemma ofFun_apply (S : Finset ι) (f : ∀ m, E m) (m : ι) :
    ((ofFun S f : c0Sum E) : lp E ⊤) m = if m ∈ S then f m else 0 := rfl

lemma norm_ofFun_le (S : Finset ι) (f : ∀ m, E m) (hf : ∀ m, ‖f m‖ ≤ 1) :
    ‖ofFun S f‖ ≤ 1 := by
  refine norm_c0Sum_le zero_le_one fun m => ?_
  rw [ofFun_apply]
  split_ifs
  · exact hf m
  · simp

/-- The point of `c0Sum E` with block `a` at `j` and zero elsewhere. -/
noncomputable def sg (j : ι) (a : E j) : c0Sum E := ofFun {j} (Function.update 0 j a)

lemma sg_self (j : ι) (a : E j) : ((sg j a : c0Sum E) : lp E ⊤) j = a := by
  simp [sg, ofFun_apply]

lemma sg_ne {j m : ι} (a : E j) (h : m ≠ j) : ((sg j a : c0Sum E) : lp E ⊤) m = 0 := by
  simp [sg, ofFun_apply, h]

lemma norm_sg_le (j : ι) (a : E j) : ‖sg j a‖ ≤ ‖a‖ := by
  refine norm_c0Sum_le (norm_nonneg _) fun m => ?_
  by_cases h : m = j
  · subst h; rw [sg_self]
  · rw [sg_ne a h, norm_zero]; exact norm_nonneg _

lemma exists_ne_zero_of_ne_zero {x : c0Sum E} (hx : x ≠ 0) : ∃ m, (x : lp E ⊤) m ≠ 0 := by
  by_contra h
  push Not at h
  exact hx (c0_ext fun m => by simp [h m])

/-- Killing for two balls. -/
lemma kill2 (q₀ q₁ : c0Sum E)
    (hcov : Metric.closedBall (0 : c0Sum E) 1 ⊆ Metric.closedBall q₀ 1 ∪ Metric.closedBall q₁ 1)
    (n₀ n₁ : ι) (u : ∀ m, E m) (hu : ∀ m, ‖u m‖ ≤ 1)
    (h₀ : 1 < ‖u n₀ - (q₀ : lp E ⊤) n₀‖) (h₁ : 1 < ‖u n₁ - (q₁ : lp E ⊤) n₁‖) : False := by
  set y := ofFun {n₀, n₁} u
  have hy := hcov (mem_closedBall_zero_iff.2 (norm_ofFun_le {n₀, n₁} u hu))
  rcases hy with h | h <;> rw [Metric.mem_closedBall, dist_eq_norm] at h
  · have := norm_apply_le (y - q₀) n₀
    simp only [y, Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, ofFun_apply] at this
    rw [if_pos (by simp)] at this
    linarith
  · have := norm_apply_le (y - q₁) n₁
    simp only [y, Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, ofFun_apply] at this
    rw [if_pos (by simp)] at this
    linarith

end C0

section Block

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The antipode `-v/‖v‖` of a nonzero vector. -/
noncomputable def antipode (v : W) : W := -(‖v‖⁻¹ • v)

lemma norm_antipode_le (v : W) : ‖antipode v‖ ≤ 1 := by
  unfold antipode
  rw [norm_neg, norm_smul, norm_inv, norm_norm]
  rcases eq_or_ne ‖v‖ 0 with h | h
  · rw [h]; simp
  · rw [inv_mul_cancel₀ h]

/-- The antipode of `v` is farther than one from every positive multiple of `v`. -/
lemma one_lt_norm_antipode_sub {v : W} (hv : v ≠ 0) {c : ℝ} (hc : 0 < c) :
    1 < ‖antipode v - c • v‖ := by
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  unfold antipode
  have : -(‖v‖⁻¹ • v) - c • v = -((‖v‖⁻¹ + c) • v) := by module
  rw [this, norm_neg, norm_smul, Real.norm_of_nonneg (by positivity), add_mul,
    inv_mul_cancel₀ hn.ne']
  have : 0 < c * ‖v‖ := by positivity
  linarith

lemma one_lt_norm_antipode_sub_self {v : W} (hv : v ≠ 0) : 1 < ‖antipode v - v‖ := by
  simpa using one_lt_norm_antipode_sub hv one_pos

/-- Two unit balls about nonzero points of a line or a plane cover its ball only if the points
are opposite. -/
theorem exists_neg_smul_of_cover (hW : Module.finrank ℝ W = 1 ∨ Module.finrank ℝ W = 2)
    {p p' : W} (hp : p ≠ 0) (hp' : p' ≠ 0)
    (hcov : Metric.closedBall (0 : W) 1 ⊆ Metric.closedBall p 1 ∪ Metric.closedBall p' 1) :
    ∃ μ : ℝ, 0 < μ ∧ p' = -(μ • p) := by
  rcases hW with hW | hW
  · obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' p hp).1 hW p'
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hp' (by rw [← hc, zero_smul])
    rcases lt_or_gt_of_ne hc0 with hneg | hpos
    · exact ⟨-c, by linarith, by rw [← hc, neg_smul, neg_neg]⟩
    · exfalso
      have hmem := hcov (mem_closedBall_zero_iff.2 (norm_antipode_le p))
      rcases hmem with h | h
      · rw [Metric.mem_closedBall, dist_eq_norm] at h
        linarith [one_lt_norm_antipode_sub_self hp]
      · rw [Metric.mem_closedBall, dist_eq_norm, ← hc] at h
        linarith [one_lt_norm_antipode_sub hp hpos]
  · obtain ⟨f, _, a, b, _, _, _, _, t, s, ht, hs, _, hu, hv⟩ :=
      (Plasticity.Plane.closedBall_subset_union_two_iff hW p p' hp hp').1 hcov
    refine ⟨s / t, div_pos hs ht, ?_⟩
    rw [hv, hu, smul_smul, div_mul_cancel₀ s ht.ne']

end Block

end Sol_Plasticity_C0Sum_exists_blockEquiv_two_balls

open Sol_Plasticity_C0Sum_exists_blockEquiv_two_balls in
theorem solution {κ : Type*}
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
    (p q : c0Sum E') (hp : p ≠ 0) (hq : q ≠ 0)
    (hcov : Metric.closedBall (0 : c0Sum E') 1 ⊆ Metric.closedBall p 1 ∪ Metric.closedBall q 1) :
    ∃ m : κ, (∀ k ≠ m, (p : lp E' ⊤) k = 0 ∧ (q : lp E' ⊤) k = 0) ∧
      ∃ μ : ℝ, 0 < μ ∧ (q : lp E' ⊤) m = -(μ • (p : lp E' ⊤) m) := by
  classical
  -- all nonzero blocks of `p` and of `q` coincide
  have hsame : ∀ m n, (p : lp E' ⊤) m ≠ 0 → (q : lp E' ⊤) n ≠ 0 → m = n := by
    intro m n hm hn
    by_contra hmn
    refine kill2 p q hcov m n
      (Function.update (Function.update 0 m (antipode ((p : lp E' ⊤) m))) n
        (antipode ((q : lp E' ⊤) n))) ?_ ?_ ?_
    · intro k
      by_cases hk : k = n
      · subst hk; simp [norm_antipode_le]
      · rw [Function.update_of_ne hk]
        by_cases hk' : k = m
        · subst hk'; simp [norm_antipode_le]
        · simp [Function.update_of_ne hk']
    · rw [Function.update_of_ne hmn, Function.update_self]
      exact one_lt_norm_antipode_sub_self hm
    · rw [Function.update_self]
      exact one_lt_norm_antipode_sub_self hn
  obtain ⟨m, hm⟩ := exists_ne_zero_of_ne_zero hp
  obtain ⟨n, hn⟩ := exists_ne_zero_of_ne_zero hq
  obtain rfl := hsame m n hm hn
  refine ⟨m, fun k hk => ⟨?_, ?_⟩, ?_⟩
  · by_contra h
    exact hk (hsame k m h hn)
  · by_contra h
    exact hk (hsame m k hm h).symm
  · refine exists_neg_smul_of_cover (hE' m) hm hn fun u hu => ?_
    rw [mem_closedBall_zero_iff] at hu
    have hy : sg m u ∈ Metric.closedBall (0 : c0Sum E') 1 :=
      mem_closedBall_zero_iff.2 ((norm_sg_le m u).trans hu)
    rcases hcov hy with h | h
    · left
      rw [Metric.mem_closedBall, dist_eq_norm] at h ⊢
      have := (norm_apply_le (sg m u - p) m).trans h
      simpa [sg_self] using this
    · right
      rw [Metric.mem_closedBall, dist_eq_norm] at h ⊢
      have := (norm_apply_le (sg m u - q) m).trans h
      simpa [sg_self] using this
