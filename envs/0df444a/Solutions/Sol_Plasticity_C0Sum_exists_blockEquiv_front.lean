-- Prove2me | solution 1 for Plasticity.C0Sum.exists_blockEquiv_front
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:56.388054+00:00
-- url     : https://prove2.me/submissions/17b82031-a6d7-4629-bd27-e2edde50ca74

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_Plane_closedBall_subset_union_two_iff
import Theorems.Thm_Plasticity_Plane_corner_cover
import Theorems.Thm_Plasticity_Plane_exists_corner_of_bad
import Theorems.Thm_Plasticity_Plane_exists_open_completions
import Theorems.Thm_Plasticity_Topology_isOpen_image_of_injOn_of_finrank_eq
import Theorems.Thm_Plasticity_BallMap_map_zero_of_surjOn
import Theorems.Thm_Plasticity_C0Sum_exists_blockEquiv_two_balls
import Theorems.Thm_Plasticity_C0Sum_exists_blockEquiv_three_balls

/-!
The front for planar source blocks (CUB103 §3, with the simplifications of the formalization:
genericity off finitely many lines instead of tangent points and Baire's theorem).

The c₀-sum helpers `norm_c0Sum_le`, `norm_apply_le`, `c0_ext`, `ofFun`, `sg` are copied from the
project's solution `Solutions/Sol_Plasticity_C0Sum_exists_extremeRule.lean`.
-/

open Plasticity

namespace Sol_Plasticity_C0Sum_exists_blockEquiv_front

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

/-- Killing for three balls. -/
lemma kill3 (q₀ q₁ q₂ : c0Sum E)
    (hcov : Metric.closedBall (0 : c0Sum E) 1 ⊆
      Metric.closedBall q₀ 1 ∪ Metric.closedBall q₁ 1 ∪ Metric.closedBall q₂ 1)
    (n₀ n₁ n₂ : ι) (u : ∀ m, E m) (hu : ∀ m, ‖u m‖ ≤ 1)
    (h₀ : 1 < ‖u n₀ - (q₀ : lp E ⊤) n₀‖) (h₁ : 1 < ‖u n₁ - (q₁ : lp E ⊤) n₁‖)
    (h₂ : 1 < ‖u n₂ - (q₂ : lp E ⊤) n₂‖) : False := by
  set y := ofFun {n₀, n₁, n₂} u
  have hy := hcov (mem_closedBall_zero_iff.2 (norm_ofFun_le {n₀, n₁, n₂} u hu))
  rcases hy with (h | h) | h <;> rw [Metric.mem_closedBall, dist_eq_norm] at h
  · have := norm_apply_le (y - q₀) n₀
    simp only [y, Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, ofFun_apply] at this
    rw [if_pos (by simp)] at this
    linarith
  · have := norm_apply_le (y - q₁) n₁
    simp only [y, Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, ofFun_apply] at this
    rw [if_pos (by simp)] at this
    linarith
  · have := norm_apply_le (y - q₂) n₂
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

/-- Two nonzero points of a line or a plane that are not opposite can be killed by one point. -/
theorem exists_far_of_not_neg (hW : Module.finrank ℝ W = 1 ∨ Module.finrank ℝ W = 2)
    {p p' : W} (hp : p ≠ 0) (hp' : p' ≠ 0) (hnot : ¬ ∃ μ : ℝ, 0 < μ ∧ p' = -(μ • p)) :
    ∃ u : W, ‖u‖ ≤ 1 ∧ 1 < ‖u - p‖ ∧ 1 < ‖u - p'‖ := by
  by_contra hcon
  push Not at hcon
  refine hnot (exists_neg_smul_of_cover hW hp hp' fun u hu => ?_)
  rw [mem_closedBall_zero_iff] at hu
  by_cases h : ‖u - p‖ ≤ 1
  · left; rwa [Metric.mem_closedBall, dist_eq_norm]
  · right; rw [Metric.mem_closedBall, dist_eq_norm]; exact hcon u hu (lt_of_not_ge h)

end Block


section Three

variable {κ : Type*} {E' : κ → Type*} [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]

/-- `p'` is a negative multiple of `p`. -/
def Opp {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (p p' : W) : Prop :=
  ∃ μ : ℝ, 0 < μ ∧ p' = -(μ • p)

/-- Covering by three balls, in a form symmetric under permutations. -/
def Cov3 (A B C : c0Sum E') : Prop :=
  ∀ y : c0Sum E', ‖y‖ ≤ 1 → ‖y - A‖ ≤ 1 ∨ ‖y - B‖ ≤ 1 ∨ ‖y - C‖ ≤ 1

lemma kill3' {A B C : c0Sum E'} (hcov : Cov3 A B C)
    (n₀ n₁ n₂ : κ) (u : ∀ m, E' m) (hu : ∀ m, ‖u m‖ ≤ 1)
    (h₀ : 1 < ‖u n₀ - (A : lp E' ⊤) n₀‖) (h₁ : 1 < ‖u n₁ - (B : lp E' ⊤) n₁‖)
    (h₂ : 1 < ‖u n₂ - (C : lp E' ⊤) n₂‖) : False := by
  refine kill3 A B C (fun y hy => ?_) n₀ n₁ n₂ u hu h₀ h₁ h₂
  rcases hcov y (mem_closedBall_zero_iff.1 hy) with h | h | h
  · left; left; rwa [Metric.mem_closedBall, dist_eq_norm]
  · left; right; rwa [Metric.mem_closedBall, dist_eq_norm]
  · right; rwa [Metric.mem_closedBall, dist_eq_norm]

lemma single3 {A B C : c0Sum E'} (hcov : Cov3 A B C) {n₀ n₁ n₂ : κ}
    (h₀ : (A : lp E' ⊤) n₀ ≠ 0) (h₁ : (B : lp E' ⊤) n₁ ≠ 0) (h₂ : (C : lp E' ⊤) n₂ ≠ 0)
    (h01 : n₀ ≠ n₁) (h02 : n₀ ≠ n₂) (h12 : n₁ ≠ n₂) : False := by
  refine kill3' hcov n₀ n₁ n₂
    (Function.update (Function.update (Function.update 0 n₀ (antipode ((A : lp E' ⊤) n₀))) n₁
      (antipode ((B : lp E' ⊤) n₁))) n₂ (antipode ((C : lp E' ⊤) n₂))) ?_ ?_ ?_ ?_
  · intro k
    by_cases hk2 : k = n₂
    · subst hk2; simp [norm_antipode_le]
    rw [Function.update_of_ne hk2]
    by_cases hk1 : k = n₁
    · subst hk1; simp [norm_antipode_le]
    rw [Function.update_of_ne hk1]
    by_cases hk0 : k = n₀
    · subst hk0; simp [norm_antipode_le]
    simp [Function.update_of_ne hk0]
  · rw [Function.update_of_ne h02, Function.update_of_ne h01, Function.update_self]
    exact one_lt_norm_antipode_sub_self h₀
  · rw [Function.update_of_ne h12, Function.update_self]
    exact one_lt_norm_antipode_sub_self h₁
  · rw [Function.update_self]
    exact one_lt_norm_antipode_sub_self h₂

lemma pair3 (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
    {A B C : c0Sum E'} (hcov : Cov3 A B C) {n n' : κ} (hnn' : n ≠ n')
    (hA : (A : lp E' ⊤) n ≠ 0) (hB : (B : lp E' ⊤) n ≠ 0)
    (hAB : ¬ Opp ((A : lp E' ⊤) n) ((B : lp E' ⊤) n)) (hC : (C : lp E' ⊤) n' ≠ 0) : False := by
  obtain ⟨u₀, hu₀, h1, h2⟩ := exists_far_of_not_neg (hE' n) hA hB hAB
  refine kill3' hcov n n n'
    (Function.update (Function.update 0 n u₀) n' (antipode ((C : lp E' ⊤) n'))) ?_ ?_ ?_ ?_
  · intro k
    by_cases hk2 : k = n'
    · subst hk2; simp [norm_antipode_le]
    rw [Function.update_of_ne hk2]
    by_cases hk1 : k = n
    · subst hk1; simpa using hu₀
    simp [Function.update_of_ne hk1]
  · rw [Function.update_of_ne hnn', Function.update_self]; exact h1
  · rw [Function.update_of_ne hnn', Function.update_self]; exact h2
  · rw [Function.update_self]
    exact one_lt_norm_antipode_sub_self hC

lemma cov3_swap23 {A B C : c0Sum E'} (h : Cov3 A B C) : Cov3 A C B := by
  intro y hy; rcases h y hy with h | h | h <;> tauto

end Three

/-! ### The block map of a planar source block -/

section Front

variable {ι κ : Type*}
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {E' : κ → Type*} [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]

lemma sg_sub (j : ι) (a b : E j) : sg j a - sg j b = (sg j (a - b) : c0Sum E) := by
  refine c0_ext fun m => ?_
  by_cases h : m = j
  · subst h; simp [sg_self]
  · simp [sg_ne _ h]

lemma sg_zero (j : ι) : (sg j (0 : E j) : c0Sum E) = 0 :=
  c0_ext fun m => by
    by_cases h : m = j
    · subst h; simp [sg_self]
    · simp [sg_ne _ h]

lemma sg_injective (j : ι) : Function.Injective (sg j : E j → c0Sum E) := by
  intro a b h
  have := congrArg (fun x : c0Sum E => (x : lp E ⊤) j) h
  simpa [sg_self] using this

lemma sg_mem {j : ι} {a : E j} (ha : ‖a‖ ≤ 1) : sg j a ∈ Metric.closedBall (0 : c0Sum E) 1 :=
  mem_closedBall_zero_iff.2 ((norm_sg_le j a).trans ha)

/-- Points supported in one block have the norm of that block. -/
lemma norm_eq_of_supp {x : c0Sum E} {m : ι} (hx : ∀ k ≠ m, (x : lp E ⊤) k = 0) :
    ‖x‖ = ‖(x : lp E ⊤) m‖ := by
  refine le_antisymm (norm_c0Sum_le (norm_nonneg _) fun k => ?_) (norm_apply_le x m)
  by_cases h : k = m
  · subst h; exact le_rfl
  · rw [hx k h, norm_zero]; exact norm_nonneg _

lemma continuous_eval (m : ι) : Continuous fun x : c0Sum E => (x : lp E ⊤) m := by
  refine (LipschitzWith.of_dist_le_mul fun x y => ?_).continuous (K := 1)
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  have := norm_apply_le (x - y) m
  simpa using this

/-- A line through `0` in block `m`. -/
def Line (m : ι) (v : E m) : Set (c0Sum E) :=
  {y | (∀ k ≠ m, (y : lp E ⊤) k = 0) ∧ ∃ t : ℝ, (y : lp E ⊤) m = t • v}

lemma isClosed_line [∀ k, FiniteDimensional ℝ (E k)] (m : ι) (v : E m) :
    IsClosed (Line m v) := by
  have h1 : IsClosed {y : c0Sum E | ∀ k ≠ m, (y : lp E ⊤) k = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun _ =>
      isClosed_eq (continuous_eval k) continuous_const
  have h2 : IsClosed {y : c0Sum E | ∃ t : ℝ, (y : lp E ⊤) m = t • v} := by
    have : {y : c0Sum E | ∃ t : ℝ, (y : lp E ⊤) m = t • v} =
        (fun y : c0Sum E => (y : lp E ⊤) m) ⁻¹' ((ℝ ∙ v : Submodule ℝ (E m)) : Set (E m)) := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe,
        Submodule.mem_span_singleton]
      exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩
    rw [this]
    exact (Submodule.closed_of_finiteDimensional _).preimage (continuous_eval m)
  exact h1.inter h2

end Front

/-! ### The block map `a ↦ F (sg i a)` -/

section Ctx

variable {ι κ : Type*}
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {E' : κ → Type*} [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
  (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
  {F : c0Sum E → c0Sum E'}
  (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
  (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
  {i : ι} (hi : Module.finrank ℝ (E i) = 2)

include hE' in
lemma fd' (k : κ) : FiniteDimensional ℝ (E' k) :=
  Module.finite_of_finrank_pos (by rcases hE' k with h | h <;> omega)

include hi in
lemma fdi : FiniteDimensional ℝ (E i) := Module.finite_of_finrank_eq_succ hi

include hbij hlip in
lemma map_zero : F 0 = 0 := Plasticity.BallMap.map_zero_of_surjOn F hbij.surjOn hlip

include hlip in
lemma phi_lip {a b : E i} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖F (sg i a) - F (sg i b)‖ ≤ ‖a - b‖ := by
  have := hlip.norm_sub_le (sg_mem ha) (sg_mem hb)
  rw [NNReal.coe_one, one_mul, sg_sub] at this
  exact this.trans (norm_sg_le _ _)

include hlip in
lemma phi_cont : ContinuousOn (fun a : E i => F (sg i a)) (Metric.closedBall 0 1) := by
  intro a ha
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε, hε, fun b hb hab => ?_⟩
  rw [dist_eq_norm] at hab ⊢
  exact (phi_lip hlip (mem_closedBall_zero_iff.1 hb) (mem_closedBall_zero_iff.1 ha)).trans_lt hab

include hbij in
lemma phi_injOn : Set.InjOn (fun a : E i => F (sg i a)) (Metric.closedBall 0 1) := by
  intro a ha b hb h
  exact sg_injective i (hbij.injOn (sg_mem (mem_closedBall_zero_iff.1 ha))
    (sg_mem (mem_closedBall_zero_iff.1 hb)) h)

include hbij hlip in
lemma phi_ne_zero {a : E i} (ha : ‖a‖ ≤ 1) (ha0 : a ≠ 0) : F (sg i a) ≠ 0 := by
  intro h
  have h0 : F (sg i (0 : E i)) = 0 := by rw [sg_zero, map_zero hbij hlip]
  exact ha0 (phi_injOn hbij (mem_closedBall_zero_iff.2 ha)
    (mem_closedBall_zero_iff.2 (by simp)) (h.trans h0.symm))

include hbij in
/-- A cover of the ball of block `i` by unit balls lifts to a cover of the target ball. -/
lemma cover_lift {y : c0Sum E'} (hy : ‖y‖ ≤ 1)
    {P : E i → Prop} (hcov : ∀ z : E i, ‖z‖ ≤ 1 → P z) :
    ∃ x ∈ Metric.closedBall (0 : c0Sum E) 1, F x = y ∧ P ((x : lp E ⊤) i) := by
  obtain ⟨x, hx, rfl⟩ := hbij.surjOn (mem_closedBall_zero_iff.2 hy)
  exact ⟨x, hx, rfl, hcov _ ((norm_apply_le x i).trans (mem_closedBall_zero_iff.1 hx))⟩

include hlip in
lemma norm_sub_phi_le {x : c0Sum E} (hx : x ∈ Metric.closedBall (0 : c0Sum E) 1) {c : E i}
    (hc : ‖c‖ ≤ 1) (hxc : ‖(x : lp E ⊤) i - c‖ ≤ 1) : ‖F x - F (sg i c)‖ ≤ 1 := by
  have h1 : ‖x - sg i c‖ ≤ 1 := by
    refine norm_c0Sum_le zero_le_one fun k => ?_
    by_cases hk : k = i
    · subst hk; simpa [sg_self] using hxc
    · simpa [sg_ne _ hk] using (norm_apply_le x k).trans (mem_closedBall_zero_iff.1 hx)
  have := hlip.norm_sub_le hx (sg_mem hc)
  rw [NNReal.coe_one, one_mul] at this
  exact this.trans h1

include hbij hlip in
lemma cover_lift2 {a b : E i} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hcov : Metric.closedBall (0 : E i) 1 ⊆ Metric.closedBall a 1 ∪ Metric.closedBall b 1) :
    Metric.closedBall (0 : c0Sum E') 1 ⊆
      Metric.closedBall (F (sg i a)) 1 ∪ Metric.closedBall (F (sg i b)) 1 := by
  intro y hy
  obtain ⟨x, hx, rfl, hP⟩ := cover_lift hbij (mem_closedBall_zero_iff.1 hy)
    (P := fun z => ‖z - a‖ ≤ 1 ∨ ‖z - b‖ ≤ 1) (fun z hz => by
      have := hcov (mem_closedBall_zero_iff.2 hz)
      simpa [Metric.mem_closedBall, dist_eq_norm] using this)
  rcases hP with h | h
  · left; rw [Metric.mem_closedBall, dist_eq_norm]; exact norm_sub_phi_le hlip hx ha h
  · right; rw [Metric.mem_closedBall, dist_eq_norm]; exact norm_sub_phi_le hlip hx hb h

include hbij hlip in
lemma cover_lift3 {a b c : E i} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (hcov : Metric.closedBall (0 : E i) 1 ⊆
      Metric.closedBall a 1 ∪ Metric.closedBall b 1 ∪ Metric.closedBall c 1) :
    Metric.closedBall (0 : c0Sum E') 1 ⊆ Metric.closedBall (F (sg i a)) 1 ∪
      Metric.closedBall (F (sg i b)) 1 ∪ Metric.closedBall (F (sg i c)) 1 := by
  intro y hy
  obtain ⟨x, hx, rfl, hP⟩ := cover_lift hbij (mem_closedBall_zero_iff.1 hy)
    (P := fun z => ‖z - a‖ ≤ 1 ∨ ‖z - b‖ ≤ 1 ∨ ‖z - c‖ ≤ 1) (fun z hz => by
      have := hcov (mem_closedBall_zero_iff.2 hz)
      simp only [Set.mem_union, Metric.mem_closedBall, dist_eq_norm] at this
      tauto)
  simp only [Set.mem_union, Metric.mem_closedBall, dist_eq_norm]
  rcases hP with h | h | h
  · left; left; exact norm_sub_phi_le hlip hx ha h
  · left; right; exact norm_sub_phi_le hlip hx hb h
  · right; exact norm_sub_phi_le hlip hx hc h

include hbij hlip hi in
/-- An open set of block `i` is never carried into a line. -/
lemma not_image_subset_line {G : Set (E i)} (hG : IsOpen G) (hGD : G ⊆ Metric.closedBall 0 1)
    (hGne : G.Nonempty) (m : κ) (v : E' m)
    (hline : ∀ a ∈ G, F (sg i a) ∈ Line m v) : False := by
  have := fdi hi
  -- a coordinate along `v`
  obtain ⟨c, hc⟩ : ∃ c : StrongDual ℝ (E' m), v = 0 ∨ c v = 1 := by
    by_cases hv : v = 0
    · exact ⟨0, Or.inl hv⟩
    · obtain ⟨g, -, hg⟩ := exists_dual_vector ℝ v (norm_ne_zero_iff.2 hv)
      refine ⟨‖v‖⁻¹ • g, Or.inr ?_⟩
      rw [ContinuousLinearMap.smul_apply, hg, smul_eq_mul, RCLike.ofReal_real_eq_id, id,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
  have hcoord : ∀ a ∈ G, (F (sg i a) : lp E' ⊤) m = c ((F (sg i a) : lp E' ⊤) m) • v := by
    intro a ha
    obtain ⟨-, t, ht⟩ := hline a ha
    rcases hc with hv | hv
    · rw [ht, hv]; simp
    · rw [ht, map_smul, hv, smul_eq_mul, mul_one]
  obtain ⟨w₀, hw₀⟩ : ∃ w : E i, w ≠ 0 := by
    have : Nontrivial (E i) := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
    exact exists_ne 0
  set h : E i → E i := fun a => c ((F (sg i a) : lp E' ⊤) m) • w₀ with hh
  have hcont : ContinuousOn h G := by
    refine ContinuousOn.smul ?_ continuousOn_const
    exact c.continuous.comp_continuousOn ((continuous_eval m).comp_continuousOn
      ((phi_cont hlip).mono hGD))
  have hinj : Set.InjOn h G := by
    intro a ha b hb hab
    have h1 : c ((F (sg i a) : lp E' ⊤) m) = c ((F (sg i b) : lp E' ⊤) m) :=
      smul_left_injective ℝ hw₀ hab
    have h2 : (F (sg i a) : lp E' ⊤) m = (F (sg i b) : lp E' ⊤) m := by
      rw [hcoord a ha, hcoord b hb, h1]
    have h3 : F (sg i a) = F (sg i b) := by
      refine c0_ext fun k => ?_
      by_cases hk : k = m
      · subst hk; exact h2
      · rw [(hline a ha).1 k hk, (hline b hb).1 k hk]
    exact phi_injOn hbij (hGD ha) (hGD hb) h3
  have hopen := Plasticity.Topology.isOpen_image_of_injOn_of_finrank_eq rfl G hG h hcont hinj
  have hsub : h '' G ⊆ ((ℝ ∙ w₀ : Submodule ℝ (E i)) : Set (E i)) := by
    rintro _ ⟨a, -, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w₀)
  have hint : (interior ((ℝ ∙ w₀ : Submodule ℝ (E i)) : Set (E i))).Nonempty :=
    (hGne.image h).mono (interior_maximal hsub hopen)
  have htop := Submodule.eq_top_of_nonempty_interior' _ hint
  have h1 := finrank_span_singleton (K := ℝ) hw₀
  rw [htop, finrank_top, hi] at h1
  omega

include hE' hbij hlip hi in
/-- In every nonempty open subset of the ball of block `i` some point has its image off three
given lines. -/
lemma exists_avoid {O : Set (E i)} (hO : IsOpen O) (hOD : O ⊆ Metric.closedBall 0 1)
    (hOne : O.Nonempty) (m₁ m₂ m₃ : κ) (v₁ : E' m₁) (v₂ : E' m₂) (v₃ : E' m₃) :
    ∃ b ∈ O, F (sg i b) ∉ Line m₁ v₁ ∧ F (sg i b) ∉ Line m₂ v₂ ∧ F (sg i b) ∉ Line m₃ v₃ := by
  have := fd' hE'
  set D := Metric.closedBall (0 : E i) 1
  set A : κ → (v : ∀ k, E' k) → Set (E i) := fun _ _ => ∅ with hA
  have hcl : ∀ (m : κ) (v : E' m), IsClosed (D ∩ (fun a => F (sg i a)) ⁻¹' Line m v) :=
    fun m v => (phi_cont hlip).preimage_isClosed_of_isClosed Metric.isClosed_closedBall
      (isClosed_line m v)
  have hint : ∀ (m : κ) (v : E' m), interior (D ∩ (fun a => F (sg i a)) ⁻¹' Line m v) = ∅ := by
    intro m v
    by_contra hne
    exact not_image_subset_line hbij hlip hi isOpen_interior
      (interior_subset.trans Set.inter_subset_left) (Set.nonempty_iff_ne_empty.2 hne) m v
      (fun a ha => (interior_subset ha).2)
  have hU : interior ((D ∩ (fun a => F (sg i a)) ⁻¹' Line m₁ v₁ ∪
      D ∩ (fun a => F (sg i a)) ⁻¹' Line m₂ v₂) ∪ D ∩ (fun a => F (sg i a)) ⁻¹' Line m₃ v₃) = ∅ := by
    rw [interior_union_isClosed_of_interior_empty ((hcl m₁ v₁).union (hcl m₂ v₂)) (hint m₃ v₃),
      interior_union_isClosed_of_interior_empty (hcl m₁ v₁) (hint m₂ v₂), hint m₁ v₁]
  by_contra hcon
  push Not at hcon
  have hsub : O ⊆ (D ∩ (fun a => F (sg i a)) ⁻¹' Line m₁ v₁ ∪
      D ∩ (fun a => F (sg i a)) ⁻¹' Line m₂ v₂) ∪ D ∩ (fun a => F (sg i a)) ⁻¹' Line m₃ v₃ := by
    intro b hb
    have hbD := hOD hb
    by_cases h1 : F (sg i b) ∈ Line m₁ v₁
    · exact Or.inl (Or.inl ⟨hbD, h1⟩)
    by_cases h2 : F (sg i b) ∈ Line m₂ v₂
    · exact Or.inl (Or.inr ⟨hbD, h2⟩)
    exact Or.inr ⟨hbD, hcon b hb h1 h2⟩
  have := interior_maximal hsub hO
  rw [hU] at this
  obtain ⟨b, hb⟩ := hOne
  exact this hb

end Ctx

/-! ### Rays, edge images and distinct lines -/

section Rays

variable {κ : Type*} {E' : κ → Type*} [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]

/-- `y` is supported in block `m` and lies on the open ray of `v` there. -/
def OnRay (y : c0Sum E') (m : κ) (v : E' m) : Prop :=
  (∀ k ≠ m, (y : lp E' ⊤) k = 0) ∧ ∃ α : ℝ, 0 < α ∧ (y : lp E' ⊤) m = α • v

lemma OnRay.smul {y : c0Sum E'} {m : κ} {v : E' m} {c : ℝ} (hc : 0 < c) (h : OnRay y m (c • v)) :
    OnRay y m v := by
  obtain ⟨h1, α, hα, h2⟩ := h
  exact ⟨h1, α * c, mul_pos hα hc, by rw [h2, smul_smul]⟩

lemma OnRay.ne_zero {y : c0Sum E'} {m : κ} {v : E' m} (hv : v ≠ 0) (h : OnRay y m v) :
    (y : lp E' ⊤) m ≠ 0 := by
  obtain ⟨-, α, hα, h2⟩ := h
  rw [h2]; exact smul_ne_zero hα.ne' hv

lemma OnRay.mem_line {y : c0Sum E'} {m : κ} {v : E' m} (h : OnRay y m v) : y ∈ Line m v := by
  obtain ⟨h1, α, -, h2⟩ := h
  exact ⟨h1, α, h2⟩

/-- Two curves leaving `0` along the same open ray meet away from `0`. -/
lemma ivt_common {φ ψ : ℝ → c0Sum E'} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hφ : ContinuousOn φ (Set.Icc 0 a)) (hψ : ContinuousOn ψ (Set.Icc 0 b))
    (hφ0 : φ 0 = 0) (hψ0 : ψ 0 = 0) {m : κ} {v : E' m} (hv : v ≠ 0)
    (hφv : ∀ t, 0 < t → t ≤ a → OnRay (φ t) m v) (hψv : ∀ t, 0 < t → t ≤ b → OnRay (ψ t) m v) :
    ∃ s, 0 < s ∧ s ≤ a ∧ ∃ t, 0 < t ∧ t ≤ b ∧ φ s = ψ t := by
  have hpos : ∀ y : c0Sum E', OnRay y m v → 0 < ‖y‖ := fun y hy =>
    norm_pos_iff.2 fun h => hy.ne_zero hv (by rw [h]; rfl)
  set c := min ‖φ a‖ ‖ψ b‖
  have hc : 0 < c := lt_min (hpos _ (hφv a ha le_rfl)) (hpos _ (hψv b hb le_rfl))
  obtain ⟨s, hs, hsc⟩ := intermediate_value_Icc ha.le (continuous_norm.comp_continuousOn hφ)
    (show c ∈ Set.Icc ‖φ 0‖ ‖φ a‖ by rw [hφ0, norm_zero]; exact ⟨hc.le, min_le_left _ _⟩)
  obtain ⟨t, ht, htc⟩ := intermediate_value_Icc hb.le (continuous_norm.comp_continuousOn hψ)
    (show c ∈ Set.Icc ‖ψ 0‖ ‖ψ b‖ by rw [hψ0, norm_zero]; exact ⟨hc.le, min_le_right _ _⟩)
  simp only [Function.comp] at hsc htc
  have hs0 : 0 < s := by
    rcases hs.1.lt_or_eq with h | h
    · exact h
    · subst h; rw [hφ0, norm_zero] at hsc; linarith
  have ht0 : 0 < t := by
    rcases ht.1.lt_or_eq with h | h
    · exact h
    · subst h; rw [hψ0, norm_zero] at htc; linarith
  refine ⟨s, hs0, hs.2, t, ht0, ht.2, ?_⟩
  obtain ⟨h1, α, hα, h2⟩ := hφv s hs0 hs.2
  obtain ⟨h1', β, hβ, h2'⟩ := hψv t ht0 ht.2
  have hn1 := norm_eq_of_supp h1
  have hn2 := norm_eq_of_supp h1'
  rw [h2, norm_smul, Real.norm_of_nonneg hα.le] at hn1
  rw [h2', norm_smul, Real.norm_of_nonneg hβ.le] at hn2
  have hαβ : α = β := by
    have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
    have : α * ‖v‖ = β * ‖v‖ := by rw [← hn1, ← hn2, hsc, htc]
    exact mul_right_cancel₀ hvn.ne' this
  refine c0_ext fun k => ?_
  by_cases hk : k = m
  · subst hk; rw [h2, h2', hαβ]
  · rw [h1 k hk, h1' k hk]

end Rays

section Ctx2

variable {ι κ : Type*}
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {E' : κ → Type*} [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
  (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
  {F : c0Sum E → c0Sum E'}
  (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
  (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
  {i : ι} (hi : Module.finrank ℝ (E i) = 2)

lemma norm_smul_le_one {r : E i} (hr : ‖r‖ ≤ 2) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    ‖t • r‖ ≤ 1 := by
  rw [norm_smul, Real.norm_of_nonneg ht0]
  nlinarith [norm_nonneg r]

lemma norm_neg_smul_le_one {r : E i} (hr : ‖r‖ ≤ 2) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    ‖-(t • r)‖ ≤ 1 := by
  rw [norm_neg]; exact norm_smul_le_one hr ht0 ht

include hE' hbij hlip hi in
/-- Short multiples of an edge vector map into one line of one target block, positive and
negative multiples onto opposite open rays (CUB103 Lemma 3.2). -/
lemma edge_image {f : StrongDual ℝ (E i)} (hf : ‖f‖ = 1) {a b : E i} (ha : ‖a‖ ≤ 1)
    (hb : ‖b‖ ≤ 1) (hfa : f a = 1) (hfb : f b = 1) (hab : a ≠ b) :
    ∃ m : κ, ∃ v : E' m, v ≠ 0 ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
      OnRay (F (sg i (t • (b - a)))) m v ∧ OnRay (F (sg i (-(t • (b - a))))) m (-v) := by
  set r := b - a with hr
  have hr0 : r ≠ 0 := sub_ne_zero.2 hab.symm
  have hr2 : ‖r‖ ≤ 2 := (norm_sub_le b a).trans (by linarith)
  have hne : ∀ t : ℝ, t ≠ 0 → t • r ≠ 0 := fun t ht => smul_ne_zero ht hr0
  -- the covers by two translates along `r`
  have hcov : ∀ t s : ℝ, 0 < t → 0 < s → t ≤ 1 / 2 → s ≤ 1 / 2 →
      Metric.closedBall (0 : c0Sum E') 1 ⊆
        Metric.closedBall (F (sg i (t • r))) 1 ∪ Metric.closedBall (F (sg i (-(s • r)))) 1 := by
    intro t s ht hs ht2 hs2
    have hts : t + s ≤ 1 := by linarith
    refine cover_lift2 hbij hlip (norm_smul_le_one hr2 ht.le ht2)
      (norm_neg_smul_le_one hr2 hs.le hs2) ?_
    exact (Plasticity.Plane.closedBall_subset_union_two_iff hi _ _ (hne t ht.ne')
      (neg_ne_zero.2 (hne s hs.ne'))).2 ⟨f, hf, a, b, ha, hb, hfa, hfb, t, s, ht, hs, hts, rfl, rfl⟩
  have hnz : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → F (sg i (t • r)) ≠ 0 ∧ F (sg i (-(t • r))) ≠ 0 :=
    fun t ht ht2 => ⟨phi_ne_zero hbij hlip (norm_smul_le_one hr2 ht.le ht2) (hne t ht.ne'),
      phi_ne_zero hbij hlip (norm_neg_smul_le_one hr2 ht.le ht2) (neg_ne_zero.2 (hne t ht.ne'))⟩
  set P := F (sg i (-((1 / 2 : ℝ) • r)))
  obtain ⟨m₀, hm₀⟩ := exists_ne_zero_of_ne_zero (hnz (1 / 2) (by norm_num) le_rfl).2
  refine ⟨m₀, -(P : lp E' ⊤) m₀, neg_ne_zero.2 hm₀, ?_⟩
  have hpos : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → OnRay (F (sg i (t • r))) m₀ (-(P : lp E' ⊤) m₀) := by
    intro t ht ht2
    obtain ⟨m, hm, μ, hμ, hPm⟩ := Plasticity.C0Sum.exists_blockEquiv_two_balls E' hE' _ _
      (hnz t ht ht2).1 (hnz (1 / 2) (by norm_num) le_rfl).2 (hcov t (1 / 2) ht (by norm_num)
        ht2 le_rfl)
    have hmm : m₀ = m := by
      by_contra h; exact hm₀ (hm m₀ h).2
    subst hmm
    refine ⟨fun k hk => (hm k hk).1, μ⁻¹, inv_pos.2 hμ, ?_⟩
    rw [hPm, neg_neg, smul_smul, inv_mul_cancel₀ hμ.ne', one_smul]
  refine fun t ht ht2 => ⟨hpos t ht ht2, ?_⟩
  have hQ := hpos (1 / 2) (by norm_num) le_rfl
  obtain ⟨m, hm, μ, hμ, hQm⟩ := Plasticity.C0Sum.exists_blockEquiv_two_balls E' hE' _ _
    (hnz (1 / 2) (by norm_num) le_rfl).1 (hnz t ht ht2).2
    (hcov (1 / 2) t (by norm_num) ht le_rfl ht2)
  have hmm : m₀ = m := by
    by_contra h; exact hQ.ne_zero (neg_ne_zero.2 hm₀) (hm m₀ h).1
  subst hmm
  obtain ⟨-, α₀, hα₀, hQ2⟩ := hQ
  refine ⟨fun k hk => (hm k hk).2, μ * α₀, mul_pos hμ hα₀, ?_⟩
  rw [hQm, hQ2, smul_smul]
  simp [smul_neg]

include hbij hlip in
/-- Images of short multiples of two independent edge vectors lie on distinct lines. -/
lemma lines_ne {r₁ r₂ : E i} (hr₁ : ‖r₁‖ ≤ 2) (hr₂ : ‖r₂‖ ≤ 2) (hind : ∀ c : ℝ, r₂ ≠ c • r₁)
    {m : κ} {v₁ v₂ : E' m} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (h₁ : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
      OnRay (F (sg i (t • r₁))) m v₁ ∧ OnRay (F (sg i (-(t • r₁)))) m (-v₁))
    (h₂ : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
      OnRay (F (sg i (t • r₂))) m v₂ ∧ OnRay (F (sg i (-(t • r₂)))) m (-v₂)) :
    ∀ c : ℝ, v₂ ≠ c • v₁ := by
  intro c hc
  have h0 : F (sg i (0 : E i)) = 0 := by rw [sg_zero, map_zero hbij hlip]
  have hcont : ∀ r : E i, ‖r‖ ≤ 2 → ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
      ContinuousOn (fun t : ℝ => F (sg i ((ε * t) • r))) (Set.Icc 0 (1 / 2)) := by
    intro r hr ε hε
    refine (phi_cont hlip).comp (Continuous.continuousOn (by fun_prop)) fun t ht => ?_
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_mul]
    have : |ε| = 1 := by rcases hε with rfl | rfl <;> simp
    rw [this, one_mul, abs_of_nonneg ht.1]
    nlinarith [norm_nonneg r, ht.2]
  have hc0 : c ≠ 0 := by
    rintro rfl; exact hv₂ (by rw [hc, zero_smul])
  have key : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → (∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
      OnRay (F (sg i ((ε * t) • r₂))) m v₁) → False := by
    intro ε hε hray
    obtain ⟨s, hs, hs2, t, ht, ht2, hst⟩ := ivt_common (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (hcont r₁ hr₁ 1 (Or.inl rfl)) (hcont r₂ hr₂ ε hε)
      (by simpa using h0) (by simpa using h0) hv₁
      (fun t ht ht2 => by simpa using (h₁ t ht ht2).1) hray
    have hD : ∀ (r : E i), ‖r‖ ≤ 2 → ∀ (u : ℝ), |u| ≤ 1 / 2 →
        (u • r) ∈ Metric.closedBall (0 : E i) 1 := by
      intro r hr u hu
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs]
      nlinarith [norm_nonneg r, abs_nonneg u]
    have heq := phi_injOn hbij (hD r₁ hr₁ (1 * s) (by rw [one_mul, abs_of_pos hs]; exact hs2))
      (hD r₂ hr₂ (ε * t) (by
        rw [abs_mul]; rcases hε with rfl | rfl <;> simp [abs_of_pos ht] <;> linarith)) hst
    have hεt : ε * t ≠ 0 := mul_ne_zero (by rcases hε with rfl | rfl <;> norm_num) ht.ne'
    refine hind ((ε * t)⁻¹ * (1 * s)) ?_
    rw [mul_smul, heq, smul_smul, inv_mul_cancel₀ hεt, one_smul]
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · refine key (-1) (Or.inr rfl) fun t ht ht2 => ?_
    have h' : OnRay (F (sg i (-(t • r₂)))) m ((-c) • v₁) := by
      rw [neg_smul, ← hc]; exact (h₂ t ht ht2).2
    have e : (-1 * t) • r₂ = -(t • r₂) := by rw [neg_one_mul, neg_smul]
    rw [e]
    exact h'.smul (by linarith)
  · refine key 1 (Or.inl rfl) fun t ht ht2 => ?_
    have := (h₂ t ht ht2).1
    rw [hc] at this
    rw [one_mul]
    exact this.smul hpos

end Ctx2

/-! ### Good directions, corners, and the block of a planar source -/

section Ctx3

variable {ι κ : Type*}
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {E' : κ → Type*} [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
  (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
  {F : c0Sum E → c0Sum E'}
  (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
  (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
  {i : ι} (hi : Module.finrank ℝ (E i) = 2)

include hi in
/-- At a good direction the completions contain a box of two open sets (CUB102(1)). -/
lemma completion_boxes {a : E i} (ha : ‖a‖ ≤ 1) (ha0 : a ≠ 0) {p q : E i}
    (hp : p ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1))
    (hq : q ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)) (hpq : p ≠ q)
    (hpe : ‖p - ‖a‖⁻¹ • a‖ < 1) (hqe : ‖q - ‖a‖⁻¹ • a‖ < 1) :
    ∃ O₁ O₂ : Set (E i), IsOpen O₁ ∧ IsOpen O₂ ∧ O₁.Nonempty ∧ O₂.Nonempty ∧
      O₁ ⊆ Metric.closedBall 0 1 ∧ O₂ ⊆ Metric.closedBall 0 1 ∧
      ∀ c₁ ∈ O₁, ∀ c₂ ∈ O₂, c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ Metric.closedBall (0 : E i) 1 ⊆
        Metric.closedBall a 1 ∪ Metric.closedBall c₁ 1 ∪ Metric.closedBall c₂ 1 := by
  have hn : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have he : ‖‖a‖⁻¹ • a‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  obtain ⟨U, hUo, ⟨c, hc⟩, hU⟩ := Plasticity.Plane.exists_open_completions hi _ p q he hp hq hpq
    hpe hqe ‖a‖ hn ha
  have hsa : ‖a‖ • ‖a‖⁻¹ • a = a := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hUo c hc
  rw [← ball_prod_same] at hball
  refine ⟨Metric.ball c.1 ρ, Metric.ball c.2 ρ, Metric.isOpen_ball, Metric.isOpen_ball,
    ⟨c.1, Metric.mem_ball_self hρ⟩, ⟨c.2, Metric.mem_ball_self hρ⟩, ?_, ?_, ?_⟩
  · intro c₁ hc₁
    have := hU (c₁, c.2) (hball ⟨hc₁, Metric.mem_ball_self hρ⟩)
    exact mem_closedBall_zero_iff.2 this.2.2.1
  · intro c₂ hc₂
    have := hU (c.1, c₂) (hball ⟨Metric.mem_ball_self hρ, hc₂⟩)
    exact mem_closedBall_zero_iff.2 this.2.2.2.1
  · intro c₁ hc₁ c₂ hc₂
    have := hU (c₁, c₂) (hball ⟨hc₁, hc₂⟩)
    rw [hsa] at this
    exact ⟨this.1, this.2.1, this.2.2.2.2⟩

include hE' hbij hlip hi in
/-- The image of a point of a good direction is supported in one block. -/
lemma single_of_good {a : E i} (ha : ‖a‖ ≤ 1) (ha0 : a ≠ 0) {p q : E i}
    (hp : p ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1))
    (hq : q ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)) (hpq : p ≠ q)
    (hpe : ‖p - ‖a‖⁻¹ • a‖ < 1) (hqe : ‖q - ‖a‖⁻¹ • a‖ < 1) :
    ∃ m, ∀ k ≠ m, (F (sg i a) : lp E' ⊤) k = 0 := by
  obtain ⟨O₁, O₂, hO₁, hO₂, hne₁, hne₂, hD₁, hD₂, hO⟩ :=
    completion_boxes hi ha ha0 hp hq hpq hpe hqe
  by_contra hcon
  push Not at hcon
  obtain ⟨m, hm⟩ := exists_ne_zero_of_ne_zero (phi_ne_zero hbij hlip ha ha0)
  obtain ⟨m', hm'm, hm'⟩ := hcon m
  set q₀ := F (sg i a)
  obtain ⟨c₁, hc₁, hc₁m, hc₁m', -⟩ := exists_avoid hE' hbij hlip hi hO₁ hD₁ hne₁ m m' m
    ((q₀ : lp E' ⊤) m) ((q₀ : lp E' ⊤) m') ((q₀ : lp E' ⊤) m)
  have hc₁D := mem_closedBall_zero_iff.1 (hD₁ hc₁)
  obtain ⟨c₂', hc₂'⟩ := hne₂
  have hc₁0 := (hO c₁ hc₁ c₂' hc₂').1
  obtain ⟨n₁, hn₁⟩ := exists_ne_zero_of_ne_zero (phi_ne_zero hbij hlip hc₁D hc₁0)
  obtain ⟨c₂, hc₂, hc₂m, hc₂m', hc₂n⟩ := exists_avoid hE' hbij hlip hi hO₂ hD₂ ⟨c₂', hc₂'⟩ m m' n₁
    ((q₀ : lp E' ⊤) m) ((q₀ : lp E' ⊤) m') ((F (sg i c₁) : lp E' ⊤) n₁)
  have hc₂D := mem_closedBall_zero_iff.1 (hD₂ hc₂)
  obtain ⟨-, hc₂0, hcov⟩ := hO c₁ hc₁ c₂ hc₂
  have hcovY := cover_lift3 hbij hlip ha hc₁D hc₂D hcov
  rcases Plasticity.C0Sum.exists_blockEquiv_three_balls E' hE' q₀ _ _
      (phi_ne_zero hbij hlip hc₁D hc₁0) (phi_ne_zero hbij hlip hc₂D hc₂0) hcovY m m'
      (Ne.symm hm'm) hm hm' with ⟨n, hn, μ, hμ, hq⟩ | ⟨qq, hqq, n, hn, hs, t, ht⟩
  · have hnn : n₁ = n := by
      by_contra h; exact hn₁ (hn n₁ h).1
    subst hnn
    exact hc₂n ⟨fun k hk => (hn k hk).2, -μ, by rw [hq, neg_smul]⟩
  · have hline : qq ∈ Line n ((q₀ : lp E' ⊤) n) := ⟨hs, t, ht⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hqq hn
    rcases hqq with rfl | rfl <;> rcases hn with rfl | rfl
    · exact hc₁m hline
    · exact hc₁m' hline
    · exact hc₂m hline
    · exact hc₂m' hline

/-- A point with a "corner package" at block `m` has its image in block `m`. -/
lemma single_of_package {q₀ q₁ q₂ : c0Sum E'} (hcov : Metric.closedBall (0 : c0Sum E') 1 ⊆
      Metric.closedBall q₀ 1 ∪ Metric.closedBall q₁ 1 ∪ Metric.closedBall q₂ 1) {m : κ}
    {u : E' m} (hu : ‖u‖ ≤ 1) (h1 : 1 < ‖u - (q₁ : lp E' ⊤) m‖)
    (h2 : 1 < ‖u - (q₂ : lp E' ⊤) m‖) : ∀ k ≠ m, (q₀ : lp E' ⊤) k = 0 := by
  intro k hk
  by_contra h
  refine kill3 q₀ q₁ q₂ hcov k m m
    (Function.update (Function.update 0 m u) k (antipode ((q₀ : lp E' ⊤) k))) ?_ ?_ ?_ ?_
  · intro l
    by_cases hl : l = k
    · subst hl; simp [norm_antipode_le]
    rw [Function.update_of_ne hl]
    by_cases hl' : l = m
    · subst hl'; simpa using hu
    simp [Function.update_of_ne hl']
  · rw [Function.update_self]; exact one_lt_norm_antipode_sub_self h
  · rw [Function.update_of_ne (Ne.symm hk), Function.update_self]; exact h1
  · rw [Function.update_of_ne (Ne.symm hk), Function.update_self]; exact h2

include hE' hbij hlip hi in
/-- At a corner both edge lines go to one target block `m`, and every point within distance one
of the corner has a cover by two short edge multiples whose images can be killed in block `m`
(CUB102(3) and the corner step of CUB103 Proposition 3.4). -/
lemma corner_package {x x₁ x₂ : E i} {f₁ f₂ : StrongDual ℝ (E i)}
    (hx : x ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1))
    (hx₁ : x₁ ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1))
    (hx₂ : x₂ ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1))
    (hf₁ : ‖f₁‖ = 1) (hf₂ : ‖f₂‖ = 1) (hx₁x : x₁ ≠ x) (hx₂x : x₂ ≠ x)
    (h₁x₁ : f₁ x₁ = 1) (h₁x : f₁ x = 1) (h₂x : f₂ x = 1) (h₂x₂ : f₂ x₂ = 1)
    (h₁x₂ : f₁ x₂ < 1) (h₂x₁ : f₂ x₁ < 1) (hlen : ‖x₂ - x‖ < 2) :
    ∃ m : κ, ∀ b : E i, ‖b‖ ≤ 1 → ‖b - x‖ < 1 → ∃ c₁ c₂ : E i, ‖c₁‖ ≤ 1 ∧ ‖c₂‖ ≤ 1 ∧
      Metric.closedBall (0 : E i) 1 ⊆
        Metric.closedBall b 1 ∪ Metric.closedBall c₁ 1 ∪ Metric.closedBall c₂ 1 ∧
      (∀ k ≠ m, (F (sg i c₁) : lp E' ⊤) k = 0) ∧ (∀ k ≠ m, (F (sg i c₂) : lp E' ⊤) k = 0) ∧
      F (sg i c₁) ≠ 0 ∧ ∃ u : E' m, ‖u‖ ≤ 1 ∧ 1 < ‖u - (F (sg i c₁) : lp E' ⊤) m‖ ∧
        1 < ‖u - (F (sg i c₂) : lp E' ⊤) m‖ := by
  have hxn : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hx.1
  have hx₁n : ‖x₁‖ ≤ 1 := mem_closedBall_zero_iff.1 hx₁.1
  have hx₂n : ‖x₂‖ ≤ 1 := mem_closedBall_zero_iff.1 hx₂.1
  set r₁ := x - x₁ with hr₁
  set r₂ := x₂ - x with hr₂
  have hr₁2 : ‖r₁‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hr₂2 : ‖r₂‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  obtain ⟨m₁, v₁, hv₁, h₁⟩ := edge_image hE' hbij hlip hi hf₁ hx₁n hxn h₁x₁ h₁x hx₁x
  obtain ⟨m₂, v₂, hv₂, h₂⟩ := edge_image hE' hbij hlip hi hf₂ hxn hx₂n h₂x h₂x₂ hx₂x.symm
  have hind : ∀ c : ℝ, r₂ ≠ c • r₁ := by
    intro c hc
    have h1 : f₁ r₂ = c * f₁ r₁ := by rw [hc, map_smul, smul_eq_mul]
    simp only [hr₁, hr₂, map_sub, h₁x, h₁x₁, sub_self, mul_zero] at h1
    linarith
  -- corner covers
  have hcc : ∀ b : E i, ‖b - x‖ < 1 → ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 / 2 ∧
      Metric.closedBall (0 : E i) 1 ⊆ Metric.closedBall b 1 ∪
        Metric.closedBall (-(μ • r₁)) 1 ∪ Metric.closedBall (μ • r₂) 1 := by
    intro b hb
    have hU : Metric.ball b 1 ∈ nhds x :=
      Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_eq_norm, ← norm_neg, neg_sub]; exact hb)
    obtain ⟨r, hr, hcov⟩ := Plasticity.Plane.corner_cover hi x x₁ x₂ f₁ f₂ hf₁ hf₂ hx₁n hxn
      h₁x₁ h₁x h₂x h₂x₂ h₁x₂ h₂x₁ _ hU
    refine ⟨min r (1 / 2), lt_min hr (by norm_num), min_le_right _ _, ?_⟩
    refine (hcov (min r (1 / 2)) (min r (1 / 2)) (lt_min hr (by norm_num)) (min_le_left _ _)
      (lt_min hr (by norm_num)) (min_le_left _ _)).trans ?_
    exact Set.union_subset_union_left _ (Set.union_subset_union_left _ Metric.ball_subset_closedBall)
  -- a good point near the midpoint of the second edge, off both edge lines
  set mid : E i := (1 / 2 : ℝ) • (x + x₂) with hmid
  have hmid1 : ‖mid‖ = 1 := by
    refine le_antisymm ?_ ?_
    · rw [hmid, norm_smul]
      have := norm_add_le x x₂
      rw [Real.norm_of_nonneg (by norm_num)]; linarith
    · have h1 : f₂ mid = 1 := by rw [hmid, map_smul, map_add, h₂x, h₂x₂]; norm_num
      have h2 := f₂.le_opNorm mid
      rw [hf₂, one_mul, h1, Real.norm_eq_abs, abs_one] at h2
      exact h2
  have hmidx : ‖mid - x‖ < 1 := by
    have : mid - x = (1 / 2 : ℝ) • (x₂ - x) := by rw [hmid]; module
    rw [this, norm_smul, Real.norm_of_nonneg (by norm_num)]; linarith
  have hmidx₂ : ‖mid - x₂‖ < 1 := by
    have : mid - x₂ = -((1 / 2 : ℝ) • (x₂ - x)) := by rw [hmid]; module
    rw [this, norm_neg, norm_smul, Real.norm_of_nonneg (by norm_num)]; linarith
  set N : E i → E i := fun b => ‖b‖⁻¹ • b
  have hNc : ContinuousOn N {b | b ≠ 0} :=
    (continuous_norm.continuousOn.inv₀ fun b hb => norm_ne_zero_iff.2 hb).smul continuousOn_id
  set O : Set (E i) := ({b | ‖b‖ < 1} ∩ {b | ‖b - x‖ < 1}) ∩
    ({b | b ≠ 0} ∩ N ⁻¹' {e | ‖x - e‖ < 1 ∧ ‖x₂ - e‖ < 1})
  have hOo : IsOpen O := by
    refine IsOpen.inter (IsOpen.inter ?_ ?_) (hNc.isOpen_inter_preimage isOpen_ne ?_)
    · exact isOpen_lt continuous_norm continuous_const
    · exact isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
    · exact (isOpen_lt (continuous_norm.comp (continuous_const.sub continuous_id))
        continuous_const).inter
        (isOpen_lt (continuous_norm.comp (continuous_const.sub continuous_id)) continuous_const)
  set s₀ : ℝ := (1 + ‖mid - x‖) / 2
  have hs₀ : 0 < s₀ := by positivity
  have hs₀1 : s₀ < 1 := by simp only [s₀]; linarith
  have hOne : O.Nonempty := by
    refine ⟨s₀ • mid, ⟨?_, ?_⟩, ?_, ?_⟩
    · show ‖s₀ • mid‖ < 1
      rw [norm_smul, hmid1, Real.norm_of_nonneg hs₀.le, mul_one]; exact hs₀1
    · show ‖s₀ • mid - x‖ < 1
      have : s₀ • mid - x = (mid - x) - (1 - s₀) • mid := by module
      rw [this]
      refine (norm_sub_le _ _).trans_lt ?_
      rw [norm_smul, hmid1, Real.norm_of_nonneg (by linarith), mul_one]
      simp only [s₀]; linarith
    · show s₀ • mid ≠ 0
      exact smul_ne_zero hs₀.ne' (norm_ne_zero_iff.1 (by rw [hmid1]; norm_num))
    · show ‖x - N (s₀ • mid)‖ < 1 ∧ ‖x₂ - N (s₀ • mid)‖ < 1
      have : N (s₀ • mid) = mid := by
        simp only [N]
        rw [norm_smul, hmid1, Real.norm_of_nonneg hs₀.le, mul_one, smul_smul,
          inv_mul_cancel₀ hs₀.ne', one_smul]
      rw [this, ← norm_neg, neg_sub, ← norm_neg (x₂ - mid), neg_sub]
      exact ⟨hmidx, hmidx₂⟩
  have hOD : O ⊆ Metric.closedBall 0 1 := fun b hb =>
    mem_closedBall_zero_iff.2 (le_of_lt hb.1.1)
  obtain ⟨b, hbO, hb₁, hb₂, -⟩ := exists_avoid hE' hbij hlip hi hOo hOD hOne m₁ m₂ m₁ v₁ v₂ v₁
  have hbD : ‖b‖ ≤ 1 := le_of_lt hbO.1.1
  have hb0 : b ≠ 0 := hbO.2.1
  have hbx : ‖b - x‖ < 1 := hbO.1.2
  obtain ⟨n, hn⟩ := single_of_good hE' hbij hlip hi hbD hb0 hx hx₂ hx₂x.symm hbO.2.2.1
    hbO.2.2.2
  have hbn : (F (sg i b) : lp E' ⊤) n ≠ 0 := by
    obtain ⟨k, hk⟩ := exists_ne_zero_of_ne_zero (phi_ne_zero hbij hlip hbD hb0)
    by_cases hkn : k = n
    · subst hkn; exact hk
    · exact absurd (hn k hkn) hk
  -- both edge lines go to one block
  obtain ⟨μ, hμ, hμ2, hcovb⟩ := hcc b hbx
  have hc₁n : ‖-(μ • r₁)‖ ≤ 1 := norm_neg_smul_le_one hr₁2 hμ.le hμ2
  have hc₂n : ‖μ • r₂‖ ≤ 1 := norm_smul_le_one hr₂2 hμ.le hμ2
  have hcovY := cover_lift3 hbij hlip hbD hc₁n hc₂n hcovb
  have hq₁ := (h₁ μ hμ hμ2).2
  have hq₂ := (h₂ μ hμ hμ2).1
  have hm12 : m₁ = m₂ := by
    by_contra h12
    have hcov3 : Cov3 (F (sg i b)) (F (sg i (-(μ • r₁)))) (F (sg i (μ • r₂))) := by
      intro y hy
      have := hcovY (mem_closedBall_zero_iff.2 hy)
      simp only [Set.mem_union, Metric.mem_closedBall, dist_eq_norm] at this
      tauto
    by_cases hn1 : n = m₁
    · subst hn1
      refine pair3 hE' hcov3 h12 hbn (hq₁.ne_zero (neg_ne_zero.2 hv₁)) ?_
        (hq₂.ne_zero hv₂)
      rintro ⟨ν, hν, hνe⟩
      apply hb₁
      obtain ⟨-, α, hα, hαe⟩ := hq₁
      refine ⟨hn, ν⁻¹ * α, ?_⟩
      have : (F (sg i b) : lp E' ⊤) n = -(ν⁻¹ • (F (sg i (-(μ • r₁))) : lp E' ⊤) n) := by
        rw [hνe, smul_neg, neg_neg, smul_smul, inv_mul_cancel₀ hν.ne', one_smul]
      rw [this, hαe]; module
    by_cases hn2 : n = m₂
    · subst hn2
      refine pair3 hE' (cov3_swap23 hcov3) (Ne.symm h12) hbn (hq₂.ne_zero hv₂) ?_
        (hq₁.ne_zero (neg_ne_zero.2 hv₁))
      rintro ⟨ν, hν, hνe⟩
      apply hb₂
      obtain ⟨-, α, hα, hαe⟩ := hq₂
      refine ⟨hn, -(ν⁻¹ * α), ?_⟩
      have : (F (sg i b) : lp E' ⊤) n = -(ν⁻¹ • (F (sg i (μ • r₂)) : lp E' ⊤) n) := by
        rw [hνe, smul_neg, neg_neg, smul_smul, inv_mul_cancel₀ hν.ne', one_smul]
      rw [this, hαe]; module
    exact single3 hcov3 hbn (hq₁.ne_zero (neg_ne_zero.2 hv₁)) (hq₂.ne_zero hv₂) hn1 hn2 h12
  subst hm12
  have hlines := lines_ne hbij hlip hr₁2 hr₂2 hind hv₁ hv₂ h₁ h₂
  refine ⟨m₁, fun b' hb' hb'x => ?_⟩
  obtain ⟨μ', hμ', hμ'2, hcov'⟩ := hcc b' hb'x
  have hq₁' := (h₁ μ' hμ' hμ'2).2
  have hq₂' := (h₂ μ' hμ' hμ'2).1
  have hc₁0 : -(μ' • r₁) ≠ 0 :=
    neg_ne_zero.2 (smul_ne_zero hμ'.ne' (sub_ne_zero.2 hx₁x.symm))
  refine ⟨-(μ' • r₁), μ' • r₂, norm_neg_smul_le_one hr₁2 hμ'.le hμ'2,
    norm_smul_le_one hr₂2 hμ'.le hμ'2, hcov', hq₁'.1, hq₂'.1,
    phi_ne_zero hbij hlip (norm_neg_smul_le_one hr₁2 hμ'.le hμ'2) hc₁0, ?_⟩
  obtain ⟨u, hu, hu1, hu2⟩ := exists_far_of_not_neg (hE' m₁) (hq₁'.ne_zero (neg_ne_zero.2 hv₁))
    (hq₂'.ne_zero hv₂) (by
      rintro ⟨ν, hν, hνe⟩
      obtain ⟨-, α, hα, hαe⟩ := hq₁'
      obtain ⟨-, β, hβ, hβe⟩ := hq₂'
      refine hlines (β⁻¹ * (ν * α)) ?_
      have : β • v₂ = (ν * α) • v₁ := by
        rw [← hβe, hνe, hαe]; module
      rw [mul_smul, ← this, smul_smul, inv_mul_cancel₀ hβ.ne', one_smul])
  exact ⟨u, hu, hu1, hu2⟩

end Ctx3

/-! ### The punctured disc is connected; the block is constant -/

section Conn

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma isPreconnected_punctured (hV : Module.finrank ℝ V = 2) :
    IsPreconnected (Metric.ball (0 : V) 1 \ {0}) := by
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  have hrank : 1 < Module.rank ℝ V := by
    rw [← Module.finrank_eq_rank, hV]; norm_num
  have hc := (isConnected_compl_singleton_of_one_lt_rank hrank (0 : V)).isPreconnected
  set g : V → V := fun v => (1 + ‖v‖)⁻¹ • v
  have hg : Continuous g :=
    ((continuous_const.add continuous_norm).inv₀ fun v =>
      (by positivity : (0 : ℝ) < 1 + ‖v‖).ne').smul continuous_id
  have himg : g '' {0}ᶜ = Metric.ball (0 : V) 1 \ {0} := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv0 : v ≠ 0 := hv
      have hpos : 0 < 1 + ‖v‖ := by positivity
      refine ⟨?_, ?_⟩
      · rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hpos.le,
          inv_mul_lt_iff₀ hpos]
        linarith
      · simp only [Set.mem_singleton_iff, g]
        exact smul_ne_zero (inv_ne_zero hpos.ne') hv0
    · rintro ⟨hw1, hw0⟩
      rw [mem_ball_zero_iff] at hw1
      have hw0' : w ≠ 0 := hw0
      have h1 : 0 < 1 - ‖w‖ := by linarith
      refine ⟨(1 - ‖w‖)⁻¹ • w, smul_ne_zero (inv_ne_zero h1.ne') hw0', ?_⟩
      simp only [g]
      rw [norm_smul, norm_inv, Real.norm_of_nonneg h1.le, smul_smul]
      have : (1 + (1 - ‖w‖)⁻¹ * ‖w‖)⁻¹ * (1 - ‖w‖)⁻¹ = 1 := by
        field_simp
        ring
      rw [this, one_smul]
  rw [← himg]
  exact hc.image g hg.continuousOn

end Conn

section Ctx4

variable {ι κ : Type*}
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {E' : κ → Type*} [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
  {F : c0Sum E → c0Sum E'}
  (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
  (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
  {i : ι} (hi : Module.finrank ℝ (E i) = 2)

include hbij hlip hi in
/-- If every nonzero point of the ball of block `i` has its image in a single block, then one
block receives the whole ball. -/
lemma const_block (hsingle : ∀ a : E i, ‖a‖ ≤ 1 → a ≠ 0 → ∃ m, ∀ k ≠ m,
      (F (sg i a) : lp E' ⊤) k = 0) :
    ∃ j, ∀ a : E i, ‖a‖ ≤ 1 → ∀ k ≠ j, (F (sg i a) : lp E' ⊤) k = 0 := by
  set Ω := Metric.ball (0 : E i) 1 \ {0}
  have hΩo : IsOpen Ω := Metric.isOpen_ball.sdiff isClosed_singleton
  have hΩD : Ω ⊆ Metric.closedBall 0 1 := fun a ha => Metric.ball_subset_closedBall ha.1
  have hblock : ∀ a ∈ Ω, ∃ m, (F (sg i a) : lp E' ⊤) m ≠ 0 ∧ ∀ k ≠ m,
      (F (sg i a) : lp E' ⊤) k = 0 := by
    intro a ha
    have haD := mem_closedBall_zero_iff.1 (hΩD ha)
    have ha0 : a ≠ 0 := ha.2
    obtain ⟨m, hm⟩ := hsingle a haD ha0
    obtain ⟨k, hk⟩ := exists_ne_zero_of_ne_zero (phi_ne_zero hbij hlip haD ha0)
    by_cases hkm : k = m
    · subst hkm; exact ⟨k, hk, hm⟩
    · exact absurd (hm k hkm) hk
  obtain ⟨w₀, hw₀⟩ : ∃ w : E i, w ≠ 0 := by
    have : Nontrivial (E i) := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
    exact exists_ne 0
  set a₀ : E i := (2 * ‖w₀‖)⁻¹ • w₀
  have hw₀n : 0 < ‖w₀‖ := norm_pos_iff.2 hw₀
  have ha₀ : a₀ ∈ Ω := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity), mul_inv,
        mul_assoc, inv_mul_cancel₀ hw₀n.ne']
      norm_num
    · exact smul_ne_zero (inv_ne_zero (by positivity)) hw₀
  obtain ⟨j, hj, -⟩ := hblock a₀ ha₀
  refine ⟨j, ?_⟩
  have hΦ : ContinuousOn (fun a : E i => F (sg i a)) Ω := (phi_cont hlip).mono hΩD
  have hU₁ : IsOpen {y : c0Sum E' | (y : lp E' ⊤) j ≠ 0} :=
    isOpen_ne_fun (continuous_eval j) continuous_const
  have hU₂ : IsOpen {y : c0Sum E' | ∃ k ≠ j, (y : lp E' ⊤) k ≠ 0} := by
    have : {y : c0Sum E' | ∃ k ≠ j, (y : lp E' ⊤) k ≠ 0} =
        ⋃ k, ⋃ (_ : k ≠ j), {y : c0Sum E' | (y : lp E' ⊤) k ≠ 0} := by
      ext y; simp
    rw [this]
    exact isOpen_iUnion fun k => isOpen_iUnion fun _ =>
      isOpen_ne_fun (continuous_eval k) continuous_const
  have hpre := isPreconnected_punctured hi
  have hΩ : ∀ a ∈ Ω, ∀ k ≠ j, (F (sg i a) : lp E' ⊤) k = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a₁, ha₁, k₁, hk₁j, hk₁⟩ := hcon
    obtain ⟨b, hbΩ, hb1, hb2⟩ := hpre _ _ (hΦ.isOpen_inter_preimage hΩo hU₁)
      (hΦ.isOpen_inter_preimage hΩo hU₂) (fun a ha => by
        obtain ⟨m, hm, hm'⟩ := hblock a ha
        by_cases hmj : m = j
        · subst hmj; exact Or.inl ⟨ha, hm⟩
        · exact Or.inr ⟨ha, m, hmj, hm⟩)
      ⟨a₀, ha₀, ha₀, hj⟩ ⟨a₁, ha₁, ha₁, k₁, hk₁j, hk₁⟩
    obtain ⟨m, -, hm'⟩ := hblock b hbΩ
    obtain ⟨-, hbj⟩ := hb1
    obtain ⟨-, k, hkj, hbk⟩ := hb2
    have h1 : j = m := by by_contra h; exact hbj (hm' j h)
    have h2 : k = m := by by_contra h; exact hbk (hm' k h)
    exact hkj (h2.trans h1.symm)
  have hC : IsClosed {y : c0Sum E' | ∀ k ≠ j, (y : lp E' ⊤) k = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun _ =>
      isClosed_eq (continuous_eval k) continuous_const
  have hS := (phi_cont (i := i) hlip).preimage_isClosed_of_isClosed Metric.isClosed_closedBall hC
  have hball : Metric.ball (0 : E i) 1 ⊆ Metric.closedBall 0 1 ∩
      (fun a : E i => F (sg i a)) ⁻¹' {y : c0Sum E' | ∀ k ≠ j, (y : lp E' ⊤) k = 0} := by
    intro a ha
    refine ⟨Metric.ball_subset_closedBall ha, ?_⟩
    by_cases ha0 : a = 0
    · subst ha0
      intro k _
      show (F (sg i 0) : lp E' ⊤) k = 0
      rw [sg_zero, map_zero hbij hlip]; rfl
    · exact hΩ a ⟨ha, ha0⟩
  have hcl := closure_minimal hball hS
  rw [closure_ball (0 : E i) one_ne_zero] at hcl
  intro a ha
  exact (hcl (mem_closedBall_zero_iff.2 ha)).2

end Ctx4


lemma eq_sg_of_supp {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] {x : c0Sum E} {i : ι} (hx : ∀ k ≠ i, (x : lp E ⊤) k = 0) :
    x = sg i ((x : lp E ⊤) i) := by
  refine c0_ext fun k => ?_
  by_cases hk : k = i
  · subst hk; rw [sg_self]
  · rw [hx k hk, sg_ne _ hk]

end Sol_Plasticity_C0Sum_exists_blockEquiv_front

open Sol_Plasticity_C0Sum_exists_blockEquiv_front in
theorem solution {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
    (F : c0Sum E → c0Sum E')
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (i : ι) (hi : Module.finrank ℝ (E i) = 2)
    (hpar : 4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard) :
    ∃ j : κ, Module.finrank ℝ (E' j) = 2 ∧
      (∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, (∀ k ≠ i, (x : lp E ⊤) k = 0) →
        ∀ m ≠ j, (F x : lp E' ⊤) m = 0) ∧
      ∀ a : E i, a ≠ 0 → ‖a‖ ≤ 1 → ∃ c₁ c₂ : E i, ‖c₁‖ ≤ 1 ∧ ‖c₂‖ ≤ 1 ∧
        Metric.closedBall (0 : E i) 1 ⊆
          Metric.closedBall a 1 ∪ Metric.closedBall c₁ 1 ∪ Metric.closedBall c₂ 1 ∧
        ∃ u : E' j, ‖u‖ ≤ 1 ∧ ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1,
          (∀ k ≠ i, (x : lp E ⊤) k = 0) → ((x : lp E ⊤) i = c₁ ∨ (x : lp E ⊤) i = c₂) →
            1 < ‖u - (F x : lp E' ⊤) j‖ := by
  classical
  have hgood_or_bad : ∀ a : E i, ‖a‖ ≤ 1 → a ≠ 0 →
      (∃ p ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1),
        ∃ q ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1),
          p ≠ q ∧ ‖p - ‖a‖⁻¹ • a‖ < 1 ∧ ‖q - ‖a‖⁻¹ • a‖ < 1) ∨
      ∃ m : κ, ∃ c₁ c₂ : E i, ‖c₁‖ ≤ 1 ∧ ‖c₂‖ ≤ 1 ∧
        Metric.closedBall (0 : E i) 1 ⊆
          Metric.closedBall a 1 ∪ Metric.closedBall c₁ 1 ∪ Metric.closedBall c₂ 1 ∧
        (∀ k ≠ m, (F (sg i c₁) : lp E' ⊤) k = 0) ∧ (∀ k ≠ m, (F (sg i c₂) : lp E' ⊤) k = 0) ∧
        F (sg i c₁) ≠ 0 ∧ ∃ u : E' m, ‖u‖ ≤ 1 ∧ 1 < ‖u - (F (sg i c₁) : lp E' ⊤) m‖ ∧
          1 < ‖u - (F (sg i c₂) : lp E' ⊤) m‖ := by
    intro a ha ha0
    by_cases hgood : ∃ p ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1),
        ∃ q ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1),
          p ≠ q ∧ ‖p - ‖a‖⁻¹ • a‖ < 1 ∧ ‖q - ‖a‖⁻¹ • a‖ < 1
    · exact Or.inl hgood
    right
    have hn : 0 < ‖a‖ := norm_pos_iff.2 ha0
    have he : ‖‖a‖⁻¹ • a‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hbad : ∀ p ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1),
        ∀ q ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1),
          ‖p - ‖a‖⁻¹ • a‖ < 1 → ‖q - ‖a‖⁻¹ • a‖ < 1 → p = q := by
      intro p hp q hq h1 h2
      by_contra h
      exact hgood ⟨p, hp, q, hq, h, h1, h2⟩
    obtain ⟨x, hx, hxe, x₁, hx₁, x₂, hx₂, f₁, f₂, hf₁, hf₂, hx₁x, hx₂x, h₁x₁, h₁x, h₂x, h₂x₂,
      h₁x₂, h₂x₁, hlen⟩ := Plasticity.Plane.exists_corner_of_bad hi hpar _ he hbad
    obtain ⟨m, hpkg⟩ := corner_package hE' hbij hlip hi hx hx₁ hx₂ hf₁ hf₂ hx₁x hx₂x h₁x₁ h₁x
      h₂x h₂x₂ h₁x₂ h₂x₁ hlen
    have hxn : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hx.1
    have hax : ‖a - x‖ < 1 := by
      have : a - x = ‖a‖ • (‖a‖⁻¹ • a - x) - (1 - ‖a‖) • x := by
        rw [smul_sub, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]; module
      rw [this]
      refine (norm_sub_le _ _).trans_lt ?_
      rw [norm_smul, norm_smul, norm_norm, Real.norm_of_nonneg (by linarith),
        norm_sub_rev (‖a‖⁻¹ • a) x]
      have h1 : ‖a‖ * ‖x - ‖a‖⁻¹ • a‖ < ‖a‖ * 1 := mul_lt_mul_of_pos_left hxe hn
      have h2 : (1 - ‖a‖) * ‖x‖ ≤ (1 - ‖a‖) * 1 :=
        mul_le_mul_of_nonneg_left hxn (by linarith)
      linarith
    exact ⟨m, hpkg a ha hax⟩
  have hsingle : ∀ a : E i, ‖a‖ ≤ 1 → a ≠ 0 → ∃ m, ∀ k ≠ m, (F (sg i a) : lp E' ⊤) k = 0 := by
    intro a ha ha0
    rcases hgood_or_bad a ha ha0 with ⟨p, hp, q, hq, hpq, hpe, hqe⟩ |
        ⟨m, c₁, c₂, hc₁, hc₂, hcov, -, -, -, u, hu, hu1, hu2⟩
    · exact single_of_good hE' hbij hlip hi ha ha0 hp hq hpq hpe hqe
    · exact ⟨m, single_of_package (cover_lift3 hbij hlip ha hc₁ hc₂ hcov) hu hu1 hu2⟩
  obtain ⟨j, hj⟩ := const_block hbij hlip hi hsingle
  have hfin : Module.finrank ℝ (E' j) = 2 := by
    rcases hE' j with h | h
    · exfalso
      obtain ⟨v, hv⟩ : ∃ v : E' j, v ≠ 0 := by
        have : Nontrivial (E' j) := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
        exact exists_ne 0
      refine not_image_subset_line hbij hlip hi Metric.isOpen_ball Metric.ball_subset_closedBall
        ⟨0, Metric.mem_ball_self one_pos⟩ j v fun a ha => ?_
      refine ⟨hj a (le_of_lt (mem_ball_zero_iff.1 ha)), ?_⟩
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v hv).1 h ((F (sg i a) : lp E' ⊤) j)
      exact ⟨c, hc.symm⟩
    · exact h
  have himg : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, (∀ k ≠ i, (x : lp E ⊤) k = 0) →
      F x = F (sg i ((x : lp E ⊤) i)) := fun x _ hx => by rw [← eq_sg_of_supp hx]
  have hxi : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ‖(x : lp E ⊤) i‖ ≤ 1 :=
    fun x hx => (norm_apply_le x i).trans (mem_closedBall_zero_iff.1 hx)
  refine ⟨j, hfin, fun x hx hsupp m hm => ?_, fun a ha0 ha => ?_⟩
  · rw [himg x hx hsupp]
    exact hj _ (hxi x hx) m hm
  have hfinal : ∀ c₁ c₂ : E i, ∀ u : E' j, 1 < ‖u - (F (sg i c₁) : lp E' ⊤) j‖ →
      1 < ‖u - (F (sg i c₂) : lp E' ⊤) j‖ → ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1,
        (∀ k ≠ i, (x : lp E ⊤) k = 0) → ((x : lp E ⊤) i = c₁ ∨ (x : lp E ⊤) i = c₂) →
          1 < ‖u - (F x : lp E' ⊤) j‖ := by
    intro c₁ c₂ u h1 h2 x hx hsupp hc
    rw [himg x hx hsupp]
    rcases hc with hc | hc <;> rw [hc] <;> assumption
  have hblockj : ∀ c : E i, ‖c‖ ≤ 1 → c ≠ 0 → (F (sg i c) : lp E' ⊤) j ≠ 0 := by
    intro c hc hc0 h
    apply phi_ne_zero hbij hlip hc hc0
    refine c0_ext fun k => ?_
    by_cases hk : k = j
    · subst hk; rw [h]; rfl
    · rw [hj c hc k hk]; rfl
  rcases hgood_or_bad a ha ha0 with ⟨p, hp, q, hq, hpq, hpe, hqe⟩ |
      ⟨m, c₁, c₂, hc₁, hc₂, hcov, hs₁, hs₂, hne, u, hu, hu1, hu2⟩
  · obtain ⟨O₁, O₂, hO₁, hO₂, ⟨c₁, hc₁⟩, hne₂, hD₁, hD₂, hO⟩ :=
      completion_boxes hi ha ha0 hp hq hpq hpe hqe
    obtain ⟨c₂, hc₂, hc₂L, -, -⟩ := exists_avoid hE' hbij hlip hi hO₂ hD₂ hne₂ j j j
      ((F (sg i c₁) : lp E' ⊤) j) ((F (sg i c₁) : lp E' ⊤) j) ((F (sg i c₁) : lp E' ⊤) j)
    obtain ⟨hc₁0, hc₂0, hcov⟩ := hO c₁ hc₁ c₂ hc₂
    have hc₁n := mem_closedBall_zero_iff.1 (hD₁ hc₁)
    have hc₂n := mem_closedBall_zero_iff.1 (hD₂ hc₂)
    obtain ⟨u, hu, hu1, hu2⟩ := exists_far_of_not_neg (hE' j) (hblockj c₁ hc₁n hc₁0)
      (hblockj c₂ hc₂n hc₂0) (by
        rintro ⟨μ, hμ, hμe⟩
        exact hc₂L ⟨hj c₂ hc₂n, -μ, by rw [hμe, neg_smul]⟩)
    exact ⟨c₁, c₂, hc₁n, hc₂n, hcov, u, hu, hfinal c₁ c₂ u hu1 hu2⟩
  · have hmj : m = j := by
      by_contra h
      apply hne
      refine c0_ext fun k => ?_
      by_cases hk : k = m
      · subst hk; rw [hj c₁ hc₁ k h]; rfl
      · rw [hs₁ k hk]; rfl
    subst hmj
    exact ⟨c₁, c₂, hc₁, hc₂, hcov, u, hu, hfinal c₁ c₂ u hu1 hu2⟩
