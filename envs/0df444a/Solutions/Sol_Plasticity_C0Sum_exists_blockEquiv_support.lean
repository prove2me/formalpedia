-- Prove2me | solution 1 for Plasticity.C0Sum.exists_blockEquiv_support
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:58.796911+00:00
-- url     : https://prove2.me/submissions/1e449027-a4b9-4a86-8b32-672ebc70415a

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Tactic.FinCases
import Theorems.Thm_Plasticity_Plane_closedBall_subset_union_two_iff
import Theorems.Thm_Plasticity_Topology_isOpen_image_of_injOn_of_finrank_eq
import Theorems.Thm_Plasticity_BallMap_map_zero_of_surjOn
import Theorems.Thm_Plasticity_C0Sum_exists_blockEquiv_two_balls
import Theorems.Thm_Plasticity_C0Sum_exists_blockEquiv_front
import Theorems.Thm_Plasticity_C0Sum_exists_blockEquiv_three_feeders

/-!
Forward support for c₀ sums of scalar and non-parallelogram planar blocks (CUB103
Proposition 3.5, CUB109 Lemmas 2.1–2.2 and Proposition 2.3).

The c₀-sum helpers `norm_c0Sum_le`, `norm_apply_le`, `c0_ext`, `ofFun`, `sg` are copied from the
project's solution `Solutions/Sol_Plasticity_C0Sum_exists_extremeRule.lean`; the planar lemmas
`exists_ne_zero_apply_eq_zero` and `exists_eq_smul_of_apply_eq_zero` from
`Solutions/Sol_Plasticity_Plane_closedBall_subset_union_two_iff.lean` and
`Solutions/Sol_Plasticity_Plane_exists_corner_of_bad.lean`.
-/

open Plasticity

namespace Sol_Plasticity_C0Sum_exists_blockEquiv_support

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

lemma eq_sg_of_supp {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] {x : c0Sum E} {i : ι} (hx : ∀ k ≠ i, (x : lp E ⊤) k = 0) :
    x = sg i ((x : lp E ⊤) i) := by
  refine c0_ext fun k => ?_
  by_cases hk : k = i
  · subst hk; rw [sg_self]
  · rw [hx k hk, sg_ne _ hk]


section PlaneFun

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_ne_zero_apply_eq_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2) (u : V) (hu : u ≠ 0) :
    ∃ ψ : StrongDual ℝ V, ψ ≠ 0 ∧ ψ u = 0 := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  have hlt : (ℝ ∙ u) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    have := finrank_span_singleton (K := ℝ) hu
    rw [h, finrank_top, hV] at this
    norm_num at this
  obtain ⟨g, hg, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  refine ⟨LinearMap.toContinuousLinearMap g, ?_, ?_⟩
  · intro h
    apply hg
    ext x
    simpa using congrArg (fun F : StrongDual ℝ V => F x) h
  · have : g u ∈ (ℝ ∙ u).map g :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self u)
    rw [hmap] at this
    simpa using this

/-- In a plane, the kernel of a nonzero functional is spanned by any nonzero element of it. -/
theorem exists_eq_smul_of_apply_eq_zero (hV : Module.finrank ℝ V = 2) (f : StrongDual ℝ V)
    (a r x : V) (ha : f a = 1) (hr : r ≠ 0) (hfr : f r = 0) (hfx : f x = 0) :
    ∃ μ : ℝ, x = μ • r := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  set g : V →ₗ[ℝ] ℝ := (f : V →ₗ[ℝ] ℝ) with hgdef
  have hsurj : LinearMap.range g = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨y • a, by simp [g, ha]⟩
  have hk : Module.finrank ℝ (LinearMap.ker g) = 1 := by
    have := LinearMap.finrank_range_add_finrank_ker g
    rw [hsurj, finrank_top, Module.finrank_self, hV] at this
    omega
  have hr' : (⟨r, by simpa [g] using hfr⟩ : LinearMap.ker g) ≠ 0 := by
    intro h
    apply hr
    simpa using congrArg Subtype.val h
  obtain ⟨μ, hμ⟩ := (finrank_eq_one_iff_of_nonzero' _ hr').1 hk ⟨x, by simpa [g] using hfx⟩
  exact ⟨μ, by simpa using (congrArg Subtype.val hμ).symm⟩

end PlaneFun

/-! ### Scalar source blocks and the provisional block map -/

section Support

variable {ι κ : Type*}
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {E' : κ → Type*} [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
  (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
  {F : c0Sum E → c0Sum E'}
  (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
  (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))

variable (F) in
/-- Block `i` is carried into block `j`. -/
def Rec (i : ι) (j : κ) : Prop :=
  ∀ a : E i, ‖a‖ ≤ 1 → ∀ k ≠ j, (F (sg i a) : lp E' ⊤) k = 0

variable (F) in
/-- The multiples `±t e`, `0 < t ≤ 1`, go to the open rays of `±v` in block `j`. -/
def Rays (i : ι) (e : E i) (j : κ) (v : E' j) : Prop :=
  ∀ t : ℝ, 0 < t → t ≤ 1 → OnRay (F (sg i (t • e))) j v ∧ OnRay (F (sg i (-(t • e)))) j (-v)

variable (F) in
/-- The auxiliary package of the front at block `i` with target block `j`. -/
def Pkg (i : ι) (j : κ) : Prop :=
  ∀ a : E i, a ≠ 0 → ‖a‖ ≤ 1 → ∃ c₁ c₂ : E i, ‖c₁‖ ≤ 1 ∧ ‖c₂‖ ≤ 1 ∧
    Metric.closedBall (0 : E i) 1 ⊆
      Metric.closedBall a 1 ∪ Metric.closedBall c₁ 1 ∪ Metric.closedBall c₂ 1 ∧
    ∃ u : E' j, ‖u‖ ≤ 1 ∧ 1 < ‖u - (F (sg i c₁) : lp E' ⊤) j‖ ∧
      1 < ‖u - (F (sg i c₂) : lp E' ⊤) j‖

omit [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] in
lemma eq_smul_of_finrank_one {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (hW : Module.finrank ℝ W = 1) {e : W} (he : ‖e‖ = 1) (a : W) :
    ∃ c : ℝ, a = c • e ∧ ‖a‖ = |c| := by
  have he0 : e ≠ 0 := norm_ne_zero_iff.1 (by rw [he]; norm_num)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' e he0).1 hW a
  exact ⟨c, hc.symm, by rw [← hc, norm_smul, he, mul_one, Real.norm_eq_abs]⟩

include hE' hbij hlip in
/-- A scalar source block is carried onto two opposite open rays of one line of one target
block (CUB109 Lemma 2.1(2)). -/
lemma scalar_rays {h : ι} (hh : Module.finrank ℝ (E h) = 1) {e : E h} (he : ‖e‖ = 1) :
    ∃ m : κ, ∃ v : E' m, v ≠ 0 ∧ Rays F h e m v := by
  have hn1 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖t • e‖ ≤ 1 := fun t ht0 ht1 => by
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg ht0]; exact ht1
  have hn2 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖-(t • e)‖ ≤ 1 := fun t ht0 ht1 => by
    rw [norm_neg]; exact hn1 t ht0 ht1
  have hcov : ∀ t s : ℝ, 0 < t → 0 < s → t ≤ 1 → s ≤ 1 →
      Metric.closedBall (0 : c0Sum E') 1 ⊆
        Metric.closedBall (F (sg h (t • e))) 1 ∪ Metric.closedBall (F (sg h (-(s • e)))) 1 := by
    intro t s ht hs ht1 hs1
    refine cover_lift2 hbij hlip (hn1 t ht.le ht1) (hn2 s hs.le hs1) fun z hz => ?_
    rw [mem_closedBall_zero_iff] at hz
    obtain ⟨c, rfl, hc⟩ := eq_smul_of_finrank_one hh he z
    rw [hc, abs_le] at hz
    simp only [Set.mem_union, Metric.mem_closedBall, dist_eq_norm]
    rcases le_or_gt 0 c with h0 | h0
    · left
      rw [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    · right
      rw [sub_neg_eq_add, ← add_smul, norm_smul, he, mul_one, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
  have he0 : e ≠ 0 := norm_ne_zero_iff.1 (by rw [he]; norm_num)
  have hne : ∀ t : ℝ, t ≠ 0 → t • e ≠ 0 := fun t ht => smul_ne_zero ht he0
  have hnz : ∀ t : ℝ, 0 < t → t ≤ 1 → F (sg h (t • e)) ≠ 0 ∧ F (sg h (-(t • e))) ≠ 0 :=
    fun t ht ht1 => ⟨phi_ne_zero hbij hlip (hn1 t ht.le ht1) (hne t ht.ne'),
      phi_ne_zero hbij hlip (hn2 t ht.le ht1) (neg_ne_zero.2 (hne t ht.ne'))⟩
  set P := F (sg h (-((1 : ℝ) • e)))
  obtain ⟨m₀, hm₀⟩ := exists_ne_zero_of_ne_zero (hnz 1 one_pos le_rfl).2
  refine ⟨m₀, -(P : lp E' ⊤) m₀, neg_ne_zero.2 hm₀, ?_⟩
  have hpos : ∀ t : ℝ, 0 < t → t ≤ 1 → OnRay (F (sg h (t • e))) m₀ (-(P : lp E' ⊤) m₀) := by
    intro t ht ht1
    obtain ⟨m, hm, μ, hμ, hPm⟩ := Plasticity.C0Sum.exists_blockEquiv_two_balls E' hE' _ _
      (hnz t ht ht1).1 (hnz 1 one_pos le_rfl).2 (hcov t 1 ht one_pos ht1 le_rfl)
    have hmm : m₀ = m := by
      by_contra h'; exact hm₀ (hm m₀ h').2
    subst hmm
    refine ⟨fun k hk => (hm k hk).1, μ⁻¹, inv_pos.2 hμ, ?_⟩
    rw [hPm, neg_neg, smul_smul, inv_mul_cancel₀ hμ.ne', one_smul]
  refine fun t ht ht1 => ⟨hpos t ht ht1, ?_⟩
  have hQ := hpos 1 one_pos le_rfl
  obtain ⟨m, hm, μ, hμ, hQm⟩ := Plasticity.C0Sum.exists_blockEquiv_two_balls E' hE' _ _
    (hnz 1 one_pos le_rfl).1 (hnz t ht ht1).2 (hcov 1 t one_pos ht le_rfl ht1)
  have hmm : m₀ = m := by
    by_contra h'; exact hQ.ne_zero (neg_ne_zero.2 hm₀) (hm m₀ h').1
  subst hmm
  obtain ⟨-, α₀, hα₀, hQ2⟩ := hQ
  refine ⟨fun k hk => (hm k hk).2, μ * α₀, mul_pos hμ hα₀, ?_⟩
  rw [hQm, hQ2]
  module

/-- Every nonzero point of a scalar block goes to a nonzero multiple of the ray vector. -/
lemma scalar_line {h : ι} (hh : Module.finrank ℝ (E h) = 1) {e : E h} (he : ‖e‖ = 1) {m : κ}
    {v : E' m} (hr : Rays F h e m v) {a : E h} (ha : ‖a‖ ≤ 1) (ha0 : a ≠ 0) :
    (∀ k ≠ m, (F (sg h a) : lp E' ⊤) k = 0) ∧
      ∃ c : ℝ, c ≠ 0 ∧ (F (sg h a) : lp E' ⊤) m = c • v := by
  obtain ⟨c, rfl, hc⟩ := eq_smul_of_finrank_one hh he a
  have hc0 : c ≠ 0 := by rintro rfl; exact ha0 (zero_smul _ _)
  rw [hc] at ha
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · have hr' := (hr (-c) (by linarith) (by rw [abs_of_neg hneg] at ha; exact ha)).2
    rw [neg_smul, neg_neg] at hr'
    obtain ⟨h1, α, hα, h2⟩ := hr'
    exact ⟨h1, -α, by linarith, by rw [h2, smul_neg, neg_smul]⟩
  · obtain ⟨h1, α, hα, h2⟩ := (hr c hpos (by rw [abs_of_pos hpos] at ha; exact ha)).1
    exact ⟨h1, α, hα.ne', h2⟩

include hbij hlip in
lemma rec_of_rays {h : ι} (hh : Module.finrank ℝ (E h) = 1) {e : E h} (he : ‖e‖ = 1) {m : κ}
    {v : E' m} (hr : Rays F h e m v) : Rec F h m := by
  intro a ha k hk
  by_cases ha0 : a = 0
  · subst ha0; rw [sg_zero, map_zero hbij hlip]; rfl
  · exact (scalar_line hh he hr ha ha0).1 k hk

include hbij hlip in
/-- The image of the open ball of a planar source block is a neighbourhood of `0` in its
target block (invariance of domain). -/
lemma planar_open {i : ι} {j : κ} (hi : Module.finrank ℝ (E i) = 2)
    (hj : Module.finrank ℝ (E' j) = 2) (hrec : Rec F i j) :
    ∃ ρ > 0, ∀ w : E' j, ‖w‖ < ρ → ∃ a : E i, ‖a‖ ≤ 1 ∧ F (sg i a) = sg j w := by
  have := fdi hi
  have : FiniteDimensional ℝ (E' j) := Module.finite_of_finrank_eq_succ hj
  set g : E i → E' j := fun a => (F (sg i a) : lp E' ⊤) j
  have hcont : ContinuousOn g (Metric.ball 0 1) :=
    (continuous_eval j).comp_continuousOn ((phi_cont hlip).mono Metric.ball_subset_closedBall)
  have hinj : Set.InjOn g (Metric.ball 0 1) := by
    intro a ha b hb hab
    have ha' := mem_closedBall_zero_iff.1 (Metric.ball_subset_closedBall ha)
    have hb' := mem_closedBall_zero_iff.1 (Metric.ball_subset_closedBall hb)
    refine phi_injOn hbij (Metric.ball_subset_closedBall ha) (Metric.ball_subset_closedBall hb) ?_
    refine c0_ext fun k => ?_
    by_cases hk : k = j
    · subst hk; exact hab
    · show (F (sg i a) : lp E' ⊤) k = (F (sg i b) : lp E' ⊤) k
      rw [hrec a ha' k hk, hrec b hb' k hk]
  have hopen := Plasticity.Topology.isOpen_image_of_injOn_of_finrank_eq (hi.trans hj.symm) _
    Metric.isOpen_ball g hcont hinj
  have hg0 : g 0 = 0 := by
    show (F (sg i 0) : lp E' ⊤) j = 0
    rw [sg_zero, map_zero hbij hlip]; rfl
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen 0 ⟨0, Metric.mem_ball_self one_pos, hg0⟩
  refine ⟨ρ, hρ, fun w hw => ?_⟩
  obtain ⟨a, ha, haw⟩ := hball (mem_ball_zero_iff.2 hw)
  have ha' := mem_closedBall_zero_iff.1 (Metric.ball_subset_closedBall ha)
  refine ⟨a, ha', ?_⟩
  rw [eq_sg_of_supp (hrec a ha')]
  exact congrArg (sg j) haw

include hbij hlip in
/-- No other source block shares the target block of a planar source block. -/
lemma planar_alone {i k : ι} {j : κ} (hki : k ≠ i)
    (hρ : ∃ ρ > 0, ∀ w : E' j, ‖w‖ < ρ → ∃ a : E i, ‖a‖ ≤ 1 ∧ F (sg i a) = sg j w)
    (hreck : Rec F k j) (hk : 0 < Module.finrank ℝ (E k)) : False := by
  obtain ⟨ρ, hρ, hopen⟩ := hρ
  obtain ⟨w₀, hw₀⟩ : ∃ w : E k, w ≠ 0 := by
    have : Nontrivial (E k) := Module.nontrivial_of_finrank_pos (R := ℝ) hk
    exact exists_ne 0
  have hw₀n : 0 < ‖w₀‖ := norm_pos_iff.2 hw₀
  set r := min ρ 1 / 2
  have hr : 0 < r := by positivity
  set c : E k := (r / ‖w₀‖) • w₀
  have hcn : ‖c‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hw₀n.ne']
  have hc0 : c ≠ 0 := norm_ne_zero_iff.1 (by rw [hcn]; exact hr.ne')
  have hr1 : r ≤ 1 := by have := min_le_right ρ 1; simp only [r]; linarith
  have hrρ : r < ρ := by
    have := min_le_left ρ 1; simp only [r]; linarith [lt_min hρ one_pos]
  have hcD : ‖c‖ ≤ 1 := by rw [hcn]; exact hr1
  have hsmall : ‖(F (sg k c) : lp E' ⊤) j‖ < ρ := by
    have h1 := phi_lip hlip hcD (by simp : ‖(0 : E k)‖ ≤ 1)
    rw [sg_zero, map_zero hbij hlip, sub_zero, sub_zero, hcn] at h1
    exact ((norm_apply_le _ j).trans h1).trans_lt hrρ
  obtain ⟨a, ha, haF⟩ := hopen _ hsmall
  rw [← eq_sg_of_supp (hreck c hcD)] at haF
  have hsg := hbij.injOn (sg_mem ha) (sg_mem hcD) haF
  have := congrArg (fun x : c0Sum E => (x : lp E ⊤) k) hsg
  simp only [sg_self, sg_ne _ hki] at this
  exact hc0 this.symm

include hbij hlip in
/-- Two scalar source blocks into one target block have distinct lines. -/
lemma scalar_lines_ne {h h' : ι} (hhh : h ≠ h') {e : E h} {e' : E h'} (he : ‖e‖ = 1)
    (he' : ‖e'‖ = 1) {m : κ} {v v' : E' m} (hv : v ≠ 0) (hv' : v' ≠ 0)
    (hr : Rays F h e m v) (hr' : Rays F h' e' m v') : ∀ c : ℝ, v' ≠ c • v := by
  intro c hc
  have h0 : ∀ j : ι, F (sg j (0 : E j)) = 0 := fun j => by rw [sg_zero, map_zero hbij hlip]
  have hD : ∀ (j : ι) (r : E j), ‖r‖ = 1 → ∀ u : ℝ, |u| ≤ 1 →
      (u • r) ∈ Metric.closedBall (0 : E j) 1 := by
    intro j r hr u hu
    rw [mem_closedBall_zero_iff, norm_smul, hr, mul_one, Real.norm_eq_abs]; exact hu
  have hcont : ∀ (j : ι) (r : E j), ‖r‖ = 1 → ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
      ContinuousOn (fun t : ℝ => F (sg j ((ε * t) • r))) (Set.Icc 0 1) := by
    intro j r hr ε hε
    refine (phi_cont hlip).comp (Continuous.continuousOn (by fun_prop)) fun t ht => ?_
    refine hD j r hr _ ?_
    rw [abs_mul]
    have : |ε| = 1 := by rcases hε with rfl | rfl <;> simp
    rw [this, one_mul, abs_of_nonneg ht.1]; exact ht.2
  have hc0 : c ≠ 0 := by
    rintro rfl; exact hv' (by rw [hc, zero_smul])
  have key : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → (∀ t : ℝ, 0 < t → t ≤ 1 →
      OnRay (F (sg h' ((ε * t) • e'))) m v) → False := by
    intro ε hε hray
    obtain ⟨s, hs, hs1, t, ht, ht1, hst⟩ := ivt_common one_pos one_pos
      (hcont h e he 1 (Or.inl rfl)) (hcont h' e' he' ε hε)
      (by simpa using h0 h) (by simpa using h0 h') hv
      (fun t ht ht1 => by simpa using (hr t ht ht1).1) hray
    have heq := hbij.injOn (sg_mem (mem_closedBall_zero_iff.1 (hD h e he (1 * s)
      (by rw [one_mul, abs_of_pos hs]; exact hs1))))
      (sg_mem (mem_closedBall_zero_iff.1 (hD h' e' he' (ε * t) (by
        rw [abs_mul]; rcases hε with rfl | rfl <;> simp [abs_of_pos ht] <;> linarith)))) hst
    have := congrArg (fun x : c0Sum E => (x : lp E ⊤) h) heq
    simp only [sg_self, sg_ne _ hhh] at this
    have he0 : e ≠ 0 := norm_ne_zero_iff.1 (by rw [he]; norm_num)
    rcases smul_eq_zero.1 this with h1 | h1
    · linarith
    · exact he0 h1
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · refine key (-1) (Or.inr rfl) fun t ht ht1 => ?_
    have h' : OnRay (F (sg h' (-(t • e')))) m ((-c) • v) := by
      rw [neg_smul, ← hc]; exact (hr' t ht ht1).2
    have e1 : (-1 * t) • e' = -(t • e') := by rw [neg_one_mul, neg_smul]
    rw [e1]
    exact h'.smul (by linarith)
  · refine key 1 (Or.inl rfl) fun t ht ht1 => ?_
    have := (hr' t ht ht1).1
    rw [hc] at this
    rw [one_mul]
    exact this.smul hpos

include hbij hlip in
/-- Images of nonzero points of two scalar blocks feeding one target block are never opposite. -/
lemma scalar_not_opp {h h' : ι} (hhh : h ≠ h') (hh : Module.finrank ℝ (E h) = 1)
    (hh' : Module.finrank ℝ (E h') = 1) {e : E h} {e' : E h'} (he : ‖e‖ = 1) (he' : ‖e'‖ = 1)
    {m m' : κ} {v : E' m} {v' : E' m'} (hv : v ≠ 0) (hv' : v' ≠ 0) (hr : Rays F h e m v)
    (hr' : Rays F h' e' m' v') (hmm : m' = m) {a : E h} {a' : E h'} (ha : ‖a‖ ≤ 1) (ha0 : a ≠ 0)
    (ha' : ‖a'‖ ≤ 1) (ha'0 : a' ≠ 0) :
    ¬ Opp ((F (sg h a) : lp E' ⊤) m) ((F (sg h' a') : lp E' ⊤) m) := by
  subst hmm
  rintro ⟨μ, hμ, hμe⟩
  obtain ⟨-, c, hc0, hc⟩ := scalar_line hh he hr ha ha0
  obtain ⟨-, c', hc'0, hc'⟩ := scalar_line hh' he' hr' ha' ha'0
  refine scalar_lines_ne hbij hlip hhh he he' hv hv' hr hr' (c'⁻¹ * (-(μ * c))) ?_
  rw [hc, hc'] at hμe
  calc v' = c'⁻¹ • (c' • v') := by rw [smul_smul, inv_mul_cancel₀ hc'0, one_smul]
    _ = _ := by rw [hμe]; module

/-- Three pairwise independent vectors of a plane are all moved off zero by one functional. -/
lemma exists_psi {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (hW : Module.finrank ℝ W = 2) {v₁ v₂ v₃ : W} (h1 : v₁ ≠ 0) (h2 : v₂ ≠ 0)
    (h12 : ∀ c : ℝ, v₂ ≠ c • v₁) (h23 : ∀ c : ℝ, v₃ ≠ c • v₂) :
    ∃ ψ : StrongDual ℝ W, ψ v₁ ≠ 0 ∧ ψ v₂ ≠ 0 ∧ ψ v₃ ≠ 0 := by
  have hpt : ∀ g : StrongDual ℝ W, g ≠ 0 → ∃ a : W, g a = 1 := by
    intro g hg
    obtain ⟨a, ha⟩ : ∃ a, g a ≠ 0 := by
      by_contra hc; push Not at hc; exact hg (ContinuousLinearMap.ext hc)
    exact ⟨(g a)⁻¹ • a, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ ha]⟩
  obtain ⟨g₁, hg₁, hg₁v₂⟩ := exists_ne_zero_apply_eq_zero hW v₂ h2
  obtain ⟨g₂, hg₂, hg₂v₁⟩ := exists_ne_zero_apply_eq_zero hW v₁ h1
  have hg₁v₁ : g₁ v₁ ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := hpt g₁ hg₁
    obtain ⟨μ, hμ⟩ := exists_eq_smul_of_apply_eq_zero hW g₁ a v₂ v₁ ha h2 hg₁v₂ h0
    have hμ0 : μ ≠ 0 := by rintro rfl; exact h1 (by rw [hμ, zero_smul])
    exact h12 μ⁻¹ (by rw [hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul])
  have hg₂v₂ : g₂ v₂ ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := hpt g₂ hg₂
    obtain ⟨μ, hμ⟩ := exists_eq_smul_of_apply_eq_zero hW g₂ a v₁ v₂ ha h1 hg₂v₁ h0
    exact h12 μ hμ
  set c₁ := (g₁ v₁)⁻¹ • g₁
  set c₂ := (g₂ v₂)⁻¹ • g₂
  have e11 : c₁ v₁ = 1 := by simp [c₁, inv_mul_cancel₀ hg₁v₁]
  have e12 : c₁ v₂ = 0 := by simp [c₁, hg₁v₂]
  have e21 : c₂ v₁ = 0 := by simp [c₂, hg₂v₁]
  have e22 : c₂ v₂ = 1 := by simp [c₂, inv_mul_cancel₀ hg₂v₂]
  by_cases hA : c₁ v₃ + c₂ v₃ = 0
  · refine ⟨c₁ + (2 : ℝ) • c₂, ?_, ?_, ?_⟩
    · simp [e11, e21]
    · simp [e12, e22]
    · intro h3
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        at h3
      have hc₁ : c₁ v₃ = 0 := by linarith
      obtain ⟨μ, hμ⟩ := exists_eq_smul_of_apply_eq_zero hW c₁ v₁ v₂ v₃ e11 h2 e12 hc₁
      exact h23 μ hμ
  · refine ⟨c₁ + c₂, ?_, ?_, ?_⟩
    · simp [e11, e21]
    · simp [e12, e22]
    · simpa using hA

/-- Flipping the unit vector if necessary, the image of half of it is positive for `ψ`. -/
lemma flip_pos {h : ι} {e : E h} (he : ‖e‖ = 1) {m : κ} {v : E' m} (hr : Rays F h e m v)
    (ψ : StrongDual ℝ (E' m)) (hψ : ψ v ≠ 0) :
    ∃ e' : E h, ‖e'‖ = 1 ∧ ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1,
      (∀ l ≠ h, (x : lp E ⊤) l = 0) → (x : lp E ⊤) h = (1 / 2 : ℝ) • e' →
        (∀ l ≠ m, (F x : lp E' ⊤) l = 0) ∧ 0 < ψ ((F x : lp E' ⊤) m) := by
  rcases lt_or_gt_of_ne hψ with hneg | hpos
  · refine ⟨-e, by rw [norm_neg, he], fun x _ hx hxh => ?_⟩
    rw [eq_sg_of_supp hx, hxh, smul_neg]
    obtain ⟨h1, α, hα, h2⟩ := (hr (1 / 2) (by norm_num) (by norm_num)).2
    refine ⟨h1, ?_⟩
    rw [h2, map_smul, map_neg, smul_eq_mul]
    nlinarith
  · refine ⟨e, he, fun x _ hx hxh => ?_⟩
    rw [eq_sg_of_supp hx, hxh]
    obtain ⟨h1, α, hα, h2⟩ := (hr (1 / 2) (by norm_num) (by norm_num)).1
    refine ⟨h1, ?_⟩
    rw [h2, map_smul, smul_eq_mul]
    positivity

end Support

section Support2

variable {ι κ : Type*}
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {E' : κ → Type*} [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
  {F : c0Sum E → c0Sum E'}

lemma finite_big (x : c0Sum E) {ε : ℝ} (hε : 0 < ε) :
    {i | ¬ ‖(x : lp E ⊤) i‖ < ε}.Finite := by
  have hx : Filter.Tendsto (fun i => ‖(x : lp E ⊤) i‖) Filter.cofinite (nhds 0) := x.2
  exact Filter.eventually_cofinite.1 (hx.eventually_lt_const hε)

lemma norm_sub_sg_le {z : c0Sum E} (hz : ‖z‖ ≤ 1) {k : ι} {c : E k}
    (hzc : ‖(z : lp E ⊤) k - c‖ ≤ 1) : ‖z - sg k c‖ ≤ 1 := by
  refine norm_c0Sum_le zero_le_one fun l => ?_
  by_cases hl : l = k
  · subst hl; simpa [sg_self] using hzc
  · simpa [sg_ne _ hl] using (norm_apply_le z l).trans hz

/-- The images of `e` and `-e` are opposite. -/
lemma opp_pair {h : ι} {e : E h} {m m' : κ} {v : E' m'} (hv : v ≠ 0) (hr : Rays F h e m' v)
    (hm : m' = m) : (F (sg h e) : lp E' ⊤) m ≠ 0 ∧
      Opp ((F (sg h e) : lp E' ⊤) m) ((F (sg h (-e)) : lp E' ⊤) m) := by
  subst hm
  obtain ⟨-, α, hα, h1⟩ := (hr 1 one_pos le_rfl).1
  obtain ⟨-, β, hβ, h2⟩ := (hr 1 one_pos le_rfl).2
  rw [one_smul] at h1 h2
  refine ⟨by rw [h1]; exact smul_ne_zero hα.ne' hv, β / α, div_pos hβ hα, ?_⟩
  rw [h2, h1, smul_smul, div_mul_cancel₀ _ hα.ne', smul_neg]

lemma flip_pos' {h : ι} {e : E h} (he : ‖e‖ = 1) {m m' : κ} {v : E' m'} (hr : Rays F h e m' v)
    (hm : m' = m) (ψ : StrongDual ℝ (E' m)) (hψ : ψ ((F (sg h e) : lp E' ⊤) m) ≠ 0) :
    ∃ e' : E h, ‖e'‖ = 1 ∧ ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1,
      (∀ l ≠ h, (x : lp E ⊤) l = 0) → (x : lp E ⊤) h = (1 / 2 : ℝ) • e' →
        (∀ l ≠ m, (F x : lp E' ⊤) l = 0) ∧ 0 < ψ ((F x : lp E' ⊤) m) := by
  subst hm
  refine flip_pos he hr ψ fun h0 => hψ ?_
  obtain ⟨-, α, -, h1⟩ := (hr 1 one_pos le_rfl).1
  rw [one_smul] at h1
  rw [h1, map_smul, h0, smul_zero]

end Support2

end Sol_Plasticity_C0Sum_exists_blockEquiv_support

open Sol_Plasticity_C0Sum_exists_blockEquiv_support in
set_option maxHeartbeats 1000000 in
theorem solution {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
    (F : c0Sum E → c0Sum E')
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1)) :
    ∃ σ : ι → κ, Function.Surjective σ ∧
      (∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ n : κ,
        (∀ i, σ i = n → (x : lp E ⊤) i = 0) → (F x : lp E' ⊤) n = 0) ∧
      (∀ i, Module.finrank ℝ (E i) = 2 →
        Module.finrank ℝ (E' (σ i)) = 2 ∧ ∀ k, σ k = σ i → k = i) ∧
      (∀ h h', Module.finrank ℝ (E' (σ h)) = 1 → σ h' = σ h → h' = h) ∧
      (∀ a b c, σ a = σ b → σ a = σ c → a = b ∨ a = c ∨ b = c) := by
  classical
  -- the provisional block map
  have hex : ∀ i, ∃ j : κ, ∃ v : E' j, ∃ e : E i, Rec F i j ∧
      (Module.finrank ℝ (E i) = 2 → Module.finrank ℝ (E' j) = 2 ∧ Pkg F i j) ∧
      (Module.finrank ℝ (E i) = 1 → ‖e‖ = 1 ∧ v ≠ 0 ∧ Rays F i e j v) := by
    intro i
    rcases hE i with hi | ⟨hi, hpar⟩
    · obtain ⟨e, he⟩ : ∃ e : E i, ‖e‖ = 1 := by
        have : Nontrivial (E i) := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
        obtain ⟨w, hw⟩ := exists_ne (0 : E i)
        exact ⟨‖w‖⁻¹ • w, by
          rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)]⟩
      obtain ⟨m, v, hv, hr⟩ := scalar_rays hE' hbij hlip hi he
      exact ⟨m, v, e, rec_of_rays hbij hlip hi he hr, fun h2 => by omega, fun _ => ⟨he, hv, hr⟩⟩
    · obtain ⟨j, hj, hrec, hpkg⟩ :=
        Plasticity.C0Sum.exists_blockEquiv_front E E' hE' F hbij hlip i hi hpar
      refine ⟨j, 0, 0, fun a ha k hk => hrec _ (sg_mem ha) (fun k' hk' => sg_ne _ hk') k hk,
        fun _ => ⟨hj, ?_⟩, fun h1 => by omega⟩
      intro a ha0 ha
      obtain ⟨c₁, c₂, hc₁, hc₂, hcov, u, hu, hfar⟩ := hpkg a ha0 ha
      exact ⟨c₁, c₂, hc₁, hc₂, hcov, u, hu,
        hfar _ (sg_mem hc₁) (fun k hk => sg_ne _ hk) (Or.inl (sg_self _ _)),
        hfar _ (sg_mem hc₂) (fun k hk => sg_ne _ hk) (Or.inr (sg_self _ _))⟩
  choose σ v e hσ using hex
  have hrec : ∀ i, Rec F i (σ i) := fun i => (hσ i).1
  have hpos_dim : ∀ i, 0 < Module.finrank ℝ (E i) := fun i => by
    rcases hE i with h | ⟨h, _⟩ <;> omega
  have hnz : ∀ i (a : E i), ‖a‖ ≤ 1 → a ≠ 0 → (F (sg i a) : lp E' ⊤) (σ i) ≠ 0 := by
    intro i a ha ha0 h
    apply phi_ne_zero hbij hlip ha ha0
    refine c0_ext fun k => ?_
    by_cases hk : k = σ i
    · subst hk; rw [h]; rfl
    · rw [hrec i a ha k hk]; rfl
  -- planar blocks are alone in their target blocks
  have halone : ∀ i, Module.finrank ℝ (E i) = 2 → ∀ k, σ k = σ i → k = i := by
    intro i hi k hk
    by_contra hki
    have hρ := planar_open hbij hlip hi ((hσ i).2.1 hi).1 (hrec i)
    have hreck : Rec F k (σ i) := by rw [← hk]; exact hrec k
    exact planar_alone hbij hlip hki hρ hreck (hpos_dim k)
  have hscalar : ∀ h, Module.finrank ℝ (E h) = 1 →
      ‖e h‖ = 1 ∧ v h ≠ 0 ∧ Rays F h (e h) (σ h) (v h) := fun h hh => (hσ h).2.2 hh
  have hnotopp : ∀ h h', h ≠ h' → Module.finrank ℝ (E h) = 1 → Module.finrank ℝ (E h') = 1 →
      σ h' = σ h → ∀ a : E h, ‖a‖ ≤ 1 → a ≠ 0 → ∀ a' : E h', ‖a'‖ ≤ 1 → a' ≠ 0 →
        ¬ Opp ((F (sg h a) : lp E' ⊤) (σ h)) ((F (sg h' a') : lp E' ⊤) (σ h)) := by
    intro h h' hhh hh hh' hσσ a ha ha0 a' ha' ha'0
    obtain ⟨he, hv, hr⟩ := hscalar h hh
    obtain ⟨he', hv', hr'⟩ := hscalar h' hh'
    exact scalar_not_opp hbij hlip hhh hh hh' he he' hv hv' hr hr' hσσ ha ha0 ha' ha'0
  have hnotmul : ∀ h h', h ≠ h' → Module.finrank ℝ (E h) = 1 → Module.finrank ℝ (E h') = 1 →
      σ h' = σ h → ∀ c : ℝ,
        (F (sg h' (e h')) : lp E' ⊤) (σ h) ≠ c • (F (sg h (e h)) : lp E' ⊤) (σ h) := by
    intro h h' hhh hh hh' hσσ c hc
    obtain ⟨he, hv, hr⟩ := hscalar h hh
    obtain ⟨he', hv', hr'⟩ := hscalar h' hh'
    obtain ⟨hq0, μ, hμ, hq⟩ := opp_pair hv' hr' hσσ
    have he1 : ‖e h‖ ≤ 1 := he.le
    have he0 : e h ≠ 0 := norm_ne_zero_iff.1 (by rw [he]; norm_num)
    have he'1 : ‖e h'‖ ≤ 1 := he'.le
    have he'0 : e h' ≠ 0 := norm_ne_zero_iff.1 (by rw [he']; norm_num)
    have hc0 : c ≠ 0 := by rintro rfl; exact hq0 (by rw [hc, zero_smul])
    rcases lt_or_gt_of_ne hc0 with hneg | hpos
    · exact hnotopp h h' hhh hh hh' hσσ _ he1 he0 _ he'1 he'0
        ⟨-c, by linarith, by rw [hc, neg_smul, neg_neg]⟩
    · exact hnotopp h h' hhh hh hh' hσσ _ he1 he0 _ (by rw [norm_neg]; exact he'1)
        (neg_ne_zero.2 he'0) ⟨μ * c, mul_pos hμ hpos, by rw [hq, hc, smul_smul]⟩
  have hdim1 : ∀ h h', h' ≠ h → σ h' = σ h → Module.finrank ℝ (E h) = 1 ∧
      Module.finrank ℝ (E h') = 1 := by
    intro h h' hne hσσ
    constructor
    · rcases hE h with hh | ⟨hh, _⟩
      · exact hh
      · exact absurd (halone h hh h' hσσ) hne
    · rcases hE h' with hh' | ⟨hh', _⟩
      · exact hh'
      · exact absurd (halone h' hh' h hσσ.symm) (Ne.symm hne)
  -- scalar target blocks receive one block
  have hsc : ∀ h h', Module.finrank ℝ (E' (σ h)) = 1 → σ h' = σ h → h' = h := by
    intro h h' h1 hσσ
    by_contra hne
    obtain ⟨hh, hh'⟩ := hdim1 h h' hne hσσ
    obtain ⟨he, -, -⟩ := hscalar h hh
    have hp := hnz h (e h) he.le (norm_ne_zero_iff.1 (by rw [he]; norm_num))
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hp).1 h1
      ((F (sg h' (e h')) : lp E' ⊤) (σ h))
    exact hnotmul h h' (Ne.symm hne) hh hh' hσσ c hc.symm
  -- at most two blocks share a target block
  have hthree : ∀ a b c, σ a = σ b → σ a = σ c → a = b ∨ a = c ∨ b = c := by
    intro a b c hab hac
    by_contra hcon
    push Not at hcon
    obtain ⟨hab', hac', hbc'⟩ := hcon
    obtain ⟨ha, hb⟩ := hdim1 a b (Ne.symm hab') hab.symm
    obtain ⟨-, hc⟩ := hdim1 a c (Ne.symm hac') hac.symm
    have hm : Module.finrank ℝ (E' (σ a)) = 2 := by
      rcases hE' (σ a) with h1 | h2
      · exact absurd (hsc a b h1 hab.symm) (Ne.symm hab')
      · exact h2
    obtain ⟨hea, hva, hra⟩ := hscalar a ha
    obtain ⟨heb, hvb, hrb⟩ := hscalar b hb
    obtain ⟨hec, hvc, hrc⟩ := hscalar c hc
    have hpa := hnz a (e a) hea.le (norm_ne_zero_iff.1 (by rw [hea]; norm_num))
    have hpb : (F (sg b (e b)) : lp E' ⊤) (σ a) ≠ 0 := by
      rw [hab]; exact hnz b (e b) heb.le (norm_ne_zero_iff.1 (by rw [heb]; norm_num))
    have h12 := hnotmul a b hab' ha hb hab.symm
    have h23 : ∀ t : ℝ, (F (sg c (e c)) : lp E' ⊤) (σ a) ≠ t • (F (sg b (e b)) : lp E' ⊤) (σ a) := by
      rw [hab]; exact hnotmul b c hbc' hb hc (hac.symm.trans hab)
    obtain ⟨ψ, hψa, hψb, hψc⟩ := exists_psi hm hpa hpb h12 h23
    obtain ⟨ea', hea', hpa'⟩ := flip_pos' hea hra rfl ψ hψa
    obtain ⟨eb', heb', hpb'⟩ := flip_pos' heb hrb hab.symm ψ hψb
    obtain ⟨ec', hec', hpc'⟩ := flip_pos' hec hrc hac.symm ψ hψc
    refine Plasticity.C0Sum.exists_blockEquiv_three_feeders E E' F hbij hlip ![a, b, c] ?_ ?_
      (fun k => Fin.cases (motive := fun k => E (![a, b, c] k)) ea'
        (fun k => Fin.cases (motive := fun k => E (![a, b, c] k.succ)) eb'
          (fun k => Fin.cases (motive := fun k => E (![a, b, c] k.succ.succ)) ec'
            (fun k => k.elim0) k) k) k) ?_ (σ a) hm ψ ?_
    · intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first
        | rfl
        | exact absurd hij hab' | exact absurd hij.symm hab'
        | exact absurd hij hac' | exact absurd hij.symm hac'
        | exact absurd hij hbc' | exact absurd hij.symm hbc'
    · intro k
      fin_cases k
      · exact ha
      · exact hb
      · exact hc
    · intro k
      fin_cases k
      · exact hea'
      · exact heb'
      · exact hec'
    · intro k
      fin_cases k
      · exact hpa'
      · exact hpb'
      · exact hpc'
  -- forward support for finitely supported points
  have hfin : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ S : Finset ι,
      (∀ i ∉ S, (x : lp E ⊤) i = 0) → ∀ n, (∀ i ∈ S, σ i = n → (x : lp E ⊤) i = 0) →
        (F x : lp E' ⊤) n = 0 := by
    intro x hx S hS n hn
    by_contra hFn
    have hxn := mem_closedBall_zero_iff.1 hx
    have hxi : ∀ i, ‖(x : lp E ⊤) i‖ ≤ 1 := fun i => (norm_apply_le x i).trans hxn
    have hauxex : ∀ i, ∃ c : Fin 2 → E i, (x : lp E ⊤) i ≠ 0 → (∀ l, ‖c l‖ ≤ 1) ∧
        Metric.closedBall (0 : E i) 1 ⊆ Metric.closedBall ((x : lp E ⊤) i) 1 ∪
          Metric.closedBall (c 0) 1 ∪ Metric.closedBall (c 1) 1 ∧
        (Module.finrank ℝ (E i) = 2 → ∃ u : E' (σ i), ‖u‖ ≤ 1 ∧
          ∀ l, 1 < ‖u - (F (sg i (c l)) : lp E' ⊤) (σ i)‖) ∧
        (Module.finrank ℝ (E i) = 1 → ∀ l, c l ≠ 0 ∧ c l = c 0) := by
      intro i
      by_cases hx0 : (x : lp E ⊤) i = 0
      · exact ⟨fun _ => 0, fun h => absurd hx0 h⟩
      rcases hE i with hi | ⟨hi, _⟩
      · set a := (x : lp E ⊤) i
        have ha : 0 < ‖a‖ := norm_pos_iff.2 hx0
        set u : E i := ‖a‖⁻¹ • a
        have hu : ‖u‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ha.ne']
        have hau : a = ‖a‖ • u := by rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
        have hc : -((2 * ‖a‖)⁻¹ • a) = (-(1 / 2 : ℝ)) • u := by
          have h2 : (2 * ‖a‖)⁻¹ * ‖a‖ = 1 / 2 := by field_simp
          calc -((2 * ‖a‖)⁻¹ • a) = -((2 * ‖a‖)⁻¹ • (‖a‖ • u)) := by rw [← hau]
            _ = (-(1 / 2 : ℝ)) • u := by rw [smul_smul, h2, neg_smul]
        refine ⟨fun _ => -((2 * ‖a‖)⁻¹ • a), fun _ => ⟨fun l => ?_, fun z hz => ?_,
          fun h2 => by omega, fun _ l => ⟨?_, rfl⟩⟩⟩
        · rw [hc, norm_smul, hu]; norm_num
        · rw [mem_closedBall_zero_iff] at hz
          obtain ⟨t, rfl, ht⟩ := eq_smul_of_finrank_one hi hu z
          rw [ht, abs_le] at hz
          simp only [Set.mem_union, Metric.mem_closedBall, dist_eq_norm]
          by_cases h1 : ‖t • u - a‖ ≤ 1
          · exact Or.inl (Or.inl h1)
          · left; right
            rw [hc, ← sub_smul, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_le]
            rw [not_le, hau, ← sub_smul, norm_smul, hu, mul_one, Real.norm_eq_abs] at h1
            have hxa : ‖a‖ ≤ 1 := hxi i
            rcases le_or_gt 0 (t - ‖a‖) with h2 | h2
            · rw [abs_of_nonneg h2] at h1; linarith
            · rw [abs_of_neg h2] at h1; constructor <;> linarith
        · rw [hc]; exact smul_ne_zero (by norm_num) (norm_ne_zero_iff.1 (by rw [hu]; norm_num))
      · obtain ⟨-, hpkg⟩ := (hσ i).2.1 hi
        obtain ⟨c₁, c₂, hc₁, hc₂, hcov, u, hu, h1, h2⟩ := hpkg _ hx0 (hxi i)
        refine ⟨![c₁, c₂], fun _ => ⟨fun l => ?_, by simpa using hcov, fun _ => ⟨u, hu, fun l => ?_⟩,
          fun h1' => by omega⟩⟩
        · fin_cases l
          · exact hc₁
          · exact hc₂
        · fin_cases l
          · exact h1
          · exact h2
    choose aux haux using hauxex
    have hauxnz : ∀ i, (x : lp E ⊤) i ≠ 0 → Module.finrank ℝ (E i) = 1 → ∀ l,
        (F (sg i (aux i l)) : lp E' ⊤) (σ i) ≠ 0 := fun i hi0 hi1 l =>
      hnz i _ ((haux i hi0).1 l) ((haux i hi0).2.2.2 hi1 l).1
    have hu : ∀ n' : κ, ∃ w : E' n', ‖w‖ ≤ 1 ∧ ∀ i ∈ S, (x : lp E ⊤) i ≠ 0 → σ i = n' →
        ∀ l, 1 < ‖w - (F (sg i (aux i l)) : lp E' ⊤) n'‖ := by
      intro n'
      by_cases hP : ∃ i ∈ S, (x : lp E ⊤) i ≠ 0 ∧ σ i = n' ∧ Module.finrank ℝ (E i) = 2
      · obtain ⟨i, -, hi0, hin', hi2⟩ := hP
        subst hin'
        obtain ⟨u, hu, hfar⟩ := (haux i hi0).2.2.1 hi2
        refine ⟨u, hu, fun i' _ _ hi'n l => ?_⟩
        obtain rfl := halone i hi2 i' hi'n
        exact hfar l
      push Not at hP
      have hsc_i : ∀ i ∈ S, (x : lp E ⊤) i ≠ 0 → σ i = n' → Module.finrank ℝ (E i) = 1 :=
        fun i hiS hi0 hin => by
          rcases hE i with h | ⟨h, _⟩
          · exact h
          · exact absurd h (hP i hiS hi0 hin)
      by_cases hQ : ∃ i ∈ S, (x : lp E ⊤) i ≠ 0 ∧ σ i = n'
      · obtain ⟨h, hhS, hh0, hhn⟩ := hQ
        subst hhn
        have hh1 := hsc_i h hhS hh0 rfl
        have hsame : ∀ l, aux h l = aux h 0 := fun l => ((haux h hh0).2.2.2 hh1 l).2
        set p := (F (sg h (aux h 0)) : lp E' ⊤) (σ h)
        have hp : p ≠ 0 := hauxnz h hh0 hh1 0
        by_cases hR : ∃ h' ∈ S, (x : lp E ⊤) h' ≠ 0 ∧ σ h' = σ h ∧ h' ≠ h
        · obtain ⟨h', hh'S, hh'0, hh'n, hh'h⟩ := hR
          have hh'1 := hsc_i h' hh'S hh'0 hh'n
          have hsame' : ∀ l, aux h' l = aux h' 0 := fun l => ((haux h' hh'0).2.2.2 hh'1 l).2
          have hp' : (F (sg h' (aux h' 0)) : lp E' ⊤) (σ h) ≠ 0 := by
            rw [← hh'n]; exact hauxnz h' hh'0 hh'1 0
          obtain ⟨w, hw, hw1, hw2⟩ := exists_far_of_not_neg (hE' (σ h)) hp hp'
            (hnotopp h h' (Ne.symm hh'h) hh1 hh'1 hh'n _ ((haux h hh0).1 0)
              ((haux h hh0).2.2.2 hh1 0).1 _ ((haux h' hh'0).1 0)
              ((haux h' hh'0).2.2.2 hh'1 0).1)
          refine ⟨w, hw, fun i _ _ hin l => ?_⟩
          rcases hthree h h' i hh'n.symm hin.symm with h1 | h1 | h1
          · exact absurd h1.symm hh'h
          · subst h1; rw [hsame l]; exact hw1
          · subst h1; rw [hsame' l]; exact hw2
        · push Not at hR
          refine ⟨antipode p, norm_antipode_le p, fun i hiS hi0 hin l => ?_⟩
          obtain rfl := hR i hiS hi0 hin
          rw [hsame l]; exact one_lt_norm_antipode_sub_self hp
      · push Not at hQ
        exact ⟨0, by simp, fun i hiS hi0 hin => absurd hin (hQ i hiS hi0)⟩
    choose u hu using hu
    have hcovX : ∀ z ∈ Metric.closedBall (0 : c0Sum E) 1, ‖z - x‖ ≤ 1 ∨
        ∃ i ∈ S, (x : lp E ⊤) i ≠ 0 ∧ ∃ l, ‖z - sg i (aux i l)‖ ≤ 1 := by
      intro z hz
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      have hzn := mem_closedBall_zero_iff.1 hz
      obtain ⟨k, hk⟩ : ∃ k, 1 < ‖(z : lp E ⊤) k - (x : lp E ⊤) k‖ := by
        by_contra hk
        push Not at hk
        exact absurd (norm_c0Sum_le zero_le_one (fun k => by simpa using hk k)) (not_le.2 h1)
      have hzk := (norm_apply_le z k).trans hzn
      have hk0 : (x : lp E ⊤) k ≠ 0 := by
        intro h0; rw [h0, sub_zero] at hk; linarith
      have hkS : k ∈ S := by by_contra h; exact hk0 (hS k h)
      obtain ⟨-, hcov, -, -⟩ := haux k hk0
      have := hcov (mem_closedBall_zero_iff.2 hzk)
      simp only [Set.mem_union, Metric.mem_closedBall, dist_eq_norm] at this
      rcases this with (h | h) | h
      · linarith
      · exact absurd (norm_sub_sg_le hzn h) (not_le.2 (h2 k hkS hk0 0))
      · exact absurd (norm_sub_sg_le hzn h) (not_le.2 (h2 k hkS hk0 1))
    set y : c0Sum E' := ofFun (insert n (S.image σ))
      (Function.update u n (antipode ((F x : lp E' ⊤) n)))
    have hy : ‖y‖ ≤ 1 := by
      refine norm_ofFun_le _ _ fun k => ?_
      by_cases hk : k = n
      · subst hk; simp [norm_antipode_le]
      · rw [Function.update_of_ne hk]; exact (hu k).1
    obtain ⟨z, hz, hzy⟩ := hbij.surjOn (mem_closedBall_zero_iff.2 hy)
    rcases hcovX z hz with h1 | ⟨i, hiS, hi0, l, h1⟩
    · have := hlip.norm_sub_le hz hx
      rw [NNReal.coe_one, one_mul, hzy] at this
      have h2 := (norm_apply_le (y - F x) n).trans (this.trans h1)
      simp only [y, Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, ofFun_apply] at h2
      rw [if_pos (Finset.mem_insert_self _ _), Function.update_self] at h2
      linarith [one_lt_norm_antipode_sub_self hFn]
    · have hσn : σ i ≠ n := fun h => hi0 (hn i hiS h)
      have hauxD : ‖aux i l‖ ≤ 1 := (haux i hi0).1 l
      have := hlip.norm_sub_le hz (sg_mem hauxD)
      rw [NNReal.coe_one, one_mul, hzy] at this
      have h2 := (norm_apply_le (y - F (sg i (aux i l))) (σ i)).trans (this.trans h1)
      simp only [y, Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, ofFun_apply] at h2
      rw [if_pos (Finset.mem_insert_of_mem (Finset.mem_image_of_mem σ hiS)),
        Function.update_of_ne hσn] at h2
      linarith [(hu (σ i)).2 i hiS hi0 rfl l]
  -- forward support
  have hsupp : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ n,
      (∀ i, σ i = n → (x : lp E ⊤) i = 0) → (F x : lp E' ⊤) n = 0 := by
    intro x hx n hn
    have hxn := mem_closedBall_zero_iff.1 hx
    refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
    set S := (finite_big x hε).toFinset
    set xε : c0Sum E := ofFun S (fun k => (x : lp E ⊤) k)
    have hxε : xε ∈ Metric.closedBall (0 : c0Sum E) 1 :=
      mem_closedBall_zero_iff.2 (norm_ofFun_le _ _ fun k => (norm_apply_le x k).trans hxn)
    have hdist : ‖x - xε‖ ≤ ε := by
      refine norm_c0Sum_le hε.le fun k => ?_
      simp only [xε, Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, ofFun_apply]
      split_ifs with hk
      · simp; exact hε.le
      · simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hk
        simpa using hk.le
    have h0 : (F xε : lp E' ⊤) n = 0 := by
      refine hfin xε hxε S (fun i hi => ?_) n (fun i hiS hin => ?_)
      · simp [xε, ofFun_apply, hi]
      · simp [xε, ofFun_apply, hiS, hn i hin]
    have hl := hlip.norm_sub_le hx hxε
    rw [NNReal.coe_one, one_mul] at hl
    calc ‖(F x : lp E' ⊤) n‖ = ‖((F x - F xε : c0Sum E') : lp E' ⊤) n‖ := by simp [h0]
      _ ≤ ‖F x - F xε‖ := norm_apply_le _ _
      _ ≤ ε := hl.trans hdist
      _ = 0 + ε := by ring
  -- surjectivity
  have hsurj : Function.Surjective σ := by
    intro n
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw⟩ : ∃ w : E' n, w ≠ 0 := by
      have : Nontrivial (E' n) := Module.nontrivial_of_finrank_pos (R := ℝ)
        (by rcases hE' n with h | h <;> omega)
      exact exists_ne 0
    have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
    set w' : E' n := (2 * ‖w‖)⁻¹ • w
    have hw'n : ‖w'‖ ≤ 1 := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity), mul_inv, mul_assoc,
        inv_mul_cancel₀ hwn.ne']
      norm_num
    have hw'0 : w' ≠ 0 := smul_ne_zero (inv_ne_zero (by positivity)) hw
    obtain ⟨x, hx, hxy⟩ := hbij.surjOn (sg_mem hw'n)
    have := hsupp x hx n (fun i hi => absurd hi (hcon i))
    rw [hxy, sg_self] at this
    exact hw'0 this
  exact ⟨σ, hsurj, hsupp, fun i hi => ⟨((hσ i).2.1 hi).1, halone i hi⟩, hsc, hthree⟩
