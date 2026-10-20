-- Prove2me | solution 1 for Plasticity.C0Sum.isometryOn_of_support
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:04:10.517461+00:00
-- url     : https://prove2.me/submissions/28ad4a4f-d3dc-4e2c-92c6-780635f2c0e3

import Definitions.Def_Plasticity_C0Sum
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Theorems.Thm_Plasticity_Ext_FreudenthalHurewicz

open Plasticity

namespace Sol_Plasticity_C0Sum_isometryOn_of_support

open Classical

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- The function underlying `finsupp S g`. -/
noncomputable def finsuppFun (S : Finset ι) (g : ∀ i : S, E i) : ∀ i, E i :=
  fun i => if h : i ∈ S then g ⟨i, h⟩ else 0

omit [∀ i, NormedSpace ℝ (E i)] in
lemma norm_finsuppFun_le (S : Finset ι) (g : ∀ i : S, E i) (i : ι) :
    ‖finsuppFun S g i‖ ≤ ‖g‖ := by
  unfold finsuppFun
  split_ifs with h
  · exact norm_le_pi_norm g ⟨i, h⟩
  · simp

omit [∀ i, NormedSpace ℝ (E i)] in
lemma memℓp_finsuppFun (S : Finset ι) (g : ∀ i : S, E i) : Memℓp (finsuppFun S g) ⊤ := by
  refine memℓp_infty ⟨‖g‖, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact norm_finsuppFun_le S g i

lemma mem_c0Sum_finsuppFun (S : Finset ι) (g : ∀ i : S, E i) :
    (⟨finsuppFun S g, memℓp_finsuppFun S g⟩ : lp E ⊤) ∈ c0Sum E := by
  show Filter.Tendsto (fun i => ‖finsuppFun S g i‖) Filter.cofinite (nhds 0)
  refine tendsto_nhds_of_eventually_eq ?_
  refine Filter.eventually_cofinite.2 (S.finite_toSet.subset ?_)
  intro i hi
  by_contra h
  have h' : i ∉ S := fun h'' => h (Finset.mem_coe.2 h'')
  exact hi (by simp [finsuppFun, h'])

/-- The point of `c0Sum E` with blocks `g` on `S` and zero elsewhere. -/
noncomputable def finsupp (S : Finset ι) (g : ∀ i : S, E i) : c0Sum E :=
  ⟨⟨finsuppFun S g, memℓp_finsuppFun S g⟩, mem_c0Sum_finsuppFun S g⟩

lemma finsupp_apply (S : Finset ι) (g : ∀ i : S, E i) (i : ι) :
    ((finsupp S g : c0Sum E) : lp E ⊤) i = if h : i ∈ S then g ⟨i, h⟩ else 0 := rfl

lemma norm_c0Sum_le {x : c0Sum E} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖(x : lp E ⊤) i‖ ≤ C) :
    ‖x‖ ≤ C := by
  rw [Submodule.coe_norm]
  exact lp.norm_le_of_forall_le hC h

lemma norm_apply_le (x : c0Sum E) (i : ι) : ‖(x : lp E ⊤) i‖ ≤ ‖x‖ := by
  rw [Submodule.coe_norm]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ i

lemma lipschitz_finsupp (S : Finset ι) : LipschitzWith 1 (finsupp (E := E) S) := by
  refine LipschitzWith.of_dist_le_mul fun g h => ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  refine norm_c0Sum_le (norm_nonneg _) fun i => ?_
  rw [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, finsupp_apply, finsupp_apply]
  split_ifs with hi
  · exact norm_le_pi_norm (g - h) ⟨i, hi⟩
  · simp

/-- The finitely supported slice of the ball. -/
def slice (S : Finset ι) : Set (c0Sum E) :=
  {x | x ∈ Metric.closedBall 0 1 ∧ ∀ i ∉ S, (x : lp E ⊤) i = 0}

lemma isCompact_slice [∀ i, FiniteDimensional ℝ (E i)] (S : Finset ι) :
    IsCompact (slice (E := E) S) := by
  have hK : IsCompact (Metric.closedBall (0 : ∀ i : S, E i) 1) := isCompact_closedBall 0 1
  have heq : slice (E := E) S = finsupp S '' Metric.closedBall 0 1 := by
    ext x
    constructor
    · rintro ⟨hx, hx0⟩
      refine ⟨fun i => (x : lp E ⊤) i, ?_, ?_⟩
      · rw [mem_closedBall_zero_iff]
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
        exact (norm_apply_le x i).trans (mem_closedBall_zero_iff.1 hx)
      · apply Subtype.ext
        apply lp.ext
        funext i
        rw [finsupp_apply]
        split_ifs with hi
        · rfl
        · exact (hx0 i hi).symm
    · rintro ⟨g, hg, rfl⟩
      refine ⟨?_, fun i hi => ?_⟩
      · rw [mem_closedBall_zero_iff]
        exact norm_c0Sum_le zero_le_one fun i =>
          (norm_finsuppFun_le S g i).trans (mem_closedBall_zero_iff.1 hg)
      · rw [finsupp_apply, dif_neg hi]
  rw [heq]
  exact hK.image (lipschitz_finsupp S).continuous

/-- Truncation of `x` to the blocks in `S`. -/
noncomputable def trunc (S : Finset ι) (x : c0Sum E) : c0Sum E := finsupp S (fun i => (x : lp E ⊤) i)

lemma trunc_mem_slice (S : Finset ι) {x : c0Sum E} (hx : x ∈ Metric.closedBall 0 1) :
    trunc S x ∈ slice S := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [mem_closedBall_zero_iff] at hx ⊢
    refine norm_c0Sum_le zero_le_one fun i => ?_
    rw [trunc, finsupp_apply]
    split_ifs
    · exact (norm_apply_le x i).trans hx
    · simp
  · rw [trunc, finsupp_apply, dif_neg hi]

lemma norm_sub_trunc_le (S : Finset ι) (x : c0Sum E) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ i ∉ S, ‖(x : lp E ⊤) i‖ ≤ ε) : ‖x - trunc S x‖ ≤ ε := by
  refine norm_c0Sum_le hε fun i => ?_
  rw [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, trunc, finsupp_apply]
  split_ifs with hi
  · simp [hε]
  · simpa using h i hi

lemma finite_big (x : c0Sum E) {ε : ℝ} (hε : 0 < ε) :
    {i | ¬ ‖(x : lp E ⊤) i‖ < ε}.Finite := by
  have hx : Filter.Tendsto (fun i => ‖(x : lp E ⊤) i‖) Filter.cofinite (nhds 0) := x.2
  exact Filter.eventually_cofinite.1 (hx.eventually_lt_const hε)

end Sol_Plasticity_C0Sum_isometryOn_of_support

open Sol_Plasticity_C0Sum_isometryOn_of_support in
theorem solution {ι : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (F : c0Sum E → c0Sum E)
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (hsupp : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      (F x : lp E ⊤) i = 0 ↔ (x : lp E ⊤) i = 0) :
    ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ y ∈ Metric.closedBall (0 : c0Sum E) 1,
      ‖F x - F y‖ = ‖x - y‖ := by
  classical
  intro x hx y hy
  have hlip' : ∀ a ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ b ∈ Metric.closedBall (0 : c0Sum E) 1,
      ‖F a - F b‖ ≤ ‖a - b‖ := by
    intro a ha b hb
    simpa [dist_eq_norm] using hlip.dist_le_mul a ha b hb
  refine le_antisymm (hlip' x hx y hy) ?_
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / 4 := by positivity
  set S : Finset ι := (finite_big x hδ).toFinset ∪ (finite_big y hδ).toFinset with hS
  have hSx : ∀ i ∉ S, ‖(x : lp E ⊤) i‖ ≤ ε / 4 := by
    intro i hi
    by_contra h
    exact hi (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).2 fun h' => h h'.le))
  have hSy : ∀ i ∉ S, ‖(y : lp E ⊤) i‖ ≤ ε / 4 := by
    intro i hi
    by_contra h
    exact hi (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 fun h' => h h'.le))
  have hxt := norm_sub_trunc_le S x hδ.le hSx
  have hyt := norm_sub_trunc_le S y hδ.le hSy
  have htx := trunc_mem_slice S hx
  have hty := trunc_mem_slice S hy
  have hmaps : Set.MapsTo F (slice S) (slice S) := by
    rintro z ⟨hz, hz0⟩
    exact ⟨hbij.mapsTo hz, fun i hi => (hsupp z hz i).2 (hz0 i hi)⟩
  have hsurj : Set.SurjOn F (slice S) (slice S) := by
    rintro w ⟨hw, hw0⟩
    obtain ⟨z, hz, rfl⟩ := hbij.surjOn hw
    exact ⟨z, ⟨hz, fun i hi => (hsupp z hz i).1 (hw0 i hi)⟩, rfl⟩
  have key := Plasticity.Ext.FreudenthalHurewicz (slice S) (isCompact_slice S) F hmaps hsurj
    (hlip.mono fun z hz => hz.1) _ htx _ hty
  rw [dist_eq_norm, dist_eq_norm] at key
  have l1 := hlip' _ htx.1 x hx
  have l2 := hlip' y hy _ hty.1
  have a1 := norm_sub_le_norm_sub_add_norm_sub x (trunc S x) y
  have a2 := norm_sub_le_norm_sub_add_norm_sub (trunc S x) (trunc S y) y
  have a3 := norm_sub_le_norm_sub_add_norm_sub (F (trunc S x)) (F x) (F (trunc S y))
  have a4 := norm_sub_le_norm_sub_add_norm_sub (F x) (F y) (F (trunc S y))
  rw [norm_sub_rev (trunc S x) x] at l1
  rw [norm_sub_rev (trunc S y) y] at a2
  linarith
