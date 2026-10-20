-- Prove2me | solution 1 for Plasticity.C0Sum.eq_zero_of_map_eq_zero.of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:53.535293+00:00
-- url     : https://prove2.me/submissions/0a04638d-8c4d-41f9-9fd3-19428cc81809

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_C0Sum_eq_zero_of_map_eq_zero_comparison
import Theorems.Thm_Plasticity_Topology_isOpen_image_of_injOn_of_finrank_eq

/-!
No collapse from three block properties (CUB100 Proposition 5.1).

The helpers `finsuppFun`, `finsupp`, `norm_c0Sum_le`, `norm_apply_le`, `lipschitz_finsupp` and
`finite_big` are copied from the project's solution `Sol_Plasticity_C0Sum_isometryOn_of_support`.
-/

open Plasticity

namespace Sol_Plasticity_C0Sum_eq_zero_of_map_eq_zero_of_blocks

open Classical

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-! ### Plumbing for `c0Sum` -/

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

lemma finite_big (x : c0Sum E) {ε : ℝ} (hε : 0 < ε) :
    {i | ¬ ‖(x : lp E ⊤) i‖ < ε}.Finite := by
  have hx : Filter.Tendsto (fun i => ‖(x : lp E ⊤) i‖) Filter.cofinite (nhds 0) := x.2
  exact Filter.eventually_cofinite.1 (hx.eventually_lt_const hε)

lemma norm_sub_apply_le (a b : c0Sum E) (i : ι) :
    ‖(a : lp E ⊤) i - (b : lp E ⊤) i‖ ≤ ‖a - b‖ := by
  have := norm_apply_le (a - b) i
  rwa [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply] at this

lemma norm_sub_le_of_forall {a b : c0Sum E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖(a : lp E ⊤) i - (b : lp E ⊤) i‖ ≤ C) : ‖a - b‖ ≤ C := by
  refine norm_c0Sum_le hC fun i => ?_
  rw [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply]
  exact h i

/-- The point with blocks `g` on `S` and the blocks of `x` elsewhere. -/
noncomputable def upd (x : c0Sum E) (S : Finset ι) (g : ∀ i, E i) : c0Sum E :=
  x - finsupp S (fun i => (x : lp E ⊤) i) + finsupp S (fun i => g i)

lemma upd_apply (x : c0Sum E) (S : Finset ι) (g : ∀ i, E i) (i : ι) :
    ((upd x S g : c0Sum E) : lp E ⊤) i = if i ∈ S then g i else (x : lp E ⊤) i := by
  simp only [upd, Submodule.coe_add, Submodule.coe_sub, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply,
    Pi.sub_apply, finsupp_apply]
  split_ifs <;> simp

lemma norm_upd_le {x : c0Sum E} (hx : ‖x‖ ≤ 1) (S : Finset ι) {g : ∀ i, E i}
    (hg : ∀ i ∈ S, ‖g i‖ ≤ 1) : ‖upd x S g‖ ≤ 1 := by
  refine norm_c0Sum_le zero_le_one fun i => ?_
  rw [upd_apply]
  split_ifs with h
  · exact hg i h
  · exact (norm_apply_le x i).trans hx

/-- A positive lower bound for finitely many positive numbers. -/
lemma exists_pos_le_finset (J : Finset ι) (f : ι → ℝ) (hf : ∀ j ∈ J, 0 < f j) :
    ∃ m > 0, ∀ j ∈ J, m ≤ f j := by
  induction J using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨m, hm, hms⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min m (f a), lt_min hm (hf a (Finset.mem_insert_self _ _)), fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hms j hj)

/-! ### Two facts at extreme points -/

/-- (R1) at an extreme point `w` of the unit ball. -/
theorem eq_smul_of_extreme {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {w : V}
    (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {p : V} (hp : ‖p‖ ≤ s) (hpw : ‖p - w‖ ≤ 1 - s) :
    p = s • w := by
  have hs1' : (1 - s) ≠ 0 := by linarith
  have ha : s⁻¹ • p ∈ Metric.closedBall (0 : V) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs0.le)]
    calc s⁻¹ * ‖p‖ ≤ s⁻¹ * s := by gcongr
      _ = 1 := inv_mul_cancel₀ hs0.ne'
  have hb : (1 - s)⁻¹ • (w - p) ∈ Metric.closedBall (0 : V) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (by linarith)),
      norm_sub_rev]
    calc (1 - s)⁻¹ * ‖p - w‖ ≤ (1 - s)⁻¹ * (1 - s) := by gcongr
      _ = 1 := inv_mul_cancel₀ hs1'
  have hseg : w ∈ openSegment ℝ (s⁻¹ • p) ((1 - s)⁻¹ • (w - p)) := by
    refine ⟨s, 1 - s, hs0, by linarith, by ring, ?_⟩
    rw [smul_smul, smul_smul, mul_inv_cancel₀ hs0.ne', mul_inv_cancel₀ hs1', one_smul, one_smul]
    abel
  have := ((mem_extremePoints.1 hw).2 _ ha _ hb hseg).1
  rw [← this, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]

/-- Extreme points of the unit ball of a nonzero normed space are unit vectors. -/
theorem norm_eq_one_of_extreme {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {w : V} (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)) {v : V} (hv : v ≠ 0) :
    ‖w‖ = 1 := by
  have hw1 : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.1 hw.1
  by_contra hne
  have hlt : ‖w‖ < 1 := lt_of_le_of_ne hw1 hne
  by_cases hw0 : w = 0
  · -- `0` is the midpoint of `±v/‖v‖`
    set u := ‖v‖⁻¹ • v with hu
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
    have hseg : w ∈ openSegment ℝ u (-u) := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      rw [hw0, smul_neg, add_neg_cancel]
    have := ((mem_extremePoints.1 hw).2 u (by simp [hu1]) (-u) (by simp [hu1]) hseg).1
    rw [this] at hu1
    exact hne hu1
  · -- `w` is the midpoint of `(1 ± δ) w`
    have hn : 0 < ‖w‖ := norm_pos_iff.2 hw0
    set δ := (1 - ‖w‖) / ‖w‖ with hδ
    have hδ0 : 0 < δ := div_pos (by linarith) hn
    have hδn : δ * ‖w‖ = 1 - ‖w‖ := by rw [hδ]; field_simp
    have h1 : (1 + δ) • w ∈ Metric.closedBall (0 : V) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (by linarith)]
      nlinarith
    have h2 : (1 - δ) • w ∈ Metric.closedBall (0 : V) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs]
      rcases le_total 0 (1 - δ) with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · rw [abs_of_nonpos h]; nlinarith
    have hseg : w ∈ openSegment ℝ ((1 + δ) • w) ((1 - δ) • w) := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      rw [smul_smul, smul_smul, ← add_smul]
      ring_nf
      rw [one_smul]
    have := ((mem_extremePoints.1 hw).2 _ h1 _ h2 hseg).1
    have h3 : δ • w = 0 := by
      have : (1 + δ) • w - w = 0 := by rw [this, sub_self]
      rwa [add_smul, one_smul, add_sub_cancel_left] at this
    rcases smul_eq_zero.1 h3 with h | h
    · exact hδ0.ne' h
    · exact hw0 h

/-! ### Open images on finite slices -/

/-- Invariance of domain on the slice of points supported in a finite set `S`: every point of
the slice near `F b` is the image of a point of the ball near `b`. -/
lemma exists_preimage_near [∀ i, FiniteDimensional ℝ (E i)] (S : Finset ι)
    (F : c0Sum E → c0Sum E)
    (hinj : Set.InjOn F (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (hsupp : ∀ z ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ j,
      (z : lp E ⊤) j = 0 → (F z : lp E ⊤) j = 0)
    (b : c0Sum E) (hb : ‖b‖ < 1) (hbS : ∀ j ∉ S, (b : lp E ⊤) j = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ z : c0Sum E, (∀ j ∉ S, (z : lp E ⊤) j = 0) → ‖z - F b‖ < η →
      ∃ y ∈ Metric.closedBall (0 : c0Sum E) 1, ‖y - b‖ < δ ∧ F y = z := by
  -- the slice as the finite-dimensional space `P`
  let P := ∀ j : S, E j
  let emb : P → c0Sum E := finsupp S
  let proj : c0Sum E → P := fun z j => (z : lp E ⊤) j
  have hemb_cont : Continuous emb := (lipschitz_finsupp S).continuous
  have hproj_le : ∀ z z' : c0Sum E, ‖proj z - proj z'‖ ≤ ‖z - z'‖ := by
    intro z z'
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
    exact norm_sub_apply_le z z' j
  have hproj_cont : Continuous proj := by
    refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun z z' => ?_)
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact hproj_le z z'
  have hproj_emb : ∀ a : P, proj (emb a) = a := by
    intro a
    funext j
    show finsuppFun S a j = a j
    simp [finsuppFun, j.2]
  have hemb_proj : ∀ z : c0Sum E, (∀ j ∉ S, (z : lp E ⊤) j = 0) → emb (proj z) = z := by
    intro z hz
    apply Subtype.ext
    apply lp.ext
    funext j
    show finsuppFun S (fun j => (z : lp E ⊤) j) j = (z : lp E ⊤) j
    unfold finsuppFun
    split_ifs with hj
    · rfl
    · exact (hz j hj).symm
  have hsuppS : ∀ a : P, emb a ∈ Metric.closedBall (0 : c0Sum E) 1 →
      ∀ j ∉ S, (F (emb a) : lp E ⊤) j = 0 := by
    intro a ha j hj
    refine hsupp _ ha j ?_
    show finsuppFun S a j = 0
    simp [finsuppFun, hj]
  set δ' := min δ (1 - ‖b‖) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (by linarith)
  let U : Set P := emb ⁻¹' Metric.ball b δ'
  have hU : IsOpen U := Metric.isOpen_ball.preimage hemb_cont
  have hUB : ∀ a ∈ U, emb a ∈ Metric.closedBall (0 : c0Sum E) 1 := by
    intro a ha
    have ha' : ‖emb a - b‖ < δ' := by simpa [U, dist_eq_norm] using ha
    rw [mem_closedBall_zero_iff]
    have h1 : ‖emb a‖ ≤ ‖b‖ + ‖emb a - b‖ := by
      have := norm_add_le b (emb a - b)
      rwa [add_sub_cancel] at this
    have h2 : δ' ≤ 1 - ‖b‖ := min_le_right _ _
    linarith
  let f : P → P := fun a => proj (F (emb a))
  have hf : ContinuousOn f U :=
    hproj_cont.comp_continuousOn ((hlip.continuousOn).comp hemb_cont.continuousOn hUB)
  have hfinj : Set.InjOn f U := by
    intro a ha a' ha' hfa
    have h1 : F (emb a) = F (emb a') := by
      rw [← hemb_proj _ (hsuppS a (hUB a ha)), ← hemb_proj _ (hsuppS a' (hUB a' ha'))]
      exact congrArg emb hfa
    have h2 := hinj (hUB a ha) (hUB a' ha') h1
    rw [← hproj_emb a, ← hproj_emb a', h2]
  have hopen : IsOpen (f '' U) :=
    Plasticity.Topology.isOpen_image_of_injOn_of_finrank_eq rfl U hU f hf hfinj
  have hbU : proj b ∈ U := by
    show emb (proj b) ∈ Metric.ball b δ'
    rw [hemb_proj b hbS]
    exact Metric.mem_ball_self hδ'0
  have hfb : f (proj b) = proj (F b) := by
    show proj (F (emb (proj b))) = proj (F b)
    rw [hemb_proj b hbS]
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hopen (proj (F b)) ⟨proj b, hbU, hfb⟩
  refine ⟨η, hη, fun z hzS hz => ?_⟩
  have hmem : proj z ∈ f '' U := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    exact (hproj_le z (F b)).trans_lt hz
  obtain ⟨a, ha, hfa⟩ := hmem
  refine ⟨emb a, hUB a ha, ?_, ?_⟩
  · have ha' : ‖emb a - b‖ < δ' := by simpa [U, dist_eq_norm] using ha
    exact ha'.trans_le (min_le_left _ _)
  · rw [← hemb_proj _ (hsuppS a (hUB a ha)), ← hemb_proj z hzS]
    exact congrArg emb hfa

end Sol_Plasticity_C0Sum_eq_zero_of_map_eq_zero_of_blocks

open Sol_Plasticity_C0Sum_eq_zero_of_map_eq_zero_of_blocks in
theorem solution {ι : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (hcov : ∀ i, ∀ b : E i, ‖b‖ ≤ 1 → b ≠ 0 →
      ∃ e ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1), ‖b - e‖ < 1)
    (hdisp : ∀ i, ∀ b z : E i, ‖b‖ ≤ 1 → ‖z‖ ≤ 1 / 2 →
      (∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1), ‖b - w‖ ≤ 1 → ‖z - w‖ ≤ 1) →
      ‖b - (2 : ℝ) • z‖ ≤ 1)
    (hpin : ∀ i, ∀ q x : E i, ‖q‖ ≤ 1 → ‖q - (2 : ℝ) • x‖ ≤ 1 → ‖q - x‖ = 1 →
      ∃ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1), ‖w - (2 : ℝ) • x‖ ≤ 1 ∧
        ∃ t₀ > 0, ∀ t : ℝ, 0 < t → t < t₀ → ∃ ρ > 0, ∀ β y : E i,
          ‖β‖ ≤ ‖(1 - 2 * t) • x + t • w‖ → ‖β - w‖ ≤ 1 - t →
          ‖y - ((1 - 2 * t) • x + t • w)‖ < ρ →
          (∀ ω ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1),
            ‖β - ω‖ ≤ max 1 ‖y - ω‖) →
          ‖q - y‖ ≤ 1 - t)
    (F : c0Sum E → c0Sum E)
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (hnorm : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      ‖(F x : lp E ⊤) i‖ ≤ ‖(x : lp E ⊤) i‖)
    (hext : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      (F x : lp E ⊤) i ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1) →
        (x : lp E ⊤) i = (F x : lp E ⊤) i)
    (x : c0Sum E) (hx : x ∈ Metric.closedBall (0 : c0Sum E) 1) (i : ι)
    (hFx : (F x : lp E ⊤) i = 0) : (x : lp E ⊤) i = 0 := by
  classical
  by_contra hxi
  have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hx
  have hball : ∀ z ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ j, ‖(z : lp E ⊤) j‖ ≤ 1 :=
    fun z hz j => (norm_apply_le z j).trans (mem_closedBall_zero_iff.1 hz)
  have hlip' : ∀ a ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ b ∈ Metric.closedBall (0 : c0Sum E) 1,
      ‖F a - F b‖ ≤ ‖a - b‖ := by
    intro a ha b hb
    simpa [dist_eq_norm] using hlip.dist_le_mul a ha b hb
  have hcmp : ∀ z ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ j,
      ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E j) 1),
        ‖(F z : lp E ⊤) j - w‖ ≤ max 1 ‖(z : lp E ⊤) j - w‖ :=
    fun z hz j w hw => Plasticity.C0Sum.eq_zero_of_map_eq_zero.comparison E
      (fun j b hb hb0 => by obtain ⟨e, he, h1⟩ := hcov j b hb hb0; exact ⟨e, he, h1.le⟩)
      F hbij.surjOn hlip hext z hz j w hw
  -- displacement in the c₀ sum
  have hdispl : ∀ p ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ j, ‖(F p : lp E ⊤) j‖ ≤ 1 / 2 →
      ‖(p : lp E ⊤) j - (2 : ℝ) • (F p : lp E ⊤) j‖ ≤ 1 := by
    intro p hp j hz
    refine hdisp j _ _ (hball p hp j) hz fun w hw hpw => ?_
    exact (hcmp p hp j w hw).trans (max_le le_rfl hpw)
  have havg : ∀ {j} (a y : E j), ‖a‖ ≤ 1 → ‖a - (2 : ℝ) • y‖ ≤ 1 → ‖a - y‖ ≤ 1 := by
    intro j a y ha hay
    have e1 : a - y = (1 / 2 : ℝ) • (a + (a - (2 : ℝ) • y)) := by module
    rw [e1, norm_smul, Real.norm_of_nonneg (by norm_num)]
    have := norm_add_le a (a - (2 : ℝ) • y)
    linarith
  -- every point of a block ball is within one of an extreme point, strictly if it is nonzero
  have hcov' : ∀ j, ∀ b : E j, ‖b‖ ≤ 1 →
      ∃ e ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E j) 1),
        ‖b - e‖ ≤ 1 ∧ (b ≠ 0 → ‖b - e‖ < 1) := by
    intro j b hb
    by_cases hb0 : b = 0
    · subst hb0
      by_cases hnt : ∃ v : E j, v ≠ 0
      · obtain ⟨v, hv⟩ := hnt
        have hu : ‖‖v‖⁻¹ • v‖ = 1 := by
          rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
        obtain ⟨e, he, -⟩ := hcov j _ hu.le (by intro h; rw [h, norm_zero] at hu; simp at hu)
        refine ⟨e, he, ?_, fun h => absurd rfl h⟩
        rw [zero_sub, norm_neg]
        exact mem_closedBall_zero_iff.1 he.1
      · push Not at hnt
        refine ⟨0, ?_, by simp, fun h => absurd rfl h⟩
        rw [mem_extremePoints]
        exact ⟨by simp, fun a _ c _ _ => ⟨hnt a, hnt c⟩⟩
    · obtain ⟨e, he, h⟩ := hcov j b hb hb0
      exact ⟨e, he, h.le, fun _ => h⟩
  -- extreme points near the blocks of `x`
  choose e he hxe hxe' using fun j => hcov' j ((x : lp E ⊤) j) (hball x hx j)
  have he1 : ∀ j, ‖e j‖ ≤ 1 := fun j => mem_closedBall_zero_iff.1 (he j).1
  -- `T`: the head `i` and the blocks where `x` is larger than one half
  set T : Finset ι := insert i (finite_big x (by norm_num : (0 : ℝ) < 1 / 2)).toFinset with hTdef
  have hiT : i ∈ T := Finset.mem_insert_self _ _
  have hT : ∀ j ∉ T, ‖(x : lp E ⊤) j‖ ≤ 1 / 2 := by
    intro j hj
    by_contra h
    exact hj (Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 (fun h' => h h'.le)))
  have hTne : ∀ j ∈ T, (x : lp E ⊤) j ≠ 0 := by
    intro j hj h0
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hxi h0
    · have := (Set.Finite.mem_toFinset _).1 hj
      simp only [Set.mem_ofPred_eq, h0, norm_zero, not_lt] at this
      norm_num at this
  -- the first lift `q`
  set v := upd x T e with hv
  have hvB : v ∈ Metric.closedBall (0 : c0Sum E) 1 :=
    mem_closedBall_zero_iff.2 (norm_upd_le hx1 T fun j _ => he1 j)
  obtain ⟨q, hqB, hFq⟩ := hbij.surjOn hvB
  have hFqj : ∀ j, (F q : lp E ⊤) j = if j ∈ T then e j else (x : lp E ⊤) j := by
    intro j; rw [hFq, hv, upd_apply]
  have hqT : ∀ j ∈ T, (q : lp E ⊤) j = e j := by
    intro j hj
    have h1 : (F q : lp E ⊤) j = e j := by rw [hFqj, if_pos hj]
    rw [hext q hqB j (by rw [h1]; exact he j), h1]
  have hq2 : ∀ j ∉ T, ‖(q : lp E ⊤) j - (2 : ℝ) • (x : lp E ⊤) j‖ ≤ 1 := by
    intro j hj
    have h1 : (F q : lp E ⊤) j = (x : lp E ⊤) j := by rw [hFqj, if_neg hj]
    have := hdispl q hqB j (by rw [h1]; exact hT j hj)
    rwa [h1] at this
  have hqx : ∀ j, ‖(q : lp E ⊤) j - (x : lp E ⊤) j‖ ≤ 1 := by
    intro j
    by_cases hj : j ∈ T
    · rw [hqT j hj, norm_sub_rev]; exact hxe j
    · exact havg _ _ (hball q hqB j) (hq2 j hj)
  have hqxT : ∀ j ∈ T, ‖(q : lp E ⊤) j - (x : lp E ⊤) j‖ < 1 := by
    intro j hj
    rw [hqT j hj, norm_sub_rev]
    exact hxe' j (hTne j hj)
  -- the pins `J` and the bound `d < 1` at the other blocks
  have hqx_apply : ∀ j, ((q - x : c0Sum E) : lp E ⊤) j = (q : lp E ⊤) j - (x : lp E ⊤) j := by
    intro j; rw [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply]
  set A : Finset ι := (finite_big (q - x) (by norm_num : (0 : ℝ) < 1 / 2)).toFinset with hA
  set J : Finset ι := A.filter (fun j => ‖(q : lp E ⊤) j - (x : lp E ⊤) j‖ = 1) with hJdef
  have hJ : ∀ j, j ∈ J ↔ ‖(q : lp E ⊤) j - (x : lp E ⊤) j‖ = 1 := by
    intro j
    rw [hJdef, Finset.mem_filter, hA, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hqx_apply]
    constructor
    · exact And.right
    · intro h; refine ⟨?_, h⟩; rw [h]; norm_num
  have hJT : ∀ j ∈ J, j ∉ T := by
    intro j hj hjT
    have := hqxT j hjT
    rw [(hJ j).1 hj] at this
    exact lt_irrefl _ this
  obtain ⟨d, hd12, hd1, hd⟩ : ∃ d : ℝ, 1 / 2 ≤ d ∧ d < 1 ∧
      ∀ j ∉ J, ‖(q : lp E ⊤) j - (x : lp E ⊤) j‖ ≤ d := by
    obtain ⟨m, hm, hmA⟩ := exists_pos_le_finset (A.filter (fun j => j ∉ J))
      (fun j => 1 - ‖(q : lp E ⊤) j - (x : lp E ⊤) j‖) (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have h2 : ‖(q : lp E ⊤) j - (x : lp E ⊤) j‖ ≠ 1 := fun h => hj.2 ((hJ j).2 h)
        have := lt_of_le_of_ne (hqx j) h2
        linarith)
    refine ⟨max (1 / 2) (1 - m), le_max_left _ _, max_lt (by norm_num) (by linarith),
      fun j hj => ?_⟩
    by_cases hjA : j ∈ A
    · have := hmA j (Finset.mem_filter.2 ⟨hjA, hj⟩)
      exact le_trans (by linarith) (le_max_right _ _)
    · have : ‖((q - x : c0Sum E) : lp E ⊤) j‖ < 1 / 2 := by
        by_contra h
        exact hjA ((Set.Finite.mem_toFinset _).2 h)
      rw [hqx_apply] at this
      exact le_trans this.le (le_max_left _ _)
  -- pin data
  have hpinJ : ∀ j, j ∈ J → ∃ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E j) 1),
      ‖w - (2 : ℝ) • (x : lp E ⊤) j‖ ≤ 1 ∧
        ∃ t₀ > 0, ∀ t : ℝ, 0 < t → t < t₀ → ∃ ρ > 0, ∀ β y : E j,
          ‖β‖ ≤ ‖(1 - 2 * t) • (x : lp E ⊤) j + t • w‖ → ‖β - w‖ ≤ 1 - t →
          ‖y - ((1 - 2 * t) • (x : lp E ⊤) j + t • w)‖ < ρ →
          (∀ ω ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E j) 1),
            ‖β - ω‖ ≤ max 1 ‖y - ω‖) →
          ‖(q : lp E ⊤) j - y‖ ≤ 1 - t :=
    fun j hj => hpin j _ _ (hball q hqB j) (hq2 j (hJT j hj)) ((hJ j).1 hj)
  choose! w hw hw2 t₀ ht₀ hρpin using hpinJ
  -- the second lift `r`
  set g' : ∀ j, E j := fun j => if j ∈ T then e j else w j with hg'
  set v' := upd x (T ∪ J) g' with hv'
  have hv'B : v' ∈ Metric.closedBall (0 : c0Sum E) 1 := by
    refine mem_closedBall_zero_iff.2 (norm_upd_le hx1 _ fun j hj => ?_)
    rw [hg']
    dsimp only
    split_ifs with hjT
    · exact he1 j
    · have hjJ : j ∈ J := by
        rcases Finset.mem_union.1 hj with h | h
        · exact absurd h hjT
        · exact h
      exact mem_closedBall_zero_iff.1 (hw j hjJ).1
  obtain ⟨r, hrB, hFr⟩ := hbij.surjOn hv'B
  have hFrj : ∀ j, (F r : lp E ⊤) j = if j ∈ T ∪ J then g' j else (x : lp E ⊤) j := by
    intro j; rw [hFr, hv', upd_apply]
  have hFrJ : ∀ j ∈ J, (F r : lp E ⊤) j = w j := by
    intro j hj
    rw [hFrj, if_pos (Finset.mem_union_right _ hj), hg']
    dsimp only
    rw [if_neg (hJT j hj)]
  have hrJ : ∀ j ∈ J, (r : lp E ⊤) j = w j := by
    intro j hj
    rw [hext r hrB j (by rw [hFrJ j hj]; exact hw j hj), hFrJ j hj]
  have hrT : ∀ j ∈ T, (r : lp E ⊤) j = e j := by
    intro j hj
    have h1 : (F r : lp E ⊤) j = e j := by
      rw [hFrj, if_pos (Finset.mem_union_left _ hj), hg']
      dsimp only
      rw [if_pos hj]
    rw [hext r hrB j (by rw [h1]; exact he j), h1]
  have hr2 : ∀ j ∉ T, ‖(r : lp E ⊤) j - (2 : ℝ) • (x : lp E ⊤) j‖ ≤ 1 := by
    intro j hj
    by_cases hjJ : j ∈ J
    · rw [hrJ j hjJ]; exact hw2 j hjJ
    · have h1 : (F r : lp E ⊤) j = (x : lp E ⊤) j := by
        rw [hFrj, if_neg (by simp [hj, hjJ])]
      have := hdispl r hrB j (by rw [h1]; exact hT j hj)
      rwa [h1] at this
  have hrx : ∀ j ∉ T, ‖(r : lp E ⊤) j - (x : lp E ⊤) j‖ ≤ 1 :=
    fun j hj => havg _ _ (hball r hrB j) (hr2 j hj)
  -- the parameter `t`
  obtain ⟨m, hm, hmJ⟩ := exists_pos_le_finset J t₀ (fun j hj => ht₀ j hj)
  set t := min (m / 2) ((1 - d) / 4) with ht
  have ht0 : 0 < t := lt_min (by linarith) (by linarith)
  have htm : ∀ j ∈ J, t < t₀ j := fun j hj =>
    lt_of_le_of_lt (min_le_left _ _) (by linarith [hmJ j hj])
  have htd : d + 2 * t < 1 := by
    have : t ≤ (1 - d) / 4 := min_le_right _ _
    linarith
  have ht12 : t < 1 / 2 := by linarith
  have hρJ : ∀ j, j ∈ J → ∃ ρ > 0, ∀ β y : E j,
      ‖β‖ ≤ ‖(1 - 2 * t) • (x : lp E ⊤) j + t • w j‖ → ‖β - w j‖ ≤ 1 - t →
      ‖y - ((1 - 2 * t) • (x : lp E ⊤) j + t • w j)‖ < ρ →
      (∀ ω ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E j) 1), ‖β - ω‖ ≤ max 1 ‖y - ω‖) →
      ‖(q : lp E ⊤) j - y‖ ≤ 1 - t :=
    fun j hj => hρpin j hj t ht0 (htm j hj)
  choose! ρ hρ0 hρ using hρJ
  -- the comparison point `b`, supported in the finite set `S'`
  set S' : Finset ι := T ∪ J ∪ (finite_big x ht0).toFinset ∪ (finite_big r ht0).toFinset ∪
    (finite_big q ht0).toFinset with hS'
  have hTS' : ∀ j ∈ T, j ∈ S' := fun j hj => by simp [hS', hj]
  have hJS' : ∀ j ∈ J, j ∈ S' := fun j hj => by simp [hS', hj]
  have hsmall : ∀ z : c0Sum E, ∀ j, ¬ ‖(z : lp E ⊤) j‖ < t → j ∈ (finite_big z ht0).toFinset :=
    fun z j h => (Set.Finite.mem_toFinset _).2 h
  have hS'x : ∀ j ∉ S', ‖(x : lp E ⊤) j‖ < t := by
    intro j hj; by_contra h; exact hj (by simp only [hS', Finset.mem_union]; tauto)
  have hS'r : ∀ j ∉ S', ‖(r : lp E ⊤) j‖ < t := by
    intro j hj; by_contra h; exact hj (by simp only [hS', Finset.mem_union]; have := hsmall r j h; tauto)
  have hS'q : ∀ j ∉ S', ‖(q : lp E ⊤) j‖ < t := by
    intro j hj; by_contra h; exact hj (by simp only [hS', Finset.mem_union]; have := hsmall q j h; tauto)
  set b0 : ∀ j, E j := fun j =>
    if j ∈ T then (1 - t) • (x : lp E ⊤) j else (1 - 2 * t) • (x : lp E ⊤) j + t • (r : lp E ⊤) j
    with hb0
  set b : c0Sum E := finsupp S' (fun j => b0 j) with hbdef
  have hbj : ∀ j, (b : lp E ⊤) j = if j ∈ S' then b0 j else 0 := by
    intro j
    rw [hbdef, finsupp_apply]
    split_ifs <;> rfl
  have hbT : ∀ j ∈ T, (b : lp E ⊤) j = (1 - t) • (x : lp E ⊤) j := by
    intro j hj
    rw [hbj, if_pos (hTS' j hj), hb0]
    dsimp only
    rw [if_pos hj]
  have hbS : ∀ j ∈ S', j ∉ T →
      (b : lp E ⊤) j = (1 - 2 * t) • (x : lp E ⊤) j + t • (r : lp E ⊤) j := by
    intro j hj hjT
    rw [hbj, if_pos hj, hb0]
    dsimp only
    rw [if_neg hjT]
  have hbO : ∀ j ∉ S', (b : lp E ⊤) j = 0 := by
    intro j hj
    rw [hbj, if_neg hj]
  have hbJ : ∀ j ∈ J,
      (b : lp E ⊤) j = (1 - 2 * t) • (x : lp E ⊤) j + t • w j := by
    intro j hj
    rw [hbS j (hJS' j hj) (hJT j hj), hrJ j hj]
  have h12t : 0 ≤ 1 - 2 * t := by linarith
  have h1t : 0 ≤ 1 - t := by linarith
  -- block estimates at `b`
  have hE1 : ∀ j, ‖(b : lp E ⊤) j‖ ≤ 1 - t := by
    intro j
    by_cases hjS : j ∈ S'
    · by_cases hjT : j ∈ T
      · rw [hbT j hjT, norm_smul, Real.norm_of_nonneg h1t]
        have := mul_le_mul_of_nonneg_left (hball x hx j) h1t
        linarith
      · rw [hbS j hjS hjT]
        have h1 := norm_add_le ((1 - 2 * t) • (x : lp E ⊤) j) (t • (r : lp E ⊤) j)
        rw [norm_smul, norm_smul, Real.norm_of_nonneg h12t, Real.norm_of_nonneg ht0.le] at h1
        have h2 := mul_le_mul_of_nonneg_left (hT j hjT) h12t
        have h3 := mul_le_mul_of_nonneg_left (hball r hrB j) ht0.le
        linarith
    · rw [hbO j hjS, norm_zero]; exact h1t
  have hE2 : ∀ j, ‖(b : lp E ⊤) j - (x : lp E ⊤) j‖ ≤ t := by
    intro j
    by_cases hjS : j ∈ S'
    · by_cases hjT : j ∈ T
      · rw [hbT j hjT]
        have e1 : (1 - t) • (x : lp E ⊤) j - (x : lp E ⊤) j = -(t • (x : lp E ⊤) j) := by module
        rw [e1, norm_neg, norm_smul, Real.norm_of_nonneg ht0.le]
        have := mul_le_mul_of_nonneg_left (hball x hx j) ht0.le
        linarith
      · rw [hbS j hjS hjT]
        have e1 : (1 - 2 * t) • (x : lp E ⊤) j + t • (r : lp E ⊤) j - (x : lp E ⊤) j =
            t • ((r : lp E ⊤) j - (2 : ℝ) • (x : lp E ⊤) j) := by module
        rw [e1, norm_smul, Real.norm_of_nonneg ht0.le]
        have := mul_le_mul_of_nonneg_left (hr2 j hjT) ht0.le
        linarith
    · rw [hbO j hjS, zero_sub, norm_neg]; exact (hS'x j hjS).le
  have hE3 : ∀ j, ‖(b : lp E ⊤) j - (r : lp E ⊤) j‖ ≤ 1 - t := by
    intro j
    by_cases hjS : j ∈ S'
    · by_cases hjT : j ∈ T
      · rw [hbT j hjT, hrT j hjT]
        have e1 : (1 - t) • (x : lp E ⊤) j - e j =
            (1 - t) • ((x : lp E ⊤) j - e j) - t • e j := by module
        have h1 := norm_sub_le ((1 - t) • ((x : lp E ⊤) j - e j)) (t • e j)
        rw [norm_smul, norm_smul, Real.norm_of_nonneg h1t, Real.norm_of_nonneg ht0.le] at h1
        have hjJ : j ∉ J := fun h => hJT j h hjT
        have h2 : ‖(x : lp E ⊤) j - e j‖ ≤ d := by
          have := hd j hjJ
          rwa [hqT j hjT, norm_sub_rev] at this
        have h3 := mul_le_mul_of_nonneg_left h2 h1t
        have h4 := mul_le_mul_of_nonneg_left (he1 j) ht0.le
        rw [e1]
        nlinarith [mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ d)]
      · rw [hbS j hjS hjT]
        have e1 : (1 - 2 * t) • (x : lp E ⊤) j + t • (r : lp E ⊤) j - (r : lp E ⊤) j =
            (1 - 2 * t) • ((x : lp E ⊤) j - (r : lp E ⊤) j) - t • (r : lp E ⊤) j := by module
        have h1 := norm_sub_le ((1 - 2 * t) • ((x : lp E ⊤) j - (r : lp E ⊤) j))
          (t • (r : lp E ⊤) j)
        rw [norm_smul, norm_smul, Real.norm_of_nonneg h12t, Real.norm_of_nonneg ht0.le] at h1
        have h2 : ‖(x : lp E ⊤) j - (r : lp E ⊤) j‖ ≤ 1 := by
          rw [norm_sub_rev]; exact hrx j hjT
        have h3 := mul_le_mul_of_nonneg_left h2 h12t
        have h4 := mul_le_mul_of_nonneg_left (hball r hrB j) ht0.le
        rw [e1]
        linarith
    · rw [hbO j hjS, zero_sub, norm_neg]; linarith [hS'r j hjS]
  have hE4 : ∀ j ∉ J, ‖(q : lp E ⊤) j - (b : lp E ⊤) j‖ ≤ d + t := by
    intro j hjJ
    by_cases hjS : j ∈ S'
    · by_cases hjT : j ∈ T
      · rw [hbT j hjT]
        have e1 : (q : lp E ⊤) j - (1 - t) • (x : lp E ⊤) j =
            ((q : lp E ⊤) j - (x : lp E ⊤) j) + t • (x : lp E ⊤) j := by module
        have h1 := norm_add_le ((q : lp E ⊤) j - (x : lp E ⊤) j) (t • (x : lp E ⊤) j)
        rw [norm_smul, Real.norm_of_nonneg ht0.le] at h1
        have h4 := mul_le_mul_of_nonneg_left (hball x hx j) ht0.le
        rw [e1]
        linarith [hd j hjJ]
      · rw [hbS j hjS hjT]
        have e1 : (q : lp E ⊤) j - ((1 - 2 * t) • (x : lp E ⊤) j + t • (r : lp E ⊤) j) =
            ((q : lp E ⊤) j - (x : lp E ⊤) j) -
              t • ((r : lp E ⊤) j - (2 : ℝ) • (x : lp E ⊤) j) := by module
        have h1 := norm_sub_le ((q : lp E ⊤) j - (x : lp E ⊤) j)
          (t • ((r : lp E ⊤) j - (2 : ℝ) • (x : lp E ⊤) j))
        rw [norm_smul, Real.norm_of_nonneg ht0.le] at h1
        have h4 := mul_le_mul_of_nonneg_left (hr2 j hjT) ht0.le
        rw [e1]
        linarith [hd j hjJ]
    · rw [hbO j hjS, sub_zero]; linarith [hS'q j hjS]
  have hbn : ‖b‖ ≤ 1 - t := norm_c0Sum_le h1t hE1
  have hbB : b ∈ Metric.closedBall (0 : c0Sum E) 1 := mem_closedBall_zero_iff.2 (by linarith)
  have hbx : ‖b - x‖ ≤ t := norm_sub_le_of_forall ht0.le hE2
  have hbr : ‖b - r‖ ≤ 1 - t := norm_sub_le_of_forall h1t hE3
  -- values at `b` on the pins
  have hβ1 : ∀ z ∈ Metric.closedBall (0 : c0Sum E) 1, (F z : lp E ⊤) = (F b : lp E ⊤) →
      ∀ j ∈ J, ‖(F z : lp E ⊤) j‖ ≤ ‖(1 - 2 * t) • (x : lp E ⊤) j + t • w j‖ := by
    intro z _ hz j hj
    rw [hz, ← hbJ j hj]
    exact hnorm b hbB j
  have hβ2 : ∀ j ∈ J, ‖(F b : lp E ⊤) j - w j‖ ≤ 1 - t := by
    intro j hj
    have := norm_sub_apply_le (F b) (F r) j
    rw [hFrJ j hj] at this
    exact this.trans ((hlip' b hbB r hrB).trans hbr)
  have hqbJ : ∀ j ∈ J, ‖(q : lp E ⊤) j - (b : lp E ⊤) j‖ ≤ 1 - t := by
    intro j hj
    refine hρ j hj ((F b : lp E ⊤) j) ((b : lp E ⊤) j) (hβ1 b hbB rfl j hj) (hβ2 j hj) ?_
      (fun ω hω => hcmp b hbB j ω hω)
    rw [← hbJ j hj, sub_self, norm_zero]
    exact hρ0 j hj
  have hqb : ‖q - b‖ ≤ 1 - t := by
    refine norm_sub_le_of_forall h1t fun j => ?_
    by_cases hj : j ∈ J
    · exact hqbJ j hj
    · linarith [hE4 j hj]
  -- the head: `F(b)_i = t e_i`
  have hFbi : (F b : lp E ⊤) i = t • e i := by
    refine eq_smul_of_extreme (he i) ht0 (by linarith) ?_ ?_
    · have := norm_sub_apply_le (F b) (F x) i
      rw [hFx, sub_zero] at this
      exact this.trans ((hlip' b hbB x hx).trans hbx)
    · have := norm_sub_apply_le (F b) (F q) i
      rw [hFqj, if_pos hiT] at this
      refine this.trans ((hlip' b hbB q hqB).trans ?_)
      rw [norm_sub_rev]; exact hqb
  have hei : ‖e i‖ = 1 := norm_eq_one_of_extreme (he i) hxi
  -- an open neighbourhood of `F b` in the slice
  obtain ⟨m', hm', hm'J⟩ := exists_pos_le_finset J ρ (fun j hj => hρ0 j hj)
  set γ := 1 - 2 * t - d with hγ
  have hγ0 : 0 < γ := by linarith
  have hsupp : ∀ z ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ j,
      (z : lp E ⊤) j = 0 → (F z : lp E ⊤) j = 0 := by
    intro z hz j hzj
    have := hnorm z hz j
    rw [hzj, norm_zero] at this
    exact norm_le_zero_iff.1 this
  obtain ⟨η, hη, hpre⟩ := exists_preimage_near S' F hbij.injOn hlip hsupp b (by linarith) hbO
    (lt_min hm' hγ0)
  set ε := min (η / 2) (t / 2) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  set gz : ∀ j, E j := Function.update (fun j => (0 : E j)) i ((t - ε) • e i) with hgz
  set z := upd (F b) {i} gz with hz
  have hzi : (z : lp E ⊤) i = (t - ε) • e i := by
    rw [hz, upd_apply, if_pos (Finset.mem_singleton_self i), hgz, Function.update_self]
  have hzj : ∀ j, j ≠ i → (z : lp E ⊤) j = (F b : lp E ⊤) j := by
    intro j hj
    rw [hz, upd_apply, if_neg (by simpa using hj)]
  have hzS : ∀ j ∉ S', (z : lp E ⊤) j = 0 := by
    intro j hj
    have hji : j ≠ i := fun h => hj (h ▸ hTS' i hiT)
    rw [hzj j hji]
    exact hsupp b hbB j (hbO j hj)
  have hzFb : ‖z - F b‖ < η := by
    have : ‖z - F b‖ ≤ ε := by
      refine norm_sub_le_of_forall hε0.le fun j => ?_
      by_cases hji : j = i
      · subst hji
        rw [hzi, hFbi, ← sub_smul, norm_smul, hei, mul_one]
        rw [show t - ε - t = -ε by ring, norm_neg, Real.norm_of_nonneg hε0.le]
      · rw [hzj j hji, sub_self, norm_zero]; exact hε0.le
    have : ε < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    linarith
  obtain ⟨y', hy'B, hy'b, hFy'⟩ := hpre z hzS hzFb
  -- the contradiction: `‖y' - q‖ ≤ 1 - t` but `‖F y' - F q‖ ≥ 1 - t + ε`
  have hup : ‖y' - q‖ ≤ 1 - t := by
    refine norm_sub_le_of_forall h1t fun j => ?_
    have hyb : ‖(y' : lp E ⊤) j - (b : lp E ⊤) j‖ < min m' γ :=
      (norm_sub_apply_le y' b j).trans_lt hy'b
    by_cases hjJ : j ∈ J
    · have hji : j ≠ i := fun h => hJT j hjJ (h ▸ hiT)
      have hFy'j : (F y' : lp E ⊤) j = (F b : lp E ⊤) j := by rw [hFy', hzj j hji]
      rw [norm_sub_rev]
      refine hρ j hjJ ((F y' : lp E ⊤) j) ((y' : lp E ⊤) j) ?_ ?_ ?_
        (fun ω hω => hcmp y' hy'B j ω hω)
      · rw [hFy'j, ← hbJ j hjJ]; exact hnorm b hbB j
      · rw [hFy'j]; exact hβ2 j hjJ
      · rw [← hbJ j hjJ]
        exact hyb.trans_le ((min_le_left _ _).trans (hm'J j hjJ))
    · have h1 := norm_sub_le_norm_sub_add_norm_sub ((y' : lp E ⊤) j) ((b : lp E ⊤) j)
        ((q : lp E ⊤) j)
      have h2 := hE4 j hjJ
      rw [norm_sub_rev] at h2
      have h3 : min m' γ ≤ γ := min_le_right _ _
      linarith
  have hlow : 1 - t + ε ≤ ‖F y' - F q‖ := by
    have := norm_sub_apply_le (F y') (F q) i
    rw [hFy', hzi, hFqj, if_pos hiT] at this
    have e1 : (t - ε) • e i - e i = (-(1 - t + ε)) • e i := by module
    rw [e1, norm_smul, hei, mul_one, norm_neg, Real.norm_of_nonneg (by linarith)] at this
    rw [hFy']
    exact this
  have := hlip' y' hy'B q hqB
  linarith
