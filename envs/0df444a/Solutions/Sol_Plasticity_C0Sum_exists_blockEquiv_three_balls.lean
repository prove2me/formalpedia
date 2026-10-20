-- Prove2me | solution 1 for Plasticity.C0Sum.exists_blockEquiv_three_balls
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:59.529959+00:00
-- url     : https://prove2.me/submissions/22383393-0694-40ae-8c77-1ade880a3064

import Definitions.Def_Plasticity_C0Sum
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Theorems.Thm_Plasticity_Plane_closedBall_subset_union_two_iff

/-!
Three unit balls covering the ball of a c₀ sum of lines and planes, one of whose centres has two
nonzero blocks (a generic form of CUB93 Lemma 2.2).

The c₀-sum helpers `norm_c0Sum_le`, `norm_apply_le`, `c0_ext`, `ofFun`, `sg` are copied from the
project's solution `Solutions/Sol_Plasticity_C0Sum_exists_extremeRule.lean`.
-/

open Plasticity

namespace Sol_Plasticity_C0Sum_exists_blockEquiv_three_balls

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

lemma opp_symm {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {p p' : W}
    (h : Opp p p') : Opp p' p := by
  obtain ⟨μ, hμ, h⟩ := h
  refine ⟨μ⁻¹, inv_pos.2 hμ, ?_⟩
  rw [h, smul_neg, neg_neg, smul_smul, inv_mul_cancel₀ hμ.ne', one_smul]

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

section Core

variable {κ : Type*} {E' : κ → Type*} [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
  (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)

include hE' in
/-- Case 1: `A` has a nonzero block outside `{m, m'}`. -/
lemma outside {q₀ A B : c0Sum E'} (hcov : Cov3 q₀ A B) (hB : B ≠ 0) {m m' : κ}
    (hmm' : m ≠ m') (hm : (q₀ : lp E' ⊤) m ≠ 0) (hm' : (q₀ : lp E' ⊤) m' ≠ 0)
    (hI : ∀ n, (∀ k ≠ n, (A : lp E' ⊤) k = 0 ∧ (B : lp E' ⊤) k = 0) →
      ¬ Opp ((A : lp E' ⊤) n) ((B : lp E' ⊤) n))
    {n₁ : κ} (hn₁ : (A : lp E' ⊤) n₁ ≠ 0) (h1m : n₁ ≠ m) (h1m' : n₁ ≠ m') : False := by
  by_cases hB' : ∃ n₂, (B : lp E' ⊤) n₂ ≠ 0 ∧ n₂ ≠ n₁
  · obtain ⟨n₂, hn₂, h21⟩ := hB'
    by_cases h2m : n₂ = m
    · subst h2m
      exact single3 hcov hm' hn₁ hn₂ (Ne.symm h1m') hmm'.symm (Ne.symm h21)
    · exact single3 hcov hm hn₁ hn₂ (Ne.symm h1m) (Ne.symm h2m) (Ne.symm h21)
  push Not at hB'
  obtain ⟨n, hn⟩ := exists_ne_zero_of_ne_zero hB
  have hBn₁ : (B : lp E' ⊤) n₁ ≠ 0 := by rwa [← hB' n hn]
  by_cases hA' : ∃ n₁', (A : lp E' ⊤) n₁' ≠ 0 ∧ n₁' ≠ n₁
  · obtain ⟨n₁', hn₁', h11⟩ := hA'
    by_cases h1'm : n₁' = m
    · subst h1'm
      exact single3 hcov hm' hn₁' hBn₁ hmm'.symm h1m'.symm h11
    · exact single3 hcov hm hn₁' hBn₁ (Ne.symm h1'm) (Ne.symm h1m) h11
  push Not at hA'
  have hsupp : ∀ k ≠ n₁, (A : lp E' ⊤) k = 0 ∧ (B : lp E' ⊤) k = 0 := by
    intro k hk
    constructor
    · by_contra h; exact hk (hA' k h)
    · by_contra h; exact hk (hB' k h)
  have hcov' : Cov3 A B q₀ := by
    intro y hy; rcases hcov y hy with h | h | h <;> tauto
  exact pair3 hE' hcov' h1m hn₁ hBn₁ (hI n₁ hsupp) hm

include hE' in
/-- Case 3a: `q₁` has block `m`, `q₂` has block `m'`, both supported in `{m, m'}`. -/
lemma case3a {q₀ q₁ q₂ : c0Sum E'} (hcov : Cov3 q₀ q₁ q₂) {m m' : κ}
    (hmm' : m ≠ m') (hm : (q₀ : lp E' ⊤) m ≠ 0)
    (hs₁ : ∀ k, k ≠ m → k ≠ m' → (q₁ : lp E' ⊤) k = 0)
    (hs₂ : ∀ k, k ≠ m → k ≠ m' → (q₂ : lp E' ⊤) k = 0)
    (hII : ∀ q, (q = q₁ ∨ q = q₂) → ∀ n, (n = m ∨ n = m') → (∀ k ≠ n, (q : lp E' ⊤) k = 0) →
      ∀ t : ℝ, (q : lp E' ⊤) n ≠ t • (q₀ : lp E' ⊤) n)
    (hm' : (q₀ : lp E' ⊤) m' ≠ 0)
    (h1 : (q₁ : lp E' ⊤) m ≠ 0) (h2 : (q₂ : lp E' ⊤) m' ≠ 0) : False := by
  by_cases o1 : Opp ((q₀ : lp E' ⊤) m) ((q₁ : lp E' ⊤) m)
  swap
  · exact pair3 hE' hcov hmm' hm h1 o1 h2
  by_cases o2 : Opp ((q₀ : lp E' ⊤) m') ((q₂ : lp E' ⊤) m')
  swap
  · exact pair3 hE' (cov3_swap23 hcov) hmm'.symm hm' h2 o2 h1
  obtain ⟨α, hα, e1⟩ := o1
  obtain ⟨β, hβ, e2⟩ := o2
  by_cases h1' : (q₁ : lp E' ⊤) m' = 0
  · refine hII q₁ (Or.inl rfl) m (Or.inl rfl) (fun k hk => ?_) (-α) (by rw [e1, neg_smul])
    by_cases hk' : k = m'
    · subst hk'; exact h1'
    · exact hs₁ k hk hk'
  by_cases h2' : (q₂ : lp E' ⊤) m = 0
  · refine hII q₂ (Or.inr rfl) m' (Or.inr rfl) (fun k hk => ?_) (-β) (by rw [e2, neg_smul])
    by_cases hk' : k = m
    · subst hk'; exact h2'
    · exact hs₂ k hk' hk
  by_cases o3 : Opp ((q₁ : lp E' ⊤) m) ((q₂ : lp E' ⊤) m)
  swap
  · exact pair3 hE' (by intro y hy; rcases hcov y hy with h | h | h <;> tauto) hmm' h1 h2' o3 hm'
  by_cases o4 : Opp ((q₀ : lp E' ⊤) m) ((q₂ : lp E' ⊤) m)
  swap
  · exact pair3 hE' (cov3_swap23 hcov) hmm' hm h2' o4 h1'
  obtain ⟨γ, hγ, e3⟩ := o3
  obtain ⟨δ, hδ, e4⟩ := o4
  have : (γ * α + δ) • (q₀ : lp E' ⊤) m = 0 := by
    rw [e1] at e3
    have h' : -(γ • -(α • (q₀ : lp E' ⊤) m)) + δ • (q₀ : lp E' ⊤) m = 0 := by
      rw [← e3, e4]; abel
    rw [← h']; module
  rcases smul_eq_zero.1 this with h | h
  · nlinarith [mul_pos hγ hα]
  · exact hm h

/-- Case 3c helper: if `q₁` has block `m` and neither 3a nor 3b holds, both lie in block `m`. -/
lemma case3c_aux {q₁ q₂ : c0Sum E'} {m m' : κ} (hq₂ : q₂ ≠ 0)
    (hs₁ : ∀ k, k ≠ m → k ≠ m' → (q₁ : lp E' ⊤) k = 0)
    (hs₂ : ∀ k, k ≠ m → k ≠ m' → (q₂ : lp E' ⊤) k = 0)
    (n3a : ¬ ((q₁ : lp E' ⊤) m ≠ 0 ∧ (q₂ : lp E' ⊤) m' ≠ 0))
    (n3b : ¬ ((q₁ : lp E' ⊤) m' ≠ 0 ∧ (q₂ : lp E' ⊤) m ≠ 0))
    (h1 : (q₁ : lp E' ⊤) m ≠ 0) :
    (q₂ : lp E' ⊤) m ≠ 0 ∧ ∀ k ≠ m, (q₁ : lp E' ⊤) k = 0 ∧ (q₂ : lp E' ⊤) k = 0 := by
  have h2' : (q₂ : lp E' ⊤) m' = 0 := by
    by_contra h; exact n3a ⟨h1, h⟩
  obtain ⟨n, hn⟩ := exists_ne_zero_of_ne_zero hq₂
  have hnm : n = m := by
    by_contra h
    by_cases h' : n = m'
    · subst h'; exact hn h2'
    · exact hn (hs₂ n h h')
  subst hnm
  have h1' : (q₁ : lp E' ⊤) m' = 0 := by
    by_contra h; exact n3b ⟨h, hn⟩
  refine ⟨hn, fun k hk => ⟨?_, ?_⟩⟩
  · by_cases hk' : k = m'
    · subst hk'; exact h1'
    · exact hs₁ k hk hk'
  · by_cases hk' : k = m'
    · subst hk'; exact h2'
    · exact hs₂ k hk hk'

end Core

end Sol_Plasticity_C0Sum_exists_blockEquiv_three_balls

open Sol_Plasticity_C0Sum_exists_blockEquiv_three_balls in
theorem solution {κ : Type*}
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
    (q₀ q₁ q₂ : c0Sum E') (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (hcov : Metric.closedBall (0 : c0Sum E') 1 ⊆
      Metric.closedBall q₀ 1 ∪ Metric.closedBall q₁ 1 ∪ Metric.closedBall q₂ 1)
    (m m' : κ) (hmm' : m ≠ m') (hm : (q₀ : lp E' ⊤) m ≠ 0) (hm' : (q₀ : lp E' ⊤) m' ≠ 0) :
    (∃ n : κ, (∀ k ≠ n, (q₁ : lp E' ⊤) k = 0 ∧ (q₂ : lp E' ⊤) k = 0) ∧
        ∃ μ : ℝ, 0 < μ ∧ (q₂ : lp E' ⊤) n = -(μ • (q₁ : lp E' ⊤) n)) ∨
      ∃ q ∈ ({q₁, q₂} : Set (c0Sum E')), ∃ n ∈ ({m, m'} : Set κ),
        (∀ k ≠ n, (q : lp E' ⊤) k = 0) ∧ ∃ t : ℝ, (q : lp E' ⊤) n = t • (q₀ : lp E' ⊤) n := by
  classical
  have hcov3 : Cov3 q₀ q₁ q₂ := by
    intro y hy
    have := hcov (mem_closedBall_zero_iff.2 hy)
    simp only [Set.mem_union, Metric.mem_closedBall, dist_eq_norm] at this
    tauto
  by_contra hcon
  push Not at hcon
  obtain ⟨hI0, hII0⟩ := hcon
  have hI : ∀ n, (∀ k ≠ n, (q₁ : lp E' ⊤) k = 0 ∧ (q₂ : lp E' ⊤) k = 0) →
      ¬ Opp ((q₁ : lp E' ⊤) n) ((q₂ : lp E' ⊤) n) := by
    rintro n hn ⟨μ, hμ, h⟩
    exact hI0 n hn μ hμ h
  have hII : ∀ q, (q = q₁ ∨ q = q₂) → ∀ n, (n = m ∨ n = m') →
      (∀ k ≠ n, (q : lp E' ⊤) k = 0) → ∀ t : ℝ, (q : lp E' ⊤) n ≠ t • (q₀ : lp E' ⊤) n := by
    intro q hq n hn hs t
    refine hII0 q ?_ n ?_ hs t
    · rcases hq with rfl | rfl <;> simp
    · rcases hn with rfl | rfl <;> simp
  by_cases o₁ : ∃ n₁, (q₁ : lp E' ⊤) n₁ ≠ 0 ∧ n₁ ≠ m ∧ n₁ ≠ m'
  · obtain ⟨n₁, h1, h1m, h1m'⟩ := o₁
    exact outside hE' hcov3 hq₂ hmm' hm hm' hI h1 h1m h1m'
  by_cases o₂ : ∃ n₂, (q₂ : lp E' ⊤) n₂ ≠ 0 ∧ n₂ ≠ m ∧ n₂ ≠ m'
  · obtain ⟨n₂, h2, h2m, h2m'⟩ := o₂
    refine outside hE' (cov3_swap23 hcov3) hq₁ hmm' hm hm' (fun n hn ho => ?_) h2 h2m h2m'
    exact hI n (fun k hk => (hn k hk).symm) (opp_symm ho)
  have hs₁ : ∀ k, k ≠ m → k ≠ m' → (q₁ : lp E' ⊤) k = 0 := by
    intro k hk hk'; by_contra h; exact o₁ ⟨k, h, hk, hk'⟩
  have hs₂ : ∀ k, k ≠ m → k ≠ m' → (q₂ : lp E' ⊤) k = 0 := by
    intro k hk hk'; by_contra h; exact o₂ ⟨k, h, hk, hk'⟩
  by_cases n3a : (q₁ : lp E' ⊤) m ≠ 0 ∧ (q₂ : lp E' ⊤) m' ≠ 0
  · exact case3a hE' hcov3 hmm' hm hs₁ hs₂ hII hm' n3a.1 n3a.2
  by_cases n3b : (q₁ : lp E' ⊤) m' ≠ 0 ∧ (q₂ : lp E' ⊤) m ≠ 0
  · refine case3a hE' hcov3 hmm'.symm hm' (fun k hk hk' => hs₁ k hk' hk)
      (fun k hk hk' => hs₂ k hk' hk) (fun q hq n hn => hII q hq n hn.symm) hm n3b.1 n3b.2
  obtain ⟨n, hn⟩ := exists_ne_zero_of_ne_zero hq₁
  have hnmm : n = m ∨ n = m' := by
    by_contra h; push Not at h; exact hn (hs₁ n h.1 h.2)
  rcases hnmm with rfl | rfl
  · obtain ⟨h2, hs⟩ := case3c_aux hq₂ hs₁ hs₂ n3a n3b hn
    exact pair3 hE' (by intro y hy; rcases hcov3 y hy with h | h | h <;> tauto) hmm' hn h2
      (hI n hs) hm'
  · obtain ⟨h2, hs⟩ := case3c_aux (m := n) (m' := m) hq₂ (fun k hk hk' => hs₁ k hk' hk)
      (fun k hk hk' => hs₂ k hk' hk) n3b n3a hn
    exact pair3 hE' (by intro y hy; rcases hcov3 y hy with h | h | h <;> tauto) hmm'.symm hn h2
      (hI n hs) hm
