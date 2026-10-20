-- Prove2me | solution 1 for Plasticity.C0Sum.exists_blockEquiv_three_feeders
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:04:00.257176+00:00
-- url     : https://prove2.me/submissions/96df822f-9c0a-4462-8291-6efe8822f992

import Definitions.Def_Plasticity_C0Sum
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_Plane_closedBall_subset_union_two_iff
import Theorems.Thm_Plasticity_Ext_InvarianceOfDomain

/-!
Three scalar source blocks cannot feed one planar target block along three rays lying in an open
half-plane (CUB109 Lemma 2.2): on an open octant of their cube the map would be a continuous
injection into the plane, against invariance of domain.

The c₀-sum helpers `norm_c0Sum_le`, `norm_apply_le`, `c0_ext`, `ofFun`, `sg` are copied from the
project's solution `Solutions/Sol_Plasticity_C0Sum_exists_extremeRule.lean`, and
`exists_norm_attained` from `Solutions/Sol_Plasticity_Plane_closedBall_subset_union_two_iff.lean`.
-/

open Plasticity

namespace Sol_Plasticity_C0Sum_exists_blockEquiv_three_feeders

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

end Block


/-- In finite dimensions every functional attains its norm on the closed unit ball. -/
theorem exists_norm_attained {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (ψ : StrongDual ℝ V) : ∃ z : V, ‖z‖ ≤ 1 ∧ ψ z = ‖ψ‖ := by
  have hK : IsCompact ((fun x => ‖ψ x‖) '' Metric.closedBall (0 : V) 1) :=
    (isCompact_closedBall (0 : V) 1).image (continuous_norm.comp ψ.continuous)
  have hne : ((fun x => ‖ψ x‖) '' Metric.closedBall (0 : V) 1).Nonempty :=
    ⟨_, 0, Metric.mem_closedBall_self zero_le_one, rfl⟩
  obtain ⟨z, hz, hzψ⟩ := hK.sSup_mem hne
  rw [ψ.sSup_unitClosedBall_eq_norm] at hzψ
  rw [mem_closedBall_zero_iff] at hz
  rcases (abs_eq (norm_nonneg ψ)).1 (by simpa [Real.norm_eq_abs] using hzψ) with h | h
  · exact ⟨z, hz, h⟩
  · exact ⟨-z, by simpa using hz, by simp [h]⟩

section Main

variable {ι κ : Type*}
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {E' : κ → Type*} [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]

lemma sg_sub (j : ι) (a b : E j) : sg j a - sg j b = (sg j (a - b) : c0Sum E) := by
  refine c0_ext fun m => ?_
  by_cases h : m = j
  · subst h; simp [sg_self]
  · simp [sg_ne _ h]

lemma continuous_sg (j : ι) : Continuous (sg j : E j → c0Sum E) := by
  refine (LipschitzWith.of_dist_le_mul fun a b => ?_).continuous (K := 1)
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, sg_sub]
  exact norm_sg_le _ _

lemma continuous_eval (m : ι) : Continuous fun x : c0Sum E => (x : lp E ⊤) m := by
  refine (LipschitzWith.of_dist_le_mul fun x y => ?_).continuous (K := 1)
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  have := norm_apply_le (x - y) m
  simpa using this

/-- A functional positive at `w` keeps its antinorming point farther than one from `w`. -/
lemma one_lt_norm_sub_of_pos {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (ψ : StrongDual ℝ W) {z₀ w : W} (hz₀ : ψ z₀ = -‖ψ‖) (hw : 0 < ψ w) : 1 < ‖z₀ - w‖ := by
  have hψ : 0 < ‖ψ‖ := by
    by_contra h
    have h0 : ‖ψ‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
    have := ψ.le_opNorm w
    rw [h0, zero_mul, Real.norm_eq_abs] at this
    linarith [abs_nonneg (ψ w), le_abs_self (ψ w)]
  have h1 := ψ.le_opNorm (w - z₀)
  rw [map_sub, hz₀, Real.norm_eq_abs, abs_of_pos (by linarith), norm_sub_rev] at h1
  by_contra h
  push Not at h
  nlinarith

end Main

end Sol_Plasticity_C0Sum_exists_blockEquiv_three_feeders

open Sol_Plasticity_C0Sum_exists_blockEquiv_three_feeders in
theorem solution {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (F : c0Sum E → c0Sum E')
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (h : Fin 3 → ι) (hinj : Function.Injective h) (hdim : ∀ k, Module.finrank ℝ (E (h k)) = 1)
    (e : ∀ k, E (h k)) (he : ∀ k, ‖e k‖ = 1)
    (m : κ) (hm : Module.finrank ℝ (E' m) = 2) (ψ : StrongDual ℝ (E' m))
    (hpos : ∀ k, ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, (∀ l ≠ h k, (x : lp E ⊤) l = 0) →
      (x : lp E ⊤) (h k) = (1 / 2 : ℝ) • e k →
        (∀ l ≠ m, (F x : lp E' ⊤) l = 0) ∧ 0 < ψ ((F x : lp E' ⊤) m)) : False := by
  classical
  have : FiniteDimensional ℝ (E' m) := Module.finite_of_finrank_eq_succ hm
  have h01 : h 0 ≠ h 1 := fun h' => by simpa using hinj h'
  have h02 : h 0 ≠ h 2 := fun h' => by simpa using hinj h'
  have h12 : h 1 ≠ h 2 := fun h' => by simpa using hinj h'
  -- the points of the cube
  set X : (Fin 3 → ℝ) → c0Sum E := fun s =>
    sg (h 0) (s 0 • e 0) + sg (h 1) (s 1 • e 1) + sg (h 2) (s 2 • e 2) with hX
  have hXk : ∀ s k, (X s : lp E ⊤) (h k) = s k • e k := by
    intro s k
    fin_cases k <;> simp [hX, sg_self, sg_ne _ h01, sg_ne _ h02, sg_ne _ h12, sg_ne _ h01.symm,
      sg_ne _ h02.symm, sg_ne _ h12.symm]
  have hXl : ∀ s l, (∀ k, l ≠ h k) → (X s : lp E ⊤) l = 0 := by
    intro s l hl
    simp [hX, sg_ne _ (hl 0), sg_ne _ (hl 1), sg_ne _ (hl 2)]
  have hXc : Continuous X := by
    simp only [hX]
    refine ((continuous_sg _).comp ?_).add ((continuous_sg _).comp ?_) |>.add
      ((continuous_sg _).comp ?_) <;> exact (continuous_apply _).smul continuous_const
  set O : Set (Fin 3 → ℝ) := Set.pi Set.univ fun _ => Set.Ioo (-1 : ℝ) 0 with hO
  have hOo : IsOpen O := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  have hblock : ∀ (x : c0Sum E) (l : ι), (∀ k, l ≠ h k) → ‖(x : lp E ⊤) l‖ ≤ ‖x‖ :=
    fun x l _ => norm_apply_le x l
  have hXmem : ∀ s ∈ O, X s ∈ Metric.closedBall (0 : c0Sum E) 1 := by
    intro s hs
    rw [mem_closedBall_zero_iff]
    refine norm_c0Sum_le zero_le_one fun l => ?_
    by_cases hl : ∃ k, l = h k
    · obtain ⟨k, rfl⟩ := hl
      rw [hXk, norm_smul, he, mul_one, Real.norm_eq_abs, abs_le]
      have hsk : -1 < s k ∧ s k < 0 := hs k (Set.mem_univ _)
      exact ⟨by linarith [hsk.1], by linarith [hsk.2]⟩
    · push Not at hl
      rw [hXl s l hl, norm_zero]; exact zero_le_one
  -- the auxiliary centres and their images
  set aux : Fin 3 → c0Sum E := fun k => sg (h k) ((1 / 2 : ℝ) • e k)
  have hauxmem : ∀ k, aux k ∈ Metric.closedBall (0 : c0Sum E) 1 := fun k =>
    mem_closedBall_zero_iff.2 ((norm_sg_le _ _).trans (by
      rw [norm_smul, he]; norm_num))
  have hauxF : ∀ k, (∀ l ≠ m, (F (aux k) : lp E' ⊤) l = 0) ∧ 0 < ψ ((F (aux k) : lp E' ⊤) m) :=
    fun k => hpos k (aux k) (hauxmem k) (fun l hl => sg_ne _ hl) (sg_self _ _)
  -- the cover of the ball of the source
  have hcover : ∀ s ∈ O, ∀ z ∈ Metric.closedBall (0 : c0Sum E) 1,
      ‖z - X s‖ ≤ 1 ∨ ∃ k, ‖z - aux k‖ ≤ 1 := by
    intro s hs z hz
    have hzn := mem_closedBall_zero_iff.1 hz
    have hcoef : ∀ k, ∃ c : ℝ, (z : lp E ⊤) (h k) = c • e k ∧ |c| ≤ 1 := by
      intro k
      have hek : e k ≠ 0 := norm_ne_zero_iff.1 (by rw [he]; norm_num)
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (e k) hek).1 (hdim k) ((z : lp E ⊤) (h k))
      refine ⟨c, hc.symm, ?_⟩
      have := (norm_apply_le z (h k)).trans hzn
      rwa [← hc, norm_smul, he, mul_one, Real.norm_eq_abs] at this
    choose c hc using hcoef
    by_cases hbig : ∃ k, s k + 1 < c k
    · obtain ⟨k, hk⟩ := hbig
      right
      refine ⟨k, norm_c0Sum_le zero_le_one fun l => ?_⟩
      by_cases hl : l = h k
      · subst hl
        simp only [aux, Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, sg_self, (hc k).1]
        rw [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs, abs_le]
        have hsk : -1 < s k ∧ s k < 0 := hs k (Set.mem_univ _)
        have hck := (abs_le.1 (hc k).2)
        constructor <;> linarith [hck.1, hck.2, hsk.1, hsk.2]
      · simp only [aux, Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, sg_ne _ hl, sub_zero]
        exact (norm_apply_le z l).trans hzn
    · push Not at hbig
      left
      refine norm_c0Sum_le zero_le_one fun l => ?_
      by_cases hl : ∃ k, l = h k
      · obtain ⟨k, rfl⟩ := hl
        simp only [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, hXk, (hc k).1]
        rw [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs, abs_le]
        have hsk : -1 < s k ∧ s k < 0 := hs k (Set.mem_univ _)
        have hck := (abs_le.1 (hc k).2)
        constructor <;> linarith [hbig k, hck.1, hck.2, hsk.1, hsk.2]
      · push Not at hl
        simp only [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, hXl s l hl, sub_zero]
        exact (norm_apply_le z l).trans hzn
  -- the image of every point of the octant lies in block `m`
  obtain ⟨z₁, hz₁, hψz₁⟩ := exists_norm_attained ψ
  set z₀ := -z₁
  have hz₀ : ‖z₀‖ ≤ 1 := by rw [norm_neg]; exact hz₁
  have hψz₀ : ψ z₀ = -‖ψ‖ := by rw [map_neg, hψz₁]
  have hsupp : ∀ s ∈ O, ∀ l ≠ m, (F (X s) : lp E' ⊤) l = 0 := by
    intro s hs l hl
    by_contra hne
    set y : c0Sum E' := ofFun {m, l}
      (Function.update (Function.update 0 m z₀) l (antipode ((F (X s) : lp E' ⊤) l)))
    have hy : ‖y‖ ≤ 1 := by
      refine norm_ofFun_le _ _ fun n => ?_
      by_cases hn : n = l
      · subst hn; simp [norm_antipode_le]
      rw [Function.update_of_ne hn]
      by_cases hn' : n = m
      · subst hn'; simpa using hz₀
      simp [Function.update_of_ne hn']
    obtain ⟨x, hx, hxy⟩ := hbij.surjOn (mem_closedBall_zero_iff.2 hy)
    rcases hcover s hs x hx with h1 | ⟨k, h1⟩
    · have := hlip.norm_sub_le hx (hXmem s hs)
      rw [NNReal.coe_one, one_mul, hxy] at this
      have h2 := (norm_apply_le (y - F (X s)) l).trans (this.trans h1)
      simp only [y, Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, ofFun_apply] at h2
      rw [if_pos (by simp), Function.update_self] at h2
      linarith [one_lt_norm_antipode_sub_self hne]
    · have := hlip.norm_sub_le hx (hauxmem k)
      rw [NNReal.coe_one, one_mul, hxy] at this
      have h2 := (norm_apply_le (y - F (aux k)) m).trans (this.trans h1)
      simp only [y, Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, ofFun_apply] at h2
      rw [if_pos (by simp), Function.update_of_ne hl.symm, Function.update_self] at h2
      linarith [one_lt_norm_sub_of_pos ψ hψz₀ (hauxF k).2]
  -- a continuous injection of the octant into a plane
  set B := Module.finBasisOfFinrankEq ℝ (E' m) hm
  have hBc : Continuous (B.equivFun : E' m → Fin 2 → ℝ) :=
    LinearMap.continuous_of_finiteDimensional (B.equivFun : E' m →ₗ[ℝ] (Fin 2 → ℝ))
  set L : E' m → Fin 3 → ℝ := fun w => ![B.equivFun w 0, B.equivFun w 1, 0]
  have hLc : Continuous L := by
    refine continuous_pi fun k => ?_
    fin_cases k
    · show Continuous fun w => B.equivFun w 0
      exact (continuous_apply 0).comp hBc
    · show Continuous fun w => B.equivFun w 1
      exact (continuous_apply 1).comp hBc
    · show Continuous fun _ => (0 : ℝ)
      exact continuous_const
  set G : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun s => L ((F (X s) : lp E' ⊤) m)
  have hGc : ContinuousOn G O :=
    hLc.comp_continuousOn ((continuous_eval m).comp_continuousOn
      (hlip.continuousOn.comp hXc.continuousOn hXmem))
  have hGi : Set.InjOn G O := by
    intro s hs s' hs' hss
    have h0 := congrFun hss 0
    have h1 := congrFun hss 1
    simp only [G, L, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have hw : B.equivFun ((F (X s) : lp E' ⊤) m) = B.equivFun ((F (X s') : lp E' ⊤) m) := by
      funext k; fin_cases k
      · exact h0
      · exact h1
    have hFm := B.equivFun.injective hw
    have hF : F (X s) = F (X s') := by
      refine c0_ext fun l => ?_
      by_cases hl : l = m
      · subst hl; exact hFm
      · rw [hsupp s hs l hl, hsupp s' hs' l hl]
    have hXX := hbij.injOn (hXmem s hs) (hXmem s' hs') hF
    funext k
    have := congrArg (fun x : c0Sum E => (x : lp E ⊤) (h k)) hXX
    simp only [hXk] at this
    have hek : e k ≠ 0 := norm_ne_zero_iff.1 (by rw [he]; norm_num)
    exact smul_left_injective ℝ hek this
  have hopen := Plasticity.Ext.InvarianceOfDomain O hOo G hGc hGi
  set s₀ : Fin 3 → ℝ := fun _ => -1 / 2
  have hs₀ : s₀ ∈ O := fun k _ => by norm_num [s₀]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen (G s₀) ⟨s₀, hs₀, rfl⟩
  have hmem : Function.update (G s₀) 2 (ε / 2) ∈ G '' O := by
    refine hball ?_
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro k
    by_cases hk : k = 2
    · subst hk
      simp only [Function.update_self, G, L, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Real.dist_eq, sub_zero]
      rw [abs_of_pos (by linarith)]; linarith
    · rw [Function.update_of_ne hk, dist_self]; exact hε
  obtain ⟨s₁, -, hs₁⟩ := hmem
  have := congrFun hs₁ 2
  simp only [Function.update_self, G, L, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at this
  linarith
