-- Prove2me | solution 1 for Plasticity.CUB37.rigidity
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T09:16:04.814387+00:00
-- url     : https://prove2.me/submissions/9eccebd2-130a-4498-b21c-2a7db73080e1

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Group.Constructions
import Theorems.Thm_Plasticity_CUB37_no_collapse
import Theorems.Thm_Plasticity_Ext_FreudenthalHurewicz

/-!
Rigidity (Theorem 3 of `expositions/c0_between_spaces.md`, §4): a nonexpansive bijection `H`
between the balls of two spaces between `c₀₀(Γ)` and `c₀(Γ)` that satisfies the coordinate
bounds (N1), and whose preimages of finitely supported points are matched, is the identity.

For a finite `S ⊆ Γ` the cube `Q_S` (points of norm `≤ 1` supported in `S`) is compact, and
`H` maps it onto itself (by (N1) and no collapse at matched points), so it is an isometry of
`Q_S` (Freudenthal–Hurewicz). Then `H (±eₙ) = ±eₙ`, the identity `‖H x ∓ eₙ‖ = ‖x ∓ eₙ‖`
pins down each coordinate of a finitely supported `x`, and density finishes.
-/

open Plasticity Filter Topology

namespace Sol_Plasticity_CUB37_rigidity

variable {Γ : Type*}

lemma mem_ballIn {X : Submodule ℝ (Linf Γ)} {x : Linf Γ} :
    x ∈ ballIn X ↔ x ∈ X ∧ ‖x‖ ≤ 1 := by
  simp only [ballIn, Set.mem_inter_iff, SetLike.mem_coe, mem_closedBall_zero_iff]

lemma abs_coord_le (x : Linf Γ) (i : Γ) : |x i| ≤ ‖x‖ := by
  have := lp.norm_apply_le_norm (p := ⊤) ENNReal.top_ne_zero x i
  rwa [Real.norm_eq_abs] at this

lemma memℓp_top_of_bound (g : Γ → ℝ) (C : ℝ) (h : ∀ i, |g i| ≤ C) : Memℓp g ⊤ := by
  rw [memℓp_infty_iff]
  refine ⟨C, ?_⟩
  rintro _ ⟨i, rfl⟩
  simpa [Real.norm_eq_abs] using h i

/-- The cube `Q_S`: points of norm at most `1` supported in the finite set `S`. -/
def cube (S : Finset Γ) : Set (Linf Γ) := {x | ‖x‖ ≤ 1 ∧ ∀ i, i ∉ S → x i = 0}

lemma mem_cube {S : Finset Γ} {x : Linf Γ} :
    x ∈ cube S ↔ ‖x‖ ≤ 1 ∧ ∀ i, i ∉ S → x i = 0 := Iff.rfl

lemma support_finite_of_mem_cube {S : Finset Γ} {x : Linf Γ} (hx : x ∈ cube S) :
    (Function.support ⇑x).Finite :=
  S.finite_toSet.subset fun i hi => by
    by_contra h
    exact hi ((mem_cube.1 hx).2 i h)

lemma cube_subset_ballIn (X : Submodule ℝ (Linf Γ)) (hX0 : c00 Γ ≤ X) (S : Finset Γ) :
    cube S ⊆ ballIn X := fun _ hx =>
  mem_ballIn.2 ⟨hX0 (support_finite_of_mem_cube hx), (mem_cube.1 hx).1⟩

/-- Extension by zero from `S` to `Γ`. -/
noncomputable def ext0 (S : Finset Γ) (v : S → ℝ) : Linf Γ := by
  classical
  exact ⟨fun i => if h : i ∈ S then v ⟨i, h⟩ else 0, memℓp_top_of_bound _ ‖v‖ fun i => by
    by_cases h : i ∈ S
    · rw [dif_pos h, ← Real.norm_eq_abs]; exact norm_le_pi_norm v ⟨i, h⟩
    · rw [dif_neg h, abs_zero]; exact norm_nonneg v⟩

lemma ext0_apply_mem (S : Finset Γ) (v : S → ℝ) (i : Γ) (h : i ∈ S) :
    ext0 S v i = v ⟨i, h⟩ := by
  classical
  show (if h : i ∈ S then v ⟨i, h⟩ else 0) = v ⟨i, h⟩
  rw [dif_pos h]

lemma ext0_apply_not_mem (S : Finset Γ) (v : S → ℝ) (i : Γ) (h : i ∉ S) :
    ext0 S v i = 0 := by
  classical
  show (if h : i ∈ S then v ⟨i, h⟩ else 0) = 0
  rw [dif_neg h]

lemma ext0_lipschitz (S : Finset Γ) : LipschitzWith 1 (ext0 S) := by
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro i
  rw [lp.coeFn_sub, Pi.sub_apply]
  by_cases h : i ∈ S
  · rw [ext0_apply_mem S v i h, ext0_apply_mem S w i h]
    exact norm_le_pi_norm (v - w) ⟨i, h⟩
  · rw [ext0_apply_not_mem S v i h, ext0_apply_not_mem S w i h, sub_zero, norm_zero]
    exact norm_nonneg _

lemma cube_eq_image (S : Finset Γ) : cube S = ext0 S '' Metric.closedBall 0 1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx1, hx0⟩ := mem_cube.1 hx
    refine ⟨fun i => x i, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs]
      exact (abs_coord_le x i).trans hx1
    · ext i
      by_cases h : i ∈ S
      · rw [ext0_apply_mem S _ i h]
      · rw [ext0_apply_not_mem S _ i h, hx0 i h]
  · rintro ⟨v, hv, rfl⟩
    rw [mem_closedBall_zero_iff] at hv
    refine mem_cube.2 ⟨?_, fun i hi => ext0_apply_not_mem S v i hi⟩
    apply lp.norm_le_of_forall_le zero_le_one
    intro i
    by_cases h : i ∈ S
    · rw [ext0_apply_mem S v i h]
      exact (norm_le_pi_norm v ⟨i, h⟩).trans hv
    · rw [ext0_apply_not_mem S v i h, norm_zero]
      exact zero_le_one

lemma isCompact_cube (S : Finset Γ) : IsCompact (cube S) := by
  rw [cube_eq_image]
  exact (isCompact_closedBall 0 1).image (ext0_lipschitz S).continuous

lemma zero_mem_cube (S : Finset Γ) : (0 : Linf Γ) ∈ cube S :=
  mem_cube.2 ⟨by simp, fun i _ => by simp⟩

lemma single_mem_cube [DecidableEq Γ] (S : Finset Γ) (n : Γ) (hn : n ∈ S) (s : ℝ)
    (hs : |s| ≤ 1) : lp.single ⊤ n s ∈ cube S := by
  refine mem_cube.2 ⟨?_, fun i hi => ?_⟩
  · rw [lp.norm_single (by simp), Real.norm_eq_abs]
    exact hs
  · have : i ≠ n := fun h => hi (h ▸ hn)
    exact lp.single_apply_ne _ _ _ this

lemma mem_cube_insert [DecidableEq Γ] (x : Linf Γ) (hx : ‖x‖ ≤ 1)
    (hfin : (Function.support ⇑x).Finite) (n : Γ) : x ∈ cube (insert n hfin.toFinset) := by
  refine mem_cube.2 ⟨hx, fun i hi => ?_⟩
  by_contra h
  exact hi (Finset.mem_insert_of_mem (hfin.mem_toFinset.2 h))

lemma norm_sub_single_le [DecidableEq Γ] (u : Linf Γ) (hu : ‖u‖ ≤ 1) (n : Γ) (s : ℝ) :
    ‖u - lp.single ⊤ n s‖ ≤ max 1 |u n - s| := by
  apply lp.norm_le_of_forall_le (le_trans zero_le_one (le_max_left _ _))
  intro i
  rw [lp.coeFn_sub, Pi.sub_apply, lp.single_apply, Real.norm_eq_abs]
  by_cases h : i = n
  · subst h
    rw [Pi.single_eq_same]
    exact le_max_right _ _
  · rw [Pi.single_eq_of_ne h, sub_zero]
    exact ((abs_coord_le u i).trans hu).trans (le_max_left _ _)

lemma abs_le_norm_sub_single [DecidableEq Γ] (u : Linf Γ) (n : Γ) (s : ℝ) :
    |u n - s| ≤ ‖u - lp.single ⊤ n s‖ := by
  have := abs_coord_le (u - lp.single ⊤ n s) n
  rwa [lp.coeFn_sub, Pi.sub_apply, lp.single_apply, Pi.single_eq_same] at this

/-- Truncation: a point of `c₀(Γ)` is within `ε` of a finitely supported point of no larger
norm. -/
lemma exists_trunc (x : Linf Γ) (hx : x ∈ c0 Γ) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : Linf Γ, (Function.support ⇑y).Finite ∧ ‖y‖ ≤ ‖x‖ ∧ ‖x - y‖ ≤ ε := by
  classical
  have hx' : Tendsto (⇑x) cofinite (𝓝 0) := hx
  have hT : {i | ¬ dist (x i) 0 < ε}.Finite :=
    Filter.eventually_cofinite.1 (Metric.tendsto_nhds.1 hx' ε hε)
  let g : Γ → ℝ := fun i => if ε ≤ |x i| then x i else 0
  have hg : ∀ i, |g i| ≤ |x i| := by
    intro i
    simp only [g]
    split_ifs <;> simp
  have hgm : Memℓp g ⊤ := memℓp_top_of_bound g ‖x‖ fun i => (hg i).trans (abs_coord_le x i)
  refine ⟨⟨g, hgm⟩, ?_, ?_, ?_⟩
  · refine hT.subset fun i hi => ?_
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, not_lt]
    by_contra h
    exact hi (show g i = 0 by simp only [g]; rw [if_neg h])
  · refine lp.norm_le_of_forall_le (norm_nonneg x) fun i => ?_
    rw [Real.norm_eq_abs]
    exact (hg i).trans (abs_coord_le x i)
  · apply lp.norm_le_of_forall_le hε.le
    intro i
    rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs]
    show |x i - g i| ≤ ε
    simp only [g]
    split_ifs with h
    · simp [hε.le]
    · rw [sub_zero]
      exact (not_le.1 h).le

end Sol_Plasticity_CUB37_rigidity

open Sol_Plasticity_CUB37_rigidity in
theorem solution {Γ : Type*} (X X' : Submodule ℝ (Linf Γ))
    (hX0 : c00 Γ ≤ X) (hX1 : X ≤ c0 Γ) (hX'0 : c00 Γ ≤ X') (hX'1 : X' ≤ c0 Γ)
    (H : Linf Γ → Linf Γ)
    (hbij : Set.BijOn H (ballIn X) (ballIn X'))
    (hlip : LipschitzOnWith 1 H (ballIn X))
    (hN1 : ∀ x ∈ ballIn X, ∀ n, (0 ≤ x n → 0 ≤ H x n ∧ H x n ≤ x n) ∧
      (x n ≤ 0 → x n ≤ H x n ∧ H x n ≤ 0))
    (hmatched : ∀ x ∈ ballIn X, (Function.support (H x)).Finite →
      ∃ w ∈ X', ∀ i, x i ≠ 0 → 0 < w i * x i) :
    ∀ x ∈ ballIn X, H x = x := by
  classical
  -- (N1) keeps zero coordinates zero
  have hzero : ∀ x ∈ ballIn X, ∀ n, x n = 0 → H x n = 0 := by
    intro x hx n hn
    have h := (hN1 x hx n).1 hn.symm.le
    rw [hn] at h
    exact le_antisymm h.2 h.1
  have h0B : (0 : Linf Γ) ∈ ballIn X := mem_ballIn.2 ⟨X.zero_mem, by simp⟩
  have hH0 : H 0 = 0 := by
    ext n
    rw [lp.coeFn_zero, Pi.zero_apply]
    exact hzero 0 h0B n (by simp)
  -- H maps each cube onto itself
  have hmapsQ : ∀ S : Finset Γ, Set.MapsTo H (cube S) (cube S) := by
    intro S x hx
    have hxB := cube_subset_ballIn X hX0 S hx
    exact mem_cube.2 ⟨(mem_ballIn.1 (hbij.mapsTo hxB)).2,
      fun i hi => hzero x hxB i ((mem_cube.1 hx).2 i hi)⟩
  have hsurjQ : ∀ S : Finset Γ, Set.SurjOn H (cube S) (cube S) := by
    intro S y hy
    have hyB : y ∈ ballIn X' := cube_subset_ballIn X' hX'0 S hy
    obtain ⟨x, hxB, rfl⟩ := hbij.surjOn hyB
    have hmatch := hmatched x hxB (support_finite_of_mem_cube hy)
    refine ⟨x, mem_cube.2 ⟨(mem_ballIn.1 hxB).2, fun i hi => ?_⟩, rfl⟩
    by_contra hxi
    exact Plasticity.CUB37.no_collapse X X' hX0 hX1 hX'0 hX'1 H hbij hlip hN1 x hxB hmatch i hxi
      ((mem_cube.1 hy).2 i hi)
  -- Freudenthal–Hurewicz: H is an isometry of each cube
  have hiso : ∀ S : Finset Γ, ∀ x ∈ cube S, ∀ y ∈ cube S, dist (H x) (H y) = dist x y :=
    fun S => Plasticity.Ext.FreudenthalHurewicz (cube S) (isCompact_cube S) H (hmapsQ S)
      (hsurjQ S) (hlip.mono (cube_subset_ballIn X hX0 S))
  -- H (±eₙ) = ±eₙ
  have hunit : ∀ n : Γ, ∀ s : ℝ, (s = 1 ∨ s = -1) →
      H (lp.single ⊤ n s) = lp.single ⊤ n s := by
    intro n s hs
    have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> simp
    have he : lp.single ⊤ n s ∈ cube ({n} : Finset Γ) :=
      single_mem_cube {n} n (Finset.mem_singleton_self n) s hs1.le
    have hd := hiso {n} _ he 0 (zero_mem_cube {n})
    rw [hH0, dist_zero_right, dist_zero_right, lp.norm_single (by simp), Real.norm_eq_abs,
      hs1] at hd
    have heB := cube_subset_ballIn X hX0 _ he
    have hoff : ∀ i, i ≠ n → H (lp.single ⊤ n s) i = 0 := fun i hi =>
      hzero _ heB i (lp.single_apply_ne _ _ _ hi)
    have hle : ‖H (lp.single ⊤ n s)‖ ≤ |H (lp.single ⊤ n s) n| := by
      apply lp.norm_le_of_forall_le (abs_nonneg _)
      intro i
      by_cases hi : i = n
      · subst hi
        rw [Real.norm_eq_abs]
      · rw [hoff i hi, norm_zero]
        exact abs_nonneg _
    have hN := hN1 _ heB n
    rw [lp.single_apply_self] at hN
    have hval : H (lp.single ⊤ n s) n = s := by
      rcases hs with rfl | rfl
      · have h := hN.1 zero_le_one
        rw [abs_of_nonneg h.1] at hle
        linarith
      · have h := hN.2 (by norm_num)
        rw [abs_of_nonpos h.2] at hle
        linarith
    ext i
    by_cases hi : i = n
    · subst hi
      rw [hval, lp.single_apply_self]
    · rw [hoff i hi, lp.single_apply_ne _ _ _ hi]
  -- H fixes every finitely supported point
  have hfix : ∀ x ∈ ballIn X, (Function.support ⇑x).Finite → H x = x := by
    intro x hx hfin
    have hx1 : ‖x‖ ≤ 1 := (mem_ballIn.1 hx).2
    have hHx1 : ‖H x‖ ≤ 1 := (mem_ballIn.1 (hbij.mapsTo hx)).2
    ext n
    have hxS : x ∈ cube (insert n hfin.toFinset) := mem_cube_insert x hx1 hfin n
    have key : ∀ s : ℝ, (s = 1 ∨ s = -1) →
        ‖H x - lp.single ⊤ n s‖ = ‖x - lp.single ⊤ n s‖ := by
      intro s hs
      have hsS : lp.single ⊤ n s ∈ cube (insert n hfin.toFinset) :=
        single_mem_cube _ n (Finset.mem_insert_self _ _) s
          (by rcases hs with rfl | rfl <;> simp)
      have h := hiso _ x hxS _ hsS
      rwa [hunit n s hs, dist_eq_norm, dist_eq_norm] at h
    rcases le_total 0 (x n) with hpos | hneg
    · obtain ⟨h0, h1⟩ := (hN1 x hx n).1 hpos
      have a1 := abs_le_norm_sub_single x n (-1)
      have a2 := norm_sub_single_le (H x) hHx1 n (-1)
      rw [key (-1) (Or.inr rfl)] at a2
      rw [abs_of_nonneg (by linarith)] at a1
      rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)] at a2
      linarith
    · obtain ⟨h0, h1⟩ := (hN1 x hx n).2 hneg
      have a1 := abs_le_norm_sub_single x n 1
      have a2 := norm_sub_single_le (H x) hHx1 n 1
      rw [key 1 (Or.inl rfl)] at a2
      rw [abs_of_nonpos (by linarith)] at a1
      rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)] at a2
      linarith
  -- density of finitely supported points and continuity of H
  intro x hx
  obtain ⟨hxX, hx1⟩ := mem_ballIn.1 hx
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨y, hyfin, hyx, hxy⟩ := exists_trunc x (hX1 hxX) (ε / 2) (by positivity)
  have hy : y ∈ ballIn X := mem_ballIn.2 ⟨hX0 hyfin, hyx.trans hx1⟩
  have hHy := hfix y hy hyfin
  have hlipxy : dist (H x) (H y) ≤ dist x y := by
    simpa using hlip.dist_le_mul x hx y hy
  rw [hHy] at hlipxy
  calc dist (H x) x ≤ dist (H x) y + dist y x := dist_triangle _ _ _
    _ ≤ dist x y + dist y x := add_le_add hlipxy le_rfl
    _ ≤ ε / 2 + ε / 2 := by rw [dist_comm y x, dist_eq_norm]; linarith
    _ = ε := by ring
