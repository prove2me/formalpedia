-- Prove2me | solution 1 for Plasticity.CUB37.no_collapse
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T09:17:23.487823+00:00
-- url     : https://prove2.me/submissions/cffd9cbd-2868-4c26-a841-024ac0ca580e

import Theorems.Thm_Plasticity_Ext_InvarianceOfDomain
import Definitions.Def_Plasticity_SeqSpace
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Data.Finset.Max

/-!
# No collapse at matched points (Proposition 2 of `expositions/c0_between_spaces.md`)

`H` is a nonexpansive bijection of the ball of `X` onto the ball of `X'` (both between
`c₀₀(Γ)` and `c₀(Γ)`) that is inward: `H x n` lies between `0` and `x n`.  If `x` is matched
by `w ∈ X'` and `x n ≠ 0`, then `H x n ≠ 0`.

The proof follows the exposition (three points `x`, `q = K z`, `r = K z'`, base point `b`
on a finite set `T`, invariance of domain on `ℝ^T`), with the signs carried explicitly
instead of conjugating by reflections.
-/

namespace Sol_Plasticity_CUB37_no_collapse

open Plasticity Filter Topology

variable {Γ : Type*}

/-! ## Basic facts on `Linf Γ` -/

lemma abs_apply_le_norm (u : Linf Γ) (i : Γ) : |u i| ≤ ‖u‖ := by
  have := lp.norm_apply_le_norm (p := ⊤) ENNReal.top_ne_zero u i
  simpa [Real.norm_eq_abs] using this

lemma norm_le_of_abs_le {u : Linf Γ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, |u i| ≤ C) : ‖u‖ ≤ C :=
  lp.norm_le_of_forall_le hC (fun i => by simpa [Real.norm_eq_abs] using h i)

lemma sub_apply (u v : Linf Γ) (i : Γ) : (u - v) i = u i - v i := by
  rw [lp.coeFn_sub]; rfl

/-- In `c₀`, only finitely many coordinates have modulus at least `ε > 0`. -/
lemma finite_ge {u : Linf Γ} (hu : u ∈ c0 Γ) {ε : ℝ} (hε : 0 < ε) :
    {i | ε ≤ |u i|}.Finite := by
  have hu' : Tendsto (⇑u) cofinite (𝓝 0) := hu
  have h := (Metric.tendsto_nhds.1 hu') ε hε
  rw [Filter.eventually_cofinite] at h
  refine h.subset ?_
  intro i hi
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, not_lt] at hi ⊢
  exact hi

/-- Attained suprema in `c₀`: if `|u i| < a` on a set of coordinates, then the supremum over
that set is still below `a`. -/
lemma exists_bound_lt {u : Linf Γ} (hu : u ∈ c0 Γ) {a : ℝ} (ha : 0 < a) (P : Γ → Prop)
    (h : ∀ i, P i → |u i| < a) : ∃ θ, 0 ≤ θ ∧ θ < a ∧ ∀ i, P i → |u i| ≤ θ := by
  classical
  have hS : ({i | a / 2 ≤ |u i|} ∩ {i | P i}).Finite :=
    (finite_ge hu (half_pos ha)).subset Set.inter_subset_left
  rcases hS.toFinset.eq_empty_or_nonempty with he | hne
  · refine ⟨a / 2, by linarith, by linarith, fun i hi => ?_⟩
    by_contra hlt
    push Not at hlt
    have hmem : i ∈ hS.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact ⟨hlt.le, hi⟩
    rw [he] at hmem
    exact Finset.notMem_empty i hmem
  · obtain ⟨i₀, hi₀, hmax⟩ := hS.toFinset.exists_max_image (fun i => |u i|) hne
    rw [Set.Finite.mem_toFinset] at hi₀
    refine ⟨max (a / 2) |u i₀|, le_max_of_le_left (by linarith),
      max_lt (by linarith) (h i₀ hi₀.2), fun i hi => ?_⟩
    by_cases hbig : a / 2 ≤ |u i|
    · exact le_max_of_le_right (hmax i (by rw [Set.Finite.mem_toFinset]; exact ⟨hbig, hi⟩))
    · exact le_max_of_le_left (not_le.1 hbig).le

/-- A bounded function as an element of `Linf Γ`. -/
def mkLinf (f : Γ → ℝ) (C : ℝ) (hf : ∀ i, |f i| ≤ C) : Linf Γ :=
  ⟨f, memℓp_infty ⟨C, by rintro _ ⟨i, rfl⟩; simpa [Real.norm_eq_abs] using hf i⟩⟩

@[simp] lemma mkLinf_apply (f : Γ → ℝ) (C : ℝ) (hf : ∀ i, |f i| ≤ C) (i : Γ) :
    mkLinf f C hf i = f i := rfl

lemma mem_ballIn {X : Submodule ℝ (Linf Γ)} {u : Linf Γ} :
    u ∈ ballIn X ↔ u ∈ X ∧ ‖u‖ ≤ 1 := by
  simp only [ballIn, Set.mem_inter_iff, SetLike.mem_coe, Metric.mem_closedBall, dist_zero_right]

/-- A point that differs from a point of `X` at finitely many coordinates lies in `X`. -/
lemma mem_of_eq_off {X : Submodule ℝ (Linf Γ)} (hX0 : c00 Γ ≤ X) {u v : Linf Γ} (hu : u ∈ X)
    (S : Set Γ) (hS : S.Finite) (h : ∀ i, i ∉ S → v i = u i) : v ∈ X := by
  have hd : v - u ∈ c00 Γ := by
    show (Function.support ⇑(v - u)).Finite
    refine hS.subset ?_
    intro i hi
    by_contra hiS
    exact hi (by rw [sub_apply, h i hiS, sub_self])
  have h2 := X.add_mem hu (hX0 hd)
  have h3 : u + (v - u) = v := by abel
  rwa [h3] at h2

/-! ## Consequences of nonexpansiveness and of (N1) -/

section Inward

variable {X : Submodule ℝ (Linf Γ)} {H : Linf Γ → Linf Γ}

lemma lip_coord (hlip : LipschitzOnWith 1 H (ballIn X)) {u v : Linf Γ} (hu : u ∈ ballIn X)
    (hv : v ∈ ballIn X) (i : Γ) : |H u i - H v i| ≤ ‖u - v‖ := by
  have h1 := hlip.dist_le_mul u hu v hv
  simp only [NNReal.coe_one, one_mul, dist_eq_norm] at h1
  calc |H u i - H v i| = |(H u - H v) i| := by rw [sub_apply]
    _ ≤ ‖H u - H v‖ := abs_apply_le_norm _ _
    _ ≤ ‖u - v‖ := h1

variable (hN1 : ∀ x ∈ ballIn X, ∀ n, (0 ≤ x n → 0 ≤ H x n ∧ H x n ≤ x n) ∧
      (x n ≤ 0 → x n ≤ H x n ∧ H x n ≤ 0))
include hN1

lemma N1_abs {u : Linf Γ} (hu : u ∈ ballIn X) (i : Γ) : |H u i| ≤ |u i| := by
  rcases le_total 0 (u i) with h | h
  · obtain ⟨h1, h2⟩ := (hN1 u hu i).1 h
    rw [abs_of_nonneg h1, abs_of_nonneg h]; exact h2
  · obtain ⟨h1, h2⟩ := (hN1 u hu i).2 h
    rw [abs_of_nonpos h2, abs_of_nonpos h]; linarith

lemma N1_zero {u : Linf Γ} (hu : u ∈ ballIn X) {i : Γ} (h : u i = 0) : H u i = 0 := by
  have := N1_abs hN1 hu i
  rw [h, abs_zero] at this
  exact abs_nonpos_iff.1 this

/-- (N2) in the form used: a coordinate of `H u` of sign `s` is dominated by that of `u`. -/
lemma N2_mul {u : Linf Γ} (hu : u ∈ ballIn X) (i : Γ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (h : 0 < s * H u i) : s * H u i ≤ s * u i := by
  rcases hs with rfl | rfl
  · simp only [one_mul] at h ⊢
    rcases le_total 0 (u i) with h' | h'
    · exact ((hN1 u hu i).1 h').2
    · have := ((hN1 u hu i).2 h').2; linarith
  · simp only [neg_mul, one_mul, neg_pos, neg_le_neg_iff] at h ⊢
    rcases le_total 0 (u i) with h' | h'
    · have := ((hN1 u hu i).1 h').1; linarith
    · exact ((hN1 u hu i).2 h').1

/-- (N2): `u i` has the strict sign of `H u i`. -/
lemma N2_sign {u : Linf Γ} (hu : u ∈ ballIn X) (i : Γ) {a : ℝ} (h : 0 < H u i * a) :
    0 < u i * a := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := N2_mul hN1 hu i (Or.inl rfl) (by linarith)
    exact mul_pos (by linarith) h2
  · have := N2_mul hN1 hu i (Or.inr rfl) (by linarith)
    exact mul_pos_of_neg_of_neg (by linarith) h2

/-- (N2) at a unit coordinate: `|H u i| = 1` forces `u i = H u i`. -/
lemma N2_unit {u : Linf Γ} (hu : u ∈ ballIn X) (i : Γ) (h : |H u i| = 1) : u i = H u i := by
  have hu1 : |u i| ≤ 1 := (abs_apply_le_norm u i).trans (mem_ballIn.1 hu).2
  rw [abs_le] at hu1
  rcases (abs_eq zero_le_one).1 h with h1 | h1
  · have := N2_mul hN1 hu i (Or.inl rfl) (by rw [h1]; norm_num)
    rw [h1] at this ⊢; linarith
  · have := N2_mul hN1 hu i (Or.inr rfl) (by rw [h1]; norm_num)
    rw [h1] at this ⊢; linarith

end Inward

/-! ## The base point coordinate on the support of `x` -/

/-- The value of the base point at a coordinate where `x` equals `a ≠ 0`:
`sgn(a)·min(|a|+t, 1-t)`. -/
noncomputable def beta (a t : ℝ) : ℝ := if 0 < a then min (a + t) (1 - t) else max (a - t) (t - 1)

lemma beta_props {a t : ℝ} (ha0 : a ≠ 0) (ha1 : |a| ≤ 1) (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    |beta a t - a| ≤ t ∧ |beta a t| ≤ 1 - t ∧
      ∀ ρ, 0 < ρ * a → |ρ| ≤ 1 → |beta a t - ρ| < 1 - t := by
  unfold beta
  rw [abs_le] at ha1
  rcases lt_or_gt_of_ne ha0 with hneg | hpos
  · rw [if_neg (not_lt.2 hneg.le)]
    rcases le_total (a - t) (t - 1) with h | h
    · rw [max_eq_right h]
      refine ⟨by rw [abs_le]; constructor <;> linarith, by rw [abs_le]; constructor <;> linarith,
        fun ρ hρ hρ1 => ?_⟩
      have hρ0 : ρ < 0 := by
        rcases pos_and_pos_or_neg_and_neg_of_mul_pos hρ with ⟨_, h2⟩ | ⟨h1, _⟩
        · linarith
        · exact h1
      rw [abs_le] at hρ1
      rw [abs_lt]; constructor <;> linarith
    · rw [max_eq_left h]
      refine ⟨by rw [abs_le]; constructor <;> linarith, by rw [abs_le]; constructor <;> linarith,
        fun ρ hρ hρ1 => ?_⟩
      have hρ0 : ρ < 0 := by
        rcases pos_and_pos_or_neg_and_neg_of_mul_pos hρ with ⟨_, h2⟩ | ⟨h1, _⟩
        · linarith
        · exact h1
      rw [abs_le] at hρ1
      rw [abs_lt]; constructor <;> linarith
  · rw [if_pos hpos]
    rcases le_total (a + t) (1 - t) with h | h
    · rw [min_eq_left h]
      refine ⟨by rw [abs_le]; constructor <;> linarith, by rw [abs_le]; constructor <;> linarith,
        fun ρ hρ hρ1 => ?_⟩
      have hρ0 : 0 < ρ := by
        rcases pos_and_pos_or_neg_and_neg_of_mul_pos hρ with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact h1
        · linarith
      rw [abs_le] at hρ1
      rw [abs_lt]; constructor <;> linarith
    · rw [min_eq_right h]
      refine ⟨by rw [abs_le]; constructor <;> linarith, by rw [abs_le]; constructor <;> linarith,
        fun ρ hρ hρ1 => ?_⟩
      have hρ0 : 0 < ρ := by
        rcases pos_and_pos_or_neg_and_neg_of_mul_pos hρ with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact h1
        · linarith
      rw [abs_le] at hρ1
      rw [abs_lt]; constructor <;> linarith

/-! ## The displayed inequality -/

/-- If `y` is within `1 - t` of `q` off `J`, and `q j * y j ≥ t` on `J` where `q j = ±1`,
then `‖y - q‖ ≤ 1 - t`, so `σ · H(y)_n ≥ t` when `H(q)_n = σ = ±1`. -/
lemma core {X : Submodule ℝ (Linf Γ)} {H : Linf Γ → Linf Γ}
    (hlip : LipschitzOnWith 1 H (ballIn X)) {q y : Linf Γ} (hqB : q ∈ ballIn X)
    (hyB : y ∈ ballIn X) {σ t : ℝ} (hσ : σ = 1 ∨ σ = -1) (ht : t ≤ 1) (n : Γ)
    (hqn : H q n = σ) (J : Set Γ) (hqJ : ∀ j ∈ J, |q j| = 1)
    (hyJ : ∀ j ∈ J, t ≤ q j * y j) (hyq : ∀ i, i ∉ J → |y i - q i| ≤ 1 - t) :
    t ≤ σ * H y n := by
  have hnorm : ‖y - q‖ ≤ 1 - t := by
    refine norm_le_of_abs_le (by linarith) fun i => ?_
    rw [sub_apply]
    by_cases hi : i ∈ J
    · have hy1 : |y i| ≤ 1 := (abs_apply_le_norm y i).trans (mem_ballIn.1 hyB).2
      have hyJi := hyJ i hi
      rw [abs_le] at hy1
      rcases (abs_eq zero_le_one).1 (hqJ i hi) with h | h
      · rw [h] at hyJi ⊢; rw [abs_le]; constructor <;> linarith
      · rw [h] at hyJi ⊢; rw [abs_le]; constructor <;> linarith
    · exact hyq i hi
  have h := (lip_coord hlip hyB hqB n).trans hnorm
  rw [hqn, abs_le] at h
  rcases hσ with rfl | rfl
  · linarith
  · linarith

/-! ## The collision: invariance of domain on `ℝ^T` -/

open Classical in
/-- Extension by zero from a finite set `T` of coordinates. -/
noncomputable def ext (T : Finset Γ) (y : T → ℝ) : Linf Γ :=
  mkLinf (fun i => if h : i ∈ T then y ⟨i, h⟩ else 0) ‖y‖ (by
    intro i
    by_cases h : i ∈ T
    · simp only [dif_pos h]
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm y ⟨i, h⟩
    · simp only [dif_neg h, abs_zero]; exact norm_nonneg _)

lemma ext_apply_mem (T : Finset Γ) (y : T → ℝ) {i : Γ} (h : i ∈ T) : ext T y i = y ⟨i, h⟩ := by
  simp [ext, h]

lemma ext_apply_not (T : Finset Γ) (y : T → ℝ) {i : Γ} (h : i ∉ T) : ext T y i = 0 := by
  simp [ext, h]

lemma ext_lip (T : Finset Γ) : LipschitzWith 1 (ext T) := by
  refine LipschitzWith.mk_one fun y y' => ?_
  rw [dist_eq_norm]
  refine norm_le_of_abs_le dist_nonneg fun i => ?_
  rw [sub_apply]
  by_cases h : i ∈ T
  · rw [ext_apply_mem T y h, ext_apply_mem T y' h, ← Real.dist_eq]
    exact dist_le_pi_dist y y' ⟨i, h⟩
  · rw [ext_apply_not T y h, ext_apply_not T y' h, sub_zero, abs_zero]; exact dist_nonneg

/-- Near a base point `b` supported in a finite set `T ∋ n`, the image of `H` contains points
that agree with `H b` off `n` and are lower at `n` in the direction `σ`. -/
lemma exists_lower {X X' : Submodule ℝ (Linf Γ)} (hX0 : c00 Γ ≤ X) {H : Linf Γ → Linf Γ}
    (hbij : Set.BijOn H (ballIn X) (ballIn X')) (hlip : LipschitzOnWith 1 H (ballIn X))
    (hN1 : ∀ x ∈ ballIn X, ∀ n, (0 ≤ x n → 0 ≤ H x n ∧ H x n ≤ x n) ∧
      (x n ≤ 0 → x n ≤ H x n ∧ H x n ≤ 0))
    (T : Finset Γ) (b : Linf Γ) (hbT : ∀ i, i ∉ T → b i = 0)
    {δ : ℝ} (hδ : 0 < δ) (hbδ : ∀ i, |b i| + δ ≤ 1) {n : Γ} (hn : n ∈ T)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ y ∈ ballIn X, (∀ i, |y i - b i| < δ) ∧ (∀ i, i ≠ n → H y i = H b i) ∧
      σ * H y n < σ * H b n := by
  classical
  let b' : T → ℝ := fun j => b j
  have hb' : ext T b' = b := by
    refine lp.ext (funext fun i => ?_)
    by_cases h : i ∈ T
    · rw [ext_apply_mem T b' h]
    · rw [ext_apply_not T b' h, hbT i h]
  let U : Set (T → ℝ) := Metric.ball b' δ
  have hUclose : ∀ y ∈ U, ∀ i, |ext T y i - b i| < δ := by
    intro y hy i
    by_cases h : i ∈ T
    · rw [ext_apply_mem T y h, ← Real.dist_eq]
      exact lt_of_le_of_lt (dist_le_pi_dist y b' ⟨i, h⟩) hy
    · rw [ext_apply_not T y h, hbT i h, sub_zero, abs_zero]; exact hδ
  have hUball : ∀ y ∈ U, ext T y ∈ ballIn X := by
    intro y hy
    refine mem_ballIn.2 ⟨mem_of_eq_off hX0 X.zero_mem (T : Set Γ) T.finite_toSet
      (fun i hi => by rw [ext_apply_not T y hi]; rfl), ?_⟩
    refine norm_le_of_abs_le zero_le_one fun i => ?_
    have h1 := hUclose y hy i
    have h2 := hbδ i
    have h3 : |ext T y i| ≤ |ext T y i - b i| + |b i| := by
      have := abs_add_le (ext T y i - b i) (b i)
      rwa [sub_add_cancel] at this
    linarith
  let f : (T → ℝ) → (T → ℝ) := fun y j => H (ext T y) j
  have hfc : ContinuousOn f U := by
    refine continuousOn_pi.2 fun j => ?_
    have hH : ContinuousOn (fun y => H (ext T y)) U :=
      hlip.continuousOn.comp (ext_lip T).continuous.continuousOn (fun y hy => hUball y hy)
    exact (lp.lipschitzWith_one_eval ⊤ (j : Γ)).continuous.comp_continuousOn hH
  have hfinj : Set.InjOn f U := by
    intro y hy y' hy' hyy
    have hH : H (ext T y) = H (ext T y') := by
      refine lp.ext (funext fun i => ?_)
      by_cases h : i ∈ T
      · exact congrFun hyy ⟨i, h⟩
      · rw [N1_zero hN1 (hUball y hy) (ext_apply_not T y h),
          N1_zero hN1 (hUball y' hy') (ext_apply_not T y' h)]
    have he : ext T y = ext T y' := hbij.injOn (hUball y hy) (hUball y' hy') hH
    funext j
    have := congrArg (fun u : Linf Γ => u j) he
    simp only [ext_apply_mem T _ j.2] at this
    exact this
  have hopen : IsOpen (f '' U) :=
    Plasticity.Ext.InvarianceOfDomain U Metric.isOpen_ball f hfc hfinj
  have hb'U : b' ∈ U := Metric.mem_ball_self hδ
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen (f b') ⟨b', hb'U, rfl⟩
  let p : T → ℝ := fun j => f b' j - (if (j : Γ) = n then σ * (ε / 2) else 0)
  have hp : p ∈ Metric.ball (f b') ε := by
    rw [Metric.mem_ball]
    have : dist p (f b') ≤ ε / 2 := by
      refine (dist_pi_le_iff (by linarith)).2 fun j => ?_
      rw [Real.dist_eq]
      simp only [p, sub_sub_cancel_left, abs_neg]
      split_ifs
      · rcases hσ with rfl | rfl
        · rw [one_mul, abs_of_pos (by linarith)]
        · rw [neg_one_mul, abs_neg, abs_of_pos (by linarith)]
      · rw [abs_zero]; linarith
    linarith
  obtain ⟨y, hyU, hfy⟩ := hball hp
  refine ⟨ext T y, hUball y hyU, hUclose y hyU, fun i hi => ?_, ?_⟩
  · by_cases hiT : i ∈ T
    · have := congrFun hfy ⟨i, hiT⟩
      simp only [f, p, hi, if_false, sub_zero] at this
      rw [this, hb']
    · have hbB : b ∈ ballIn X := hb' ▸ hUball b' hb'U
      rw [N1_zero hN1 (hUball y hyU) (ext_apply_not T y hiT), N1_zero hN1 hbB (hbT i hiT)]
  · have := congrFun hfy ⟨n, hn⟩
    simp only [f, p, if_true] at this
    rw [this, hb']
    rcases hσ with rfl | rfl
    · linarith
    · linarith

end Sol_Plasticity_CUB37_no_collapse

open Plasticity Sol_Plasticity_CUB37_no_collapse

theorem solution {Γ : Type*} (X X' : Submodule ℝ (Linf Γ))
    (hX0 : c00 Γ ≤ X) (hX1 : X ≤ c0 Γ) (hX'0 : c00 Γ ≤ X') (hX'1 : X' ≤ c0 Γ)
    (H : Linf Γ → Linf Γ)
    (hbij : Set.BijOn H (ballIn X) (ballIn X'))
    (hlip : LipschitzOnWith 1 H (ballIn X))
    (hN1 : ∀ x ∈ ballIn X, ∀ n, (0 ≤ x n → 0 ≤ H x n ∧ H x n ≤ x n) ∧
      (x n ≤ 0 → x n ≤ H x n ∧ H x n ≤ 0))
    (x : Linf Γ) (hx : x ∈ ballIn X)
    (hmatch : ∃ w ∈ X', ∀ i, x i ≠ 0 → 0 < w i * x i)
    (n : Γ) (hn : x n ≠ 0) :
    H x n ≠ 0 := by
  classical
  intro hcol
  obtain ⟨w, hwX', hw⟩ := hmatch
  have hxX : x ∈ X := (mem_ballIn.1 hx).1
  have hx1 : ∀ i, |x i| ≤ 1 := fun i => (abs_apply_le_norm x i).trans (mem_ballIn.1 hx).2
  -- the sign `σ` of `x n`
  obtain ⟨σ, hσ, hσx⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < σ * x n := by
    rcases lt_or_gt_of_ne hn with h | h
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  -- the matching element is not zero
  have hwn : 0 < w n * x n := hw n hn
  have hwnorm : 0 < ‖w‖ := by
    have : w n ≠ 0 := by rintro h; rw [h, zero_mul] at hwn; exact lt_irrefl _ hwn
    exact lt_of_lt_of_le (abs_pos.2 this) (abs_apply_le_norm w n)
  /- The first target `z`: `w / ‖w‖` with the coordinate `n` replaced by `σ`. -/
  have hzb : ∀ i, |(fun i => if i = n then σ else w i / ‖w‖) i| ≤ 1 := by
    intro i
    simp only
    split_ifs
    · rw [hσabs]
    · rw [abs_div, abs_of_pos hwnorm, div_le_one hwnorm]; exact abs_apply_le_norm w i
  obtain ⟨z, hz_apply⟩ : ∃ z : Linf Γ, ∀ i, z i = if i = n then σ else w i / ‖w‖ :=
    ⟨mkLinf _ 1 hzb, fun i => rfl⟩
  have hzX' : z ∈ X' := by
    refine mem_of_eq_off hX'0 (X'.smul_mem ‖w‖⁻¹ hwX') {n} (Set.finite_singleton n)
      fun i hi => ?_
    have hi' : i ≠ n := hi
    rw [hz_apply, if_neg hi', lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  have hzB : z ∈ ballIn X' :=
    mem_ballIn.2 ⟨hzX', norm_le_of_abs_le zero_le_one fun i => by rw [hz_apply]; exact hzb i⟩
  have hzn : z n = σ := by rw [hz_apply, if_pos rfl]
  have hzx : ∀ i, x i ≠ 0 → 0 < z i * x i := by
    intro i hi
    rw [hz_apply]
    split_ifs with h
    · subst h; exact hσx
    · rw [div_mul_eq_mul_div]; exact div_pos (hw i hi) hwnorm
  /- The first point `q = K z`. -/
  obtain ⟨q, hqB, hqz⟩ := hbij.surjOn hzB
  have hqX : q ∈ X := (mem_ballIn.1 hqB).1
  have hq1 : ∀ i, |q i| ≤ 1 := fun i => (abs_apply_le_norm q i).trans (mem_ballIn.1 hqB).2
  have hHqn : H q n = σ := by rw [hqz, hzn]
  have hqx : ∀ i, x i ≠ 0 → 0 < q i * x i := fun i hi =>
    N2_sign hN1 hqB i (by rw [hqz]; exact hzx i hi)
  /- The finite set `J` of unit coordinates of `q` off the support of `x`. -/
  obtain ⟨J, hJ⟩ : ∃ J : Set Γ, ∀ j, j ∈ J ↔ x j = 0 ∧ |q j| = 1 :=
    ⟨{j | x j = 0 ∧ |q j| = 1}, fun j => Iff.rfl⟩
  have hJfin : J.Finite := by
    refine (finite_ge (hX1 hqX) (by norm_num : (0:ℝ) < 1 / 2)).subset ?_
    intro j hj
    rw [hJ] at hj
    show 1 / 2 ≤ |q j|
    rw [hj.2]; norm_num
  /- The second target `z'`: `z` with the coordinates in `J` replaced by those of `q`. -/
  have hz'b : ∀ i, |(fun i => if i ∈ J then q i else z i) i| ≤ 1 := by
    intro i
    simp only
    split_ifs
    · exact hq1 i
    · exact (abs_apply_le_norm z i).trans (mem_ballIn.1 hzB).2
  obtain ⟨z', hz'_apply⟩ : ∃ z' : Linf Γ, ∀ i, z' i = if i ∈ J then q i else z i :=
    ⟨mkLinf _ 1 hz'b, fun i => rfl⟩
  have hz'X' : z' ∈ X' :=
    mem_of_eq_off hX'0 hzX' J hJfin fun i hi => by rw [hz'_apply, if_neg hi]
  have hz'B : z' ∈ ballIn X' :=
    mem_ballIn.2 ⟨hz'X', norm_le_of_abs_le zero_le_one fun i => by rw [hz'_apply]; exact hz'b i⟩
  /- The second point `r = K z'`. -/
  obtain ⟨r, hrB, hrz⟩ := hbij.surjOn hz'B
  have hrX : r ∈ X := (mem_ballIn.1 hrB).1
  have hr1 : ∀ i, |r i| ≤ 1 := fun i => (abs_apply_le_norm r i).trans (mem_ballIn.1 hrB).2
  have hHrJ : ∀ j ∈ J, H r j = q j := fun j hj => by rw [hrz, hz'_apply, if_pos hj]
  have hrx : ∀ i, x i ≠ 0 → 0 < r i * x i := fun i hi => by
    have hiJ : i ∉ J := fun h => hi ((hJ i).1 h).1
    exact N2_sign hN1 hrB i (by rw [hrz, hz'_apply, if_neg hiJ]; exact hzx i hi)
  /- `M`: the supremum of `|q i|` off `supp x ∪ J`, which is below `1`. -/
  obtain ⟨M, hM0, hM1, hM⟩ := exists_bound_lt (hX1 hqX) one_pos
    (fun i => x i = 0 ∧ i ∉ J)
    (fun i hi => lt_of_le_of_ne (hq1 i) (fun h => hi.2 ((hJ i).2 ⟨hi.1, h⟩)))
  obtain ⟨t, ht0, ht1, htM⟩ : ∃ t : ℝ, 0 < t ∧ t < 1 / 2 ∧ t + M < 1 - t :=
    ⟨(1 - M) / 4, by linarith, by linarith, by linarith⟩
  /- The finite set `T`. -/
  have hT₀ : (({n} ∪ {i | t ≤ |x i|}) ∪ {i | 1 - t ≤ |q i|} ∪ {i | 1 - t ≤ |r i|} :
      Set Γ).Finite :=
    (((Set.finite_singleton n).union (finite_ge (hX1 hxX) ht0)).union
      (finite_ge (hX1 hqX) (by linarith))).union (finite_ge (hX1 hrX) (by linarith))
  obtain ⟨T, hT⟩ : ∃ T : Finset Γ, ∀ i, i ∈ T ↔
      ((i = n ∨ t ≤ |x i|) ∨ 1 - t ≤ |q i|) ∨ 1 - t ≤ |r i| :=
    ⟨hT₀.toFinset, fun i => by rw [Set.Finite.mem_toFinset]; rfl⟩
  have hnT : n ∈ T := (hT n).2 (Or.inl (Or.inl (Or.inl rfl)))
  have hJT : ∀ j ∈ J, j ∈ T := fun j hj =>
    (hT j).2 (Or.inl (Or.inr (by rw [((hJ j).1 hj).2]; linarith)))
  have hTc : ∀ i, i ∉ T → |x i| < t ∧ |q i| < 1 - t ∧ |r i| < 1 - t := by
    intro i hi
    rw [hT] at hi
    simp only [not_or, not_le] at hi
    exact ⟨hi.1.1.2, hi.1.2, hi.2⟩
  /- The base point `b`. -/
  have hbfb : ∀ i, |(fun i => if i ∈ T then (if x i = 0 then t * r i else beta (x i) t)
      else 0) i| ≤ 1 - t := by
    intro i
    simp only
    split_ifs with hiT hxi
    · rw [abs_mul, abs_of_pos ht0]
      nlinarith [hr1 i, abs_nonneg (r i)]
    · exact (beta_props hxi (hx1 i) ht0 ht1).2.1
    · rw [abs_zero]; linarith
  obtain ⟨b, hb_apply⟩ : ∃ b : Linf Γ, ∀ i,
      b i = if i ∈ T then (if x i = 0 then t * r i else beta (x i) t) else 0 :=
    ⟨mkLinf _ (1 - t) hbfb, fun i => rfl⟩
  have hb_zero : ∀ i, i ∈ T → x i = 0 → b i = t * r i := fun i h1 h2 => by
    rw [hb_apply, if_pos h1, if_pos h2]
  have hb_supp : ∀ i, i ∈ T → x i ≠ 0 → b i = beta (x i) t := fun i h1 h2 => by
    rw [hb_apply, if_pos h1, if_neg h2]
  have hbT : ∀ i, i ∉ T → b i = 0 := fun i h => by rw [hb_apply, if_neg h]
  have hb1 : ∀ i, |b i| ≤ 1 - t := fun i => by rw [hb_apply]; exact hbfb i
  have hbX : b ∈ X :=
    mem_of_eq_off hX0 X.zero_mem (T : Set Γ) T.finite_toSet fun i hi => by rw [hbT i hi]; rfl
  have hbB : b ∈ ballIn X :=
    mem_ballIn.2 ⟨hbX, norm_le_of_abs_le zero_le_one fun i => by linarith [hb1 i]⟩
  /- (a) `‖b - x‖ ≤ t`. -/
  have hba : ‖b - x‖ ≤ t := by
    refine norm_le_of_abs_le ht0.le fun i => ?_
    rw [sub_apply]
    by_cases hiT : i ∈ T
    · by_cases hxi : x i = 0
      · rw [hb_zero i hiT hxi, hxi, sub_zero, abs_mul, abs_of_pos ht0]
        nlinarith [hr1 i, abs_nonneg (r i)]
      · rw [hb_supp i hiT hxi]; exact (beta_props hxi (hx1 i) ht0 ht1).1
    · rw [hbT i hiT, zero_sub, abs_neg]; exact (hTc i hiT).1.le
  /- (b) `‖b - r‖ ≤ 1 - t`. -/
  have hbr : ‖b - r‖ ≤ 1 - t := by
    refine norm_le_of_abs_le (by linarith) fun i => ?_
    rw [sub_apply]
    by_cases hiT : i ∈ T
    · by_cases hxi : x i = 0
      · rw [hb_zero i hiT hxi]
        have : t * r i - r i = -((1 - t) * r i) := by ring
        rw [this, abs_neg, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 1 - t)]
        nlinarith [hr1 i, abs_nonneg (r i)]
      · rw [hb_supp i hiT hxi]
        exact ((beta_props hxi (hx1 i) ht0 ht1).2.2 (r i) (hrx i hxi) (hr1 i)).le
    · rw [hbT i hiT, zero_sub, abs_neg]; exact (hTc i hiT).2.2.le
  /- (c) `|b i - q i| < 1 - t` off `J`, hence `≤ θ < 1 - t` there. -/
  have hbq : ∀ i, i ∉ J → |(b - q) i| < 1 - t := by
    intro i hiJ
    rw [sub_apply]
    by_cases hiT : i ∈ T
    · by_cases hxi : x i = 0
      · rw [hb_zero i hiT hxi]
        have h1 : |t * r i - q i| ≤ t * |r i| + |q i| := by
          calc |t * r i - q i| ≤ |t * r i| + |q i| := abs_sub _ _
            _ = t * |r i| + |q i| := by rw [abs_mul, abs_of_pos ht0]
        have h2 : t * |r i| ≤ t := by nlinarith [hr1 i, abs_nonneg (r i)]
        have h3 := hM i ⟨hxi, hiJ⟩
        linarith
      · rw [hb_supp i hiT hxi]
        exact (beta_props hxi (hx1 i) ht0 ht1).2.2 (q i) (hqx i hxi) (hq1 i)
    · rw [hbT i hiT, zero_sub, abs_neg]; exact (hTc i hiT).2.1
  obtain ⟨θ, hθ0, hθ1, hθ⟩ := exists_bound_lt (hX1 (X.sub_mem hbX hqX))
    (by linarith : (0:ℝ) < 1 - t) (fun i => i ∉ J) hbq
  /- The values of `H` at `b`: `σ H(b)_n ≤ t` and `q_j H(b)_j ≥ t` on `J`. -/
  have hHbn : σ * H b n ≤ t := by
    have h1 := lip_coord hlip hbB hx n
    rw [hcol, sub_zero] at h1
    calc σ * H b n ≤ |σ * H b n| := le_abs_self _
      _ = |H b n| := by rw [abs_mul, hσabs, one_mul]
      _ ≤ ‖b - x‖ := h1
      _ ≤ t := hba
  have hqJ : ∀ j ∈ J, |q j| = 1 := fun j hj => ((hJ j).1 hj).2
  have hHbJ : ∀ j ∈ J, t ≤ q j * H b j := by
    intro j hj
    have h1 := (lip_coord hlip hbB hrB j).trans hbr
    rw [hHrJ j hj, abs_le] at h1
    rcases (abs_eq zero_le_one).1 (hqJ j hj) with h | h
    · rw [h] at h1 ⊢; linarith
    · rw [h] at h1 ⊢; linarith
  /- The collision. -/
  obtain ⟨δ, hδ0, hδt, hδθ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ t ∧ δ ≤ 1 - t - θ :=
    ⟨min t (1 - t - θ), lt_min ht0 (by linarith), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨y, hyB, hyb, hyH, hyn⟩ := exists_lower hX0 hbij hlip hN1 T b hbT hδ0
    (fun i => by linarith [hb1 i]) hnT hσ
  have hyJ : ∀ j ∈ J, t ≤ q j * y j := by
    intro j hj
    have hjn : j ≠ n := fun h => hn (h ▸ ((hJ j).1 hj).1)
    have h1 : t ≤ q j * H y j := by rw [hyH j hjn]; exact hHbJ j hj
    have hs : q j = 1 ∨ q j = -1 := (abs_eq zero_le_one).1 (hqJ j hj)
    exact h1.trans (N2_mul hN1 hyB j hs (by linarith))
  have hyq : ∀ i, i ∉ J → |y i - q i| ≤ 1 - t := by
    intro i hiJ
    have h1 := hyb i
    have h2 := hθ i hiJ
    rw [sub_apply] at h2
    have h3 : |y i - q i| ≤ |y i - b i| + |b i - q i| := abs_sub_le _ _ _
    linarith
  have := core hlip hqB hyB hσ (by linarith) n hHqn J hqJ hyJ hyq
  linarith
