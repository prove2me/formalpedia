-- Prove2me | solution 1 for Rudin.ch09_C1_iff_partials_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T03:11:01.397161+00:00
-- url     : https://prove2.me/submissions/b3bde9c6-32be-4b22-8979-319e5da6b4c6

import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Partial derivatives and total differentiability

Mathlib has no bridge between the existence of continuous partial derivatives and Fréchet
differentiability.  This file builds one, for maps between Euclidean spaces.
-/

namespace MvPartial

open Set Filter

variable {n m : ℕ}

/-- The `j`-th coordinate vector of `ℝⁿ`. -/
noncomputable def e (j : Fin n) : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j (1 : ℝ)

@[simp] theorem e_apply (j i : Fin n) : (e j) i = if j = i then (1:ℝ) else 0 := by
  simp [e, EuclideanSpace.single, PiLp.single_apply, eq_comm]

@[simp] theorem norm_e (j : Fin n) : ‖e j‖ = 1 := by
  simp [e]

/-- A vector dominated coordinatewise by another has no larger Euclidean norm. -/
theorem norm_le_of_abs_le {v w : EuclideanSpace ℝ (Fin n)} (h : ∀ i, |v i| ≤ |w i|) :
    ‖v‖ ≤ ‖w‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖v i‖ = |v i| := rfl
  have h2 : ‖w i‖ = |w i| := rfl
  rw [h1, h2]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2

theorem abs_coord_le (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) : |v i| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v i
  simpa using this

/-- Expansion of a vector in the coordinate basis. -/
theorem sum_smul_e (v : EuclideanSpace ℝ (Fin n)) : ∑ j, v j • e j = v := by
  ext i
  have hsum : ((∑ j, v j • e j) : EuclideanSpace ℝ (Fin n)) i = ∑ j, (v j • e j) i := by
    simp
  rw [hsum]
  simp only [PiLp.smul_apply, smul_eq_mul, e_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ i (fun j => v j)]
  simp


variable {E : Set (EuclideanSpace ℝ (Fin n))}
  {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
  {D : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- The linear map assembled from a family of partial derivatives at a point. -/
noncomputable def assembleₗ (D : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) where
  toFun v := ∑ j, v j • D j x
  map_add' u v := by
    simp only [PiLp.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' c v := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul]

/-- The candidate total derivative assembled from the partial derivatives. -/
noncomputable def assemble (D : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (assembleₗ D x).toContinuousLinearMap

@[simp] theorem assemble_apply (x v : EuclideanSpace ℝ (Fin n)) :
    assemble D x v = ∑ j, v j • D j x := rfl

/-- The partial derivative hypothesis, transported along the `j`-th axis. -/
theorem hasDerivAt_shift (hD : ∀ j : Fin n, ∀ y ∈ E,
      HasDerivAt (fun t : ℝ => f (y + t • e j)) (D j y) 0)
    (j : Fin n) (p : EuclideanSpace ℝ (Fin n)) (s : ℝ) (hs : p + s • e j ∈ E) :
    HasDerivAt (fun t : ℝ => f (p + t • e j)) (D j (p + s • e j)) s := by
  have hq := hD j (p + s • e j) hs
  have hq0 : HasDerivAt (fun t : ℝ => f (p + s • e j + t • e j)) (D j (p + s • e j)) (s - s) := by
    simpa using hq
  have hcomp := hq0.comp_sub_const s s
  have hfun : (fun t : ℝ => f (p + s • e j + (t - s) • e j)) = fun t : ℝ => f (p + t • e j) := by
    funext t
    congr 1
    rw [add_assoc, ← add_smul]
    ring_nf
  rwa [hfun] at hcomp


/-- The point reached from `x` after replacing the first `k` coordinates by those of `x + h`. -/
noncomputable def step (x h : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x
  | (k + 1) => if hk : k < n then step x h k + h ⟨k, hk⟩ • e ⟨k, hk⟩ else step x h k

theorem step_apply (x h : EuclideanSpace ℝ (Fin n)) (k : ℕ) (i : Fin n) :
    (step x h k) i = if (i : ℕ) < k then x i + h i else x i := by
  induction k with
  | zero => simp [step]
  | succ k ih =>
    by_cases hk : k < n
    · rw [step, dif_pos hk]
      have hco : ((step x h k + h ⟨k, hk⟩ • e ⟨k, hk⟩ : EuclideanSpace ℝ (Fin n)) i)
          = (step x h k) i + h ⟨k, hk⟩ * (e (⟨k, hk⟩ : Fin n)) i := by simp
      rw [hco, ih, e_apply]
      rcases Nat.lt_trichotomy (i : ℕ) k with h1 | h1 | h1
      · have c3 : (⟨k, hk⟩ : Fin n) ≠ i := by
          intro hc; have hv := congrArg Fin.val hc; simp at hv; omega
        have c2 : (i : ℕ) < k + 1 := by omega
        simp [h1, c2, c3]
      · have hik : (⟨k, hk⟩ : Fin n) = i := Fin.ext h1.symm
        have c1 : ¬ ((i : ℕ) < k) := by omega
        have c2 : (i : ℕ) < k + 1 := by omega
        simp [c1, c2, hik]
      · have c3 : (⟨k, hk⟩ : Fin n) ≠ i := by
          intro hc; have hv := congrArg Fin.val hc; simp at hv; omega
        have c1 : ¬ ((i : ℕ) < k) := by omega
        have c2 : ¬ ((i : ℕ) < k + 1) := by omega
        simp [c1, c2, c3]
    · rw [step, dif_neg hk, ih]
      have : (i : ℕ) < k := lt_of_lt_of_le i.isLt (by omega)
      rw [if_pos this, if_pos (by omega)]

theorem step_zero (x h : EuclideanSpace ℝ (Fin n)) : step x h 0 = x := rfl

theorem step_n (x h : EuclideanSpace ℝ (Fin n)) : step x h n = x + h := by
  ext i
  rw [step_apply, if_pos i.isLt]
  simp

theorem step_succ (x h : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk : k < n) :
    step x h (k + 1) = step x h k + h ⟨k, hk⟩ • e ⟨k, hk⟩ := by
  rw [step, dif_pos hk]

/-- Every point on the segment used at stage `k` stays within `‖h‖` of `x`. -/
theorem norm_step_seg_le (x h : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk : k < n) {t : ℝ}
    (ht : |t| ≤ |h ⟨k, hk⟩|) :
    ‖step x h k + t • e ⟨k, hk⟩ - x‖ ≤ ‖h‖ := by
  refine norm_le_of_abs_le fun i => ?_
  have hco : ((step x h k + t • e ⟨k, hk⟩ - x : EuclideanSpace ℝ (Fin n)) i)
      = (step x h k) i + t * (e (⟨k, hk⟩ : Fin n)) i - x i := by simp
  rw [hco, step_apply, e_apply]
  rcases Nat.lt_trichotomy (i : ℕ) k with h1 | h1 | h1
  · have c3 : (⟨k, hk⟩ : Fin n) ≠ i := by
      intro hc; have hv := congrArg Fin.val hc; simp at hv; omega
    simp [h1, c3]
  · have hik : (⟨k, hk⟩ : Fin n) = i := Fin.ext h1.symm
    have c1 : ¬ ((i : ℕ) < k) := by omega
    rw [if_neg c1, if_pos hik]
    have hsimp : x i + t * 1 - x i = t := by ring
    rw [hsimp, ← hik]
    exact ht
  · have c3 : (⟨k, hk⟩ : Fin n) ≠ i := by
      intro hc; have hv := congrArg Fin.val hc; simp at hv; omega
    have c1 : ¬ ((i : ℕ) < k) := by omega
    simp [c1, c3]


/-- One stage of the telescoping estimate: along the `k`-th axis the increment of `f` differs
from `hₖ · Dₖ(x)` by at most `ε |hₖ|`. -/
theorem stage_estimate
    (hD : ∀ j : Fin n, ∀ y ∈ E, HasDerivAt (fun t : ℝ => f (y + t • e j)) (D j y) 0)
    {x h : EuclideanSpace ℝ (Fin n)} {k : ℕ} (hk : k < n) {ε : ℝ}
    (hseg : ∀ t : ℝ, |t| ≤ |h ⟨k, hk⟩| → step x h k + t • e ⟨k, hk⟩ ∈ E)
    (hbound : ∀ t : ℝ, |t| ≤ |h ⟨k, hk⟩| →
      ‖D ⟨k, hk⟩ (step x h k + t • e ⟨k, hk⟩) - D ⟨k, hk⟩ x‖ ≤ ε) :
    ‖f (step x h (k + 1)) - f (step x h k) - h ⟨k, hk⟩ • D ⟨k, hk⟩ x‖ ≤ ε * |h ⟨k, hk⟩| := by
  classical
  set j : Fin n := ⟨k, hk⟩ with hj
  set p : EuclideanSpace ℝ (Fin n) := step x h k with hp
  set φ : ℝ → EuclideanSpace ℝ (Fin m) := fun t => f (p + t • e j) - t • D j x with hφ
  have hderiv : ∀ t : ℝ, |t| ≤ |h j| →
      HasDerivAt φ (D j (p + t • e j) - D j x) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℝ => f (p + u • e j)) (D j (p + t • e j)) t :=
      hasDerivAt_shift hD j p t (hseg t ht)
    have h2 : HasDerivAt (fun u : ℝ => u • D j x) (D j x) t := by
      simpa using (hasDerivAt_id t).smul_const (D j x)
    exact h1.sub h2
  have hkey : ∀ a b : ℝ, a ≤ b → (∀ t ∈ Set.Icc a b, |t| ≤ |h j|) →
      ‖φ b - φ a‖ ≤ ε * (b - a) := by
    intro a b hab hsub
    have hd : ∀ t ∈ Set.Icc a b, HasDerivWithinAt φ (D j (p + t • e j) - D j x) (Set.Icc a b) t :=
      fun t ht => (hderiv t (hsub t ht)).hasDerivWithinAt
    have hbd : ∀ t ∈ Set.Ico a b, ‖D j (p + t • e j) - D j x‖ ≤ ε :=
      fun t ht => hbound t (hsub t (Set.Ico_subset_Icc_self ht))
    exact norm_image_sub_le_of_norm_deriv_le_segment' hd hbd b (Set.right_mem_Icc.2 hab)
  have hstep1 : f (step x h (k + 1)) = f (p + h j • e j) := by rw [step_succ x h hk]
  have hφ0 : φ 0 = f p := by simp [hφ]
  have hφh : φ (h j) = f (p + h j • e j) - h j • D j x := by simp [hφ]
  have hre : f (p + h j • e j) - f p - h j • D j x
      = (f (p + h j • e j) - h j • D j x) - f p := by abel
  rcases le_total 0 (h j) with hpos | hneg
  · have hsub : ∀ t ∈ Set.Icc (0:ℝ) (h j), |t| ≤ |h j| := by
      intro t ht
      rw [abs_of_nonneg ht.1, abs_of_nonneg hpos]
      exact ht.2
    have := hkey 0 (h j) hpos hsub
    rw [hφ0, hφh] at this
    rw [hstep1, hre]
    calc ‖f (p + h j • e j) - h j • D j x - f p‖ ≤ ε * (h j - 0) := this
      _ = ε * |h j| := by rw [abs_of_nonneg hpos]; ring
  · have hsub : ∀ t ∈ Set.Icc (h j) (0:ℝ), |t| ≤ |h j| := by
      intro t ht
      rw [abs_of_nonpos ht.2, abs_of_nonpos hneg]
      linarith [ht.1]
    have := hkey (h j) 0 hneg hsub
    rw [hφ0, hφh] at this
    rw [hstep1, hre, norm_sub_rev]
    calc ‖f p - (f (p + h j • e j) - h j • D j x)‖ ≤ ε * (0 - h j) := this
      _ = ε * |h j| := by rw [abs_of_nonpos hneg]; ring


/-- The telescoping sum of the stage increments. -/
theorem telescope (x h : EuclideanSpace ℝ (Fin n)) :
    f (x + h) - f x - assemble D x h
      = ∑ k ∈ Finset.range n, (if hk : k < n then
          f (step x h (k + 1)) - f (step x h k) - h ⟨k, hk⟩ • D ⟨k, hk⟩ x else 0) := by
  have h1 : ∑ k ∈ Finset.range n, (f (step x h (k + 1)) - f (step x h k))
      = f (step x h n) - f (step x h 0) := Finset.sum_range_sub (fun k => f (step x h k)) n
  have h2 : ∑ k ∈ Finset.range n, (if hk : k < n then h ⟨k, hk⟩ • D ⟨k, hk⟩ x else 0)
      = ∑ j : Fin n, h j • D j x := by
    rw [Finset.sum_range fun k => (if hk : k < n then h ⟨k, hk⟩ • D ⟨k, hk⟩ x else 0)]
    exact Finset.sum_congr rfl fun j _ => by rw [dif_pos j.isLt]
  have h3 : ∑ k ∈ Finset.range n, (if hk : k < n then
      f (step x h (k + 1)) - f (step x h k) - h ⟨k, hk⟩ • D ⟨k, hk⟩ x else 0)
      = ∑ k ∈ Finset.range n, (f (step x h (k + 1)) - f (step x h k))
        - ∑ k ∈ Finset.range n, (if hk : k < n then h ⟨k, hk⟩ • D ⟨k, hk⟩ x else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [dif_pos hk, dif_pos hk]
  rw [h3, h1, h2, step_zero, step_n, assemble_apply]

/-- **Continuous partial derivatives give total differentiability.** -/
theorem hasFDerivAt_of_partials (hE : IsOpen E)
    (hD : ∀ j : Fin n, ∀ y ∈ E, HasDerivAt (fun t : ℝ => f (y + t • e j)) (D j y) 0)
    (hcont : ∀ j : Fin n, ContinuousOn (D j) E)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ E) :
    HasFDerivAt f (assemble D x) x := by
  classical
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  set ε : ℝ := c / (n + 1) with hε
  have hεpos : 0 < ε := by positivity
  -- pick a ball on which every `D j` stays within `ε` of its value at `x`
  have hballs : ∀ j : Fin n, ∃ δ > 0, ∀ y, ‖y - x‖ ≤ δ → y ∈ E ∧ ‖D j y - D j x‖ ≤ ε := by
    intro j
    have h1 := (hcont j x hx)
    rw [Metric.continuousWithinAt_iff] at h1
    obtain ⟨δ1, hδ1, hδ1'⟩ := h1 ε hεpos
    obtain ⟨δ2, hδ2, hδ2'⟩ := Metric.isOpen_iff.1 hE x hx
    refine ⟨min δ1 δ2 / 2, by positivity, fun y hy => ?_⟩
    have hd : dist y x < min δ1 δ2 := by
      rw [dist_eq_norm]
      have : min δ1 δ2 / 2 < min δ1 δ2 := by
        have : 0 < min δ1 δ2 := lt_min hδ1 hδ2
        linarith
      linarith
    have hyE : y ∈ E := hδ2' (by rw [Metric.mem_ball]; exact lt_of_lt_of_le hd (min_le_right _ _))
    exact ⟨hyE, le_of_lt (hδ1' hyE (lt_of_lt_of_le hd (min_le_left _ _)))⟩
  choose δ hδpos hδ using hballs
  set d : ℝ := if h : (Finset.univ : Finset (Fin n)).Nonempty then Finset.univ.inf' h δ else 1
    with hd
  have hdpos : 0 < d := by
    rw [hd]
    split
    · rename_i hne
      exact (Finset.lt_inf'_iff hne).2 fun j _ => hδpos j
    · norm_num
  have hdle : ∀ j : Fin n, d ≤ δ j := by
    intro j
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨j, Finset.mem_univ j⟩
    rw [hd, dif_pos hne]
    exact Finset.inf'_le _ (Finset.mem_univ j)
  rw [Metric.eventually_nhds_iff]
  refine ⟨d, hdpos, fun y hy => ?_⟩
  set h : EuclideanSpace ℝ (Fin n) := y - x with hh
  have hnh : ‖h‖ < d := by rw [hh, ← dist_eq_norm]; exact hy
  have hyx : y = x + h := by rw [hh]; abel
  -- each stage is controlled
  have hstage : ∀ k : ℕ, ∀ hk : k < n,
      ‖f (step x h (k + 1)) - f (step x h k) - h ⟨k, hk⟩ • D ⟨k, hk⟩ x‖ ≤ ε * |h ⟨k, hk⟩| := by
    intro k hk
    refine stage_estimate hD hk ?_ ?_
    · intro t ht
      exact (hδ ⟨k, hk⟩ _ (le_of_lt (lt_of_le_of_lt (norm_step_seg_le x h hk ht)
        (lt_of_lt_of_le hnh (hdle ⟨k, hk⟩))))).1
    · intro t ht
      exact (hδ ⟨k, hk⟩ _ (le_of_lt (lt_of_le_of_lt (norm_step_seg_le x h hk ht)
        (lt_of_lt_of_le hnh (hdle ⟨k, hk⟩))))).2
  -- sum up
  have hsum : ‖f (x + h) - f x - assemble D x h‖ ≤ ∑ k ∈ Finset.range n, ε * ‖h‖ := by
    rw [telescope]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k hk => ?_)
    rw [Finset.mem_range] at hk
    rw [dif_pos hk]
    exact le_trans (hstage k hk) (by
      have := abs_coord_le h ⟨k, hk⟩
      nlinarith [hεpos, abs_nonneg (h ⟨k, hk⟩)])
  rw [hyx]
  have hfin : ∑ k ∈ Finset.range n, ε * ‖h‖ = n * (ε * ‖h‖) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hfin] at hsum
  have hnorm : ‖y - x‖ = ‖h‖ := by rw [hh]
  rw [hnorm]
  refine le_trans hsum ?_
  have hnn : (0:ℝ) ≤ ‖h‖ := norm_nonneg _
  have hεc : (n : ℝ) * ε ≤ c := by
    rw [hε]
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hc]
  nlinarith [hεc, hnn]


theorem assemble_sub_apply (x y v : EuclideanSpace ℝ (Fin n)) :
    (assemble D x - assemble D y) v = ∑ j, v j • (D j x - D j y) := by
  simp only [ContinuousLinearMap.sub_apply, assemble_apply, smul_sub]
  exact (Finset.sum_sub_distrib _ _).symm

theorem norm_assemble_sub_le (x y : EuclideanSpace ℝ (Fin n)) :
    ‖assemble D x - assemble D y‖ ≤ ∑ j, ‖D j x - D j y‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun j _ => norm_nonneg _) ?_
  intro v
  rw [assemble_sub_apply]
  refine le_trans (norm_sum_le Finset.univ (fun j : Fin n => v j • (D j x - D j y))) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_smul, Real.norm_eq_abs]
  nlinarith [abs_coord_le v j, norm_nonneg (D j x - D j y), abs_nonneg (v j)]

theorem assemble_continuousOn (hcont : ∀ j : Fin n, ContinuousOn (D j) E) :
    ContinuousOn (fun x => assemble D x) E := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hεn : 0 < ε / (n + 1) := by positivity
  have hch : ∀ j : Fin n, ∃ δ > 0, ∀ y ∈ E, dist y x < δ → ‖D j y - D j x‖ < ε / (n + 1) := by
    intro j
    have h1 := hcont j x hx
    rw [Metric.continuousWithinAt_iff] at h1
    obtain ⟨δ, hδ, hδ'⟩ := h1 (ε / (n + 1)) hεn
    exact ⟨δ, hδ, fun y hy hd => by rw [← dist_eq_norm]; exact hδ' hy hd⟩
  choose δ hδpos hδ using hch
  set d : ℝ := if h : (Finset.univ : Finset (Fin n)).Nonempty then Finset.univ.inf' h δ else 1
    with hd
  have hdpos : 0 < d := by
    rw [hd]; split
    · rename_i hne; exact (Finset.lt_inf'_iff hne).2 fun j _ => hδpos j
    · norm_num
  refine ⟨d, hdpos, fun y hy hdist => ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (norm_assemble_sub_le y x) ?_
  have hb : ∀ j : Fin n, ‖D j y - D j x‖ < ε / (n + 1) := by
    intro j
    refine hδ j y hy (lt_of_lt_of_le hdist ?_)
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨j, Finset.mem_univ j⟩
    rw [hd, dif_pos hne]
    exact Finset.inf'_le _ (Finset.mem_univ j)
  calc ∑ j, ‖D j y - D j x‖ ≤ ∑ _j : Fin n, ε / (n + 1) :=
        Finset.sum_le_sum fun j _ => le_of_lt (hb j)
    _ = n * (ε / (n + 1)) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [hε]

/-- **Continuous partial derivatives give a `C¹` map.** -/
theorem contDiffOn_one_of_partials (hE : IsOpen E)
    (hD : ∀ j : Fin n, ∀ y ∈ E, HasDerivAt (fun t : ℝ => f (y + t • e j)) (D j y) 0)
    (hcont : ∀ j : Fin n, ContinuousOn (D j) E) :
    ContDiffOn ℝ 1 f E := by
  intro x hx
  have hone : (1 : WithTop ℕ∞) = ((0 : ℕ) : WithTop ℕ∞) + 1 := by norm_num
  have h1 : ContDiffAt ℝ 1 f x := by
    rw [hone, contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨fun y => assemble D y, ⟨E, hE.mem_nhds hx, fun y hy => hasFDerivAt_of_partials hE hD hcont hy⟩, ?_⟩
    simp only [Nat.cast_zero]
    rw [contDiffAt_zero]
    exact ⟨E, hE.mem_nhds hx, assemble_continuousOn hcont⟩
  exact h1.contDiffWithinAt


/-- Conversely, a `C¹` map has continuous partial derivatives. -/
theorem partials_of_contDiffOn_one (hE : IsOpen E) (hf : ContDiffOn ℝ 1 f E) :
    ∃ D : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m),
      (∀ j : Fin n, ∀ x ∈ E, HasDerivAt (fun t : ℝ => f (x + t • e j)) (D j x) 0) ∧
      (∀ j : Fin n, ContinuousOn (D j) E) := by
  refine ⟨fun j x => fderiv ℝ f x (e j), ?_, ?_⟩
  · intro j x hx
    have hdiff : DifferentiableAt ℝ f x :=
      ((hf.differentiableOn (by norm_num)).differentiableAt (hE.mem_nhds hx))
    have hfd : HasFDerivAt f (fderiv ℝ f x) x := hdiff.hasFDerivAt
    have h0 : HasDerivAt (fun t : ℝ => t • e j) (e j) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).smul_const (e j)
    have hline : HasDerivAt (fun t : ℝ => x + t • e j) (e j) 0 := by
      simpa using h0.const_add x
    have hfd0 : HasFDerivAt f (fderiv ℝ f x) ((fun t : ℝ => x + t • e j) 0) := by simpa using hfd
    have hcomp := hfd0.comp_hasDerivAt 0 hline
    simpa [Function.comp_def] using hcomp
  · intro j
    have hcont : ContinuousOn (fun x => fderiv ℝ f x) E :=
      hf.continuousOn_fderiv_of_isOpen hE le_rfl
    exact (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin m)) (e j)).continuous.comp_continuousOn
      hcont

/-- **Rudin, Theorem 9.21.**  A map between Euclidean spaces is `C¹` on an open set exactly when
its partial derivatives exist there and are continuous. -/
theorem contDiffOn_one_iff_partials (hE : IsOpen E) :
    ContDiffOn ℝ 1 f E ↔
      ∃ D : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m),
        (∀ j : Fin n, ∀ x ∈ E, HasDerivAt (fun t : ℝ => f (x + t • e j)) (D j x) 0) ∧
        (∀ j : Fin n, ContinuousOn (D j) E) := by
  constructor
  · exact partials_of_contDiffOn_one hE
  · rintro ⟨D, hD, hcont⟩
    exact contDiffOn_one_of_partials hE hD hcont

end MvPartial

open Filter Topology in
theorem solution (n m : ℕ) (E : Set (EuclideanSpace ℝ (Fin n)))
    (hE : IsOpen E) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) :
    ContDiffOn ℝ 1 f E ↔
      ∃ D : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m),
        (∀ j : Fin n, ∀ x ∈ E,
          HasDerivAt (fun t : ℝ => f (x + t • EuclideanSpace.single j (1 : ℝ))) (D j x) 0) ∧
        (∀ j : Fin n, ContinuousOn (D j) E) :=
  MvPartial.contDiffOn_one_iff_partials hE
