-- Prove2me | solution 1 for TalagrandConc.ConvexHull.exp_fAlpha_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T03:56:33.699645+00:00
-- url     : https://prove2.me/submissions/75cc5dc3-fbdc-436d-9b41-b149bfe194b6

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

set_option autoImplicit false

namespace TalConvP

open TalagrandConc.ConvexHull

/-- `ξ(α, 1-λ)` in the `λ` parametrisation. -/
lemma xi_one_sub (α l : ℝ) :
    xi α (1 - l) = α * l * Real.log l - (1 + α * l) * Real.log ((1 + α * l) / (1 + α)) := by
  unfold xi
  have h1 : (1 : ℝ) - (1 - l) = l := by ring
  have h2 : α + 1 - α * (1 - l) = 1 + α * l := by ring
  have h3 : 1 + α - α * (1 - l) = 1 + α * l := by ring
  rw [h1, h2, h3]

/-- The equality case: `r (1 + αλ) = λ (1 + α)`. -/
lemma xi_eq_of (α l r : ℝ) (hα : 0 < α) (hl : 0 < l) (hr : 0 < r)
    (hrl : r * (1 + α * l) = l * (1 + α)) :
    xi α (1 - l) = Real.log (1 + α - α * r) + α * l * Real.log r := by
  rw [xi_one_sub]
  have hc : 0 < 1 + α * l := by positivity
  have hd : 0 < 1 + α := by linarith
  have hr' : r = l * (1 + α) / (1 + α * l) := by
    field_simp; linarith
  have hD : 1 + α - α * r = (1 + α) / (1 + α * l) := by
    rw [hr']; field_simp; ring
  have hm : l * (1 + α) ≠ 0 := by positivity
  rw [hD, hr', Real.log_div hm hc.ne', Real.log_mul hl.ne' hd.ne',
    Real.log_div hc.ne' hd.ne', Real.log_div hd.ne' hc.ne']
  ring

/-- The upper bound: for all `r ∈ (0,1]`, `log(1+α-αr) + αλ log r ≤ ξ(α, 1-λ)`. -/
lemma xi_ge (α l r : ℝ) (hα : 0 < α) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) :
    Real.log (1 + α - α * r) + α * l * Real.log r ≤ xi α (1 - l) := by
  have hd : 0 < 1 + α := by linarith
  have hD : 0 < 1 + α - α * r := by nlinarith
  rcases hl0.lt_or_eq with hl | hl
  · rw [xi_one_sub]
    have hc : 0 < 1 + α * l := by positivity
    -- concavity of log with weights 1/c and αl/c
    have hw1 : 0 ≤ 1 / (1 + α * l) := by positivity
    have hw2 : 0 ≤ α * l / (1 + α * l) := by positivity
    have hw : 1 / (1 + α * l) + α * l / (1 + α * l) = 1 := by field_simp
    have hconc := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.mpr hD)
      (Set.mem_Ioi.mpr (show 0 < r / l by positivity)) hw1 hw2 hw
    simp only [smul_eq_mul] at hconc
    have harg : 1 / (1 + α * l) * (1 + α - α * r) + α * l / (1 + α * l) * (r / l)
        = (1 + α) / (1 + α * l) := by
      field_simp; ring
    rw [harg, Real.log_div hr.ne' hl.ne', Real.log_div hd.ne' hc.ne'] at hconc
    rw [Real.log_div hc.ne' hd.ne']
    have key : Real.log (1 + α - α * r) + α * l * (Real.log r - Real.log l)
        ≤ (1 + α * l) * (Real.log (1 + α) - Real.log (1 + α * l)) := by
      have := mul_le_mul_of_nonneg_left hconc hc.le
      have e1 : (1 + α * l) * (1 / (1 + α * l) * Real.log (1 + α - α * r)
          + α * l / (1 + α * l) * (Real.log r - Real.log l))
          = Real.log (1 + α - α * r) + α * l * (Real.log r - Real.log l) := by
        field_simp
      linarith
    nlinarith [key]
  · subst hl
    rw [xi_one_sub]
    simp only [mul_zero, zero_mul, add_zero, Real.log_zero, one_mul, zero_sub]
    rw [one_div, Real.log_inv, neg_neg]
    exact Real.log_le_log hD (by nlinarith)

lemma xi_one (α : ℝ) : xi α 1 = Real.log (1 + α) := by
  have := xi_one_sub α 0
  simp only [sub_zero, mul_zero, zero_mul, add_zero, Real.log_zero, one_mul, zero_sub] at this
  rw [this, one_div, Real.log_inv, neg_neg]

lemma xi_zero (α : ℝ) : xi α 0 = 0 := by
  unfold xi; simp

lemma xi_nonneg (α u : ℝ) (hα : 0 < α) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ xi α u := by
  have := xi_ge α (1 - u) 1 hα (by linarith) (by linarith) one_pos le_rfl
  simp only [mul_one, sub_self, sub_sub_cancel, Real.log_one, mul_zero, add_zero] at this
  simpa using this

/-- Convexity of `ξ(α, ·)` on `[0,1]`, from the representation as a supremum of affine maps. -/
lemma xi_convexOn (α : ℝ) (hα : 0 < α) : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (xi α) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  set z := a * x + b * y with hz
  have hz1 : z ≤ 1 := by nlinarith [hx.2, hy.2]
  rcases hz1.lt_or_eq with hz1 | hz1
  · set l := 1 - z with hl
    have hl0 : 0 < l := by linarith
    have hl1 : l ≤ 1 := by nlinarith [hx.1, hy.1]
    set r := l * (1 + α) / (1 + α * l) with hr
    have hc : 0 < 1 + α * l := by positivity
    have hr0 : 0 < r := by positivity
    have hr1 : r ≤ 1 := by rw [hr, div_le_one hc]; nlinarith
    have hrl : r * (1 + α * l) = l * (1 + α) := by rw [hr]; field_simp
    have heq := xi_eq_of α l r hα hl0 hr0 hrl
    have hzl : z = 1 - l := by rw [hl]; ring
    have gx := xi_ge α (1 - x) r hα (by linarith [hx.2]) (by linarith [hx.1]) hr0 hr1
    have gy := xi_ge α (1 - y) r hα (by linarith [hy.2]) (by linarith [hy.1]) hr0 hr1
    rw [sub_sub_cancel] at gx gy
    rw [hzl, heq]
    have hl' : l = a * (1 - x) + b * (1 - y) := by rw [hl, hz]; linear_combination (-1:ℝ) * hab
    rw [hl']
    have h1 := mul_le_mul_of_nonneg_left gx ha
    have h2 := mul_le_mul_of_nonneg_left gy hb
    have hsum : (a + b) * Real.log (1 + α - α * r) = Real.log (1 + α - α * r) := by
      rw [hab, one_mul]
    linarith
  · have p1 : 0 ≤ a * (1 - x) := mul_nonneg ha (sub_nonneg.2 hx.2)
    have p2 : 0 ≤ b * (1 - y) := mul_nonneg hb (sub_nonneg.2 hy.2)
    have p3 : a * (1 - x) + b * (1 - y) = 0 := by
      have : a * (1 - x) + b * (1 - y) = (a + b) - z := by rw [hz]; ring
      rw [this, hab, hz1]; ring
    have e1 : a * (1 - x) = 0 := by linarith
    have e2 : b * (1 - y) = 0 := by linarith
    have ex : a * xi α x = a * xi α 1 := by
      rcases mul_eq_zero.1 e1 with h | h
      · rw [h]; ring
      · rw [show x = 1 by linarith]
    have ey : b * xi α y = b * xi α 1 := by
      rcases mul_eq_zero.1 e2 with h | h
      · rw [h]; ring
      · rw [show y = 1 by linarith]
    rw [hz1, ex, ey, ← add_mul, hab, one_mul]

/-- Bernoulli-type inequality `1 + α - α q ≤ q^{-α}` for `q > 0`. -/
lemma bern (α q : ℝ) (hα : 0 < α) (hq : 0 < q) : 1 + α - α * q ≤ q ^ (-α) := by
  rw [Real.rpow_def_of_pos hq]
  have h1 := Real.add_one_le_exp (Real.log q * -α)
  have h2 := Real.log_le_sub_one_of_pos hq
  nlinarith

lemma xi_continuousOn (α : ℝ) (hα : 0 < α) : ContinuousOn (xi α) (Set.Icc (0:ℝ) 1) := by
  have e : xi α = fun u => α * ((1 - u) * Real.log (1 - u))
      - (α + 1 - α * u) * Real.log ((1 + α - α * u) / (1 + α)) := by
    funext u; unfold xi; ring
  rw [e]
  apply ContinuousOn.sub
  · exact (continuous_const.mul (Real.continuous_mul_log.comp
      (continuous_const.sub continuous_id))).continuousOn
  · apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.log (by fun_prop)
    intro u hu
    have : 0 < 1 + α - α * u := by nlinarith [hu.2]
    positivity

end TalConvP

namespace TalConvP

open TalagrandConc.ConvexHull
open scoped ENNReal

/-- generalised `f_α`: infimum of `∑ ξ` over the convex hull of a pattern set. -/
noncomputable def gW (α : ℝ) {N : ℕ} (S : Set (Fin N → ℝ)) : ℝ≥0∞ :=
  ⨅ s ∈ convexHull ℝ S, ENNReal.ofReal (∑ i, xi α (s i))

noncomputable def Ex (v : ℝ≥0∞) : ℝ≥0∞ := EReal.exp (v : EReal)

def Is01 {N : ℕ} (S : Set (Fin N → ℝ)) : Prop := ∀ s ∈ S, ∀ i, s i = 0 ∨ s i = 1

lemma hull01 {N : ℕ} {S : Set (Fin N → ℝ)} (hS : Is01 S) {t : Fin N → ℝ}
    (ht : t ∈ convexHull ℝ S) (i : Fin N) : t i ∈ Set.Icc (0:ℝ) 1 := by
  have hsub : convexHull ℝ S ⊆ Set.univ.pi (fun _ : Fin N => Set.Icc (0:ℝ) 1) := by
    apply convexHull_min
    · intro s hs j _
      rcases hS s hs j with h | h <;> rw [h] <;> simp
    · exact convex_pi (fun _ _ => convex_Icc 0 1)
  exact hsub ht i (Set.mem_univ i)

noncomputable def vec {N : ℕ} (b : Fin N → Bool) : Fin N → ℝ := fun i => if b i then 1 else 0

lemma is01_sub_range {N : ℕ} {S : Set (Fin N → ℝ)} (hS : Is01 S) : S ⊆ Set.range (@vec N) := by
  intro s hs
  refine ⟨fun i => decide (s i = 1), ?_⟩
  funext i
  unfold vec
  rcases hS s hs i with h | h <;> simp [h]

lemma is01_finite {N : ℕ} {S : Set (Fin N → ℝ)} (hS : Is01 S) : S.Finite :=
  (Set.finite_range _).subset (is01_sub_range hS)

lemma F_continuousOn {N : ℕ} (α : ℝ) (hα : 0 < α) {S : Set (Fin N → ℝ)} (hS : Is01 S) :
    ContinuousOn (fun t : Fin N → ℝ => ∑ i, xi α (t i)) (convexHull ℝ S) := by
  apply continuousOn_finsetSum
  intro i _
  exact (xi_continuousOn α hα).comp (continuous_apply i).continuousOn
    (fun t ht => hull01 hS ht i)

lemma F_nonneg {N : ℕ} (α : ℝ) (hα : 0 < α) {S : Set (Fin N → ℝ)} (hS : Is01 S)
    {t : Fin N → ℝ} (ht : t ∈ convexHull ℝ S) : 0 ≤ ∑ i, xi α (t i) :=
  Finset.sum_nonneg (fun i _ => xi_nonneg α (t i) hα (hull01 hS ht i).1 (hull01 hS ht i).2)

lemma gW_attain {N : ℕ} (α : ℝ) (hα : 0 < α) {S : Set (Fin N → ℝ)} (hS : Is01 S)
    (hne : (convexHull ℝ S).Nonempty) :
    ∃ t ∈ convexHull ℝ S, gW α S = ENNReal.ofReal (∑ i, xi α (t i)) := by
  obtain ⟨t, ht, hmin⟩ := ((is01_finite hS).isCompact_convexHull ℝ).exists_isMinOn hne
    (F_continuousOn α hα hS)
  refine ⟨t, ht, le_antisymm (iInf₂_le t ht) (le_iInf₂ fun t' ht' => ?_)⟩
  exact ENNReal.ofReal_le_ofReal (hmin ht')

lemma gW_empty {N : ℕ} (α : ℝ) {S : Set (Fin N → ℝ)} (h : ¬ (convexHull ℝ S).Nonempty) :
    gW α S = ⊤ := by
  rw [Set.not_nonempty_iff_eq_empty] at h
  unfold gW; rw [h]; simp

lemma gW_mono {N : ℕ} (α : ℝ) {S T : Set (Fin N → ℝ)} (h : S ⊆ T) : gW α T ≤ gW α S := by
  unfold gW
  exact le_iInf₂ fun t ht => iInf₂_le t (convexHull_mono h ht)

lemma Ex_ofReal {t : ℝ} (ht : 0 ≤ t) : Ex (ENNReal.ofReal t) = ENNReal.ofReal (Real.exp t) := by
  unfold Ex
  rw [EReal.coe_ennreal_ofReal, max_eq_left ht, EReal.exp_coe]

lemma Ex_top : Ex ⊤ = ⊤ := by
  unfold Ex; simp

lemma Ex_mono {a b : ℝ≥0∞} (h : a ≤ b) : Ex a ≤ Ex b := by
  unfold Ex
  exact EReal.exp_monotone (EReal.coe_ennreal_le_coe_ennreal_iff.2 h)

lemma Ex_ne_zero (a : ℝ≥0∞) : Ex a ≠ 0 := by
  have h1 : Ex 0 ≤ Ex a := Ex_mono (by simp)
  have h0 : Ex 0 = 1 := by
    rw [← ENNReal.ofReal_zero, Ex_ofReal le_rfl, Real.exp_zero, ENNReal.ofReal_one]
  intro h; rw [h, h0] at h1; exact absurd h1 (by simp)

/-- the affine embedding `t ↦ (c, t)`. -/
noncomputable def consA {N : ℕ} (c : ℝ) : (Fin N → ℝ) →ᵃ[ℝ] (Fin (N + 1) → ℝ) where
  toFun t := Fin.cons c t
  linear :=
    { toFun := fun t => Fin.cons 0 t
      map_add' := by
        intro a b; funext i; refine Fin.cases ?_ ?_ i <;> simp
      map_smul' := by
        intro m a; funext i; refine Fin.cases ?_ ?_ i <;> simp }
  map_vadd' := by
    intro p v; funext i; refine Fin.cases ?_ ?_ i <;> simp

lemma consA_apply {N : ℕ} (c : ℝ) (t : Fin N → ℝ) : consA c t = Fin.cons c t := rfl

lemma cons_mem_hull {N : ℕ} (c : ℝ) {S : Set (Fin N → ℝ)} {W : Set (Fin (N + 1) → ℝ)}
    (h : ∀ s ∈ S, (Fin.cons c s : Fin (N + 1) → ℝ) ∈ W) {t : Fin N → ℝ}
    (ht : t ∈ convexHull ℝ S) : (Fin.cons c t : Fin (N + 1) → ℝ) ∈ convexHull ℝ W := by
  have h1 : consA c t ∈ (consA c) '' convexHull ℝ S := ⟨t, ht, rfl⟩
  rw [AffineMap.image_convexHull] at h1
  refine convexHull_mono ?_ h1
  rintro _ ⟨s, hs, rfl⟩
  exact h s hs

lemma hull_step_pos {N : ℕ} (α : ℝ) (hα : 0 < α) (W : Set (Fin (N + 1) → ℝ))
    (S1 S2 : Set (Fin N → ℝ)) (h01 : Is01 S1) (h02 : Is01 S2) (hsub : S1 ⊆ S2)
    (h1 : ∀ s ∈ S1, (Fin.cons 0 s : Fin (N + 1) → ℝ) ∈ W)
    (h2 : ∀ s ∈ S2, (Fin.cons 1 s : Fin (N + 1) → ℝ) ∈ W)
    (l : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 1) :
    Ex (gW α W) ≤ ENNReal.ofReal (Real.exp (xi α (1 - l))) * Ex (gW α S1) ^ l
      * Ex (gW α S2) ^ (1 - l) := by
  by_cases hne : (convexHull ℝ S1).Nonempty
  · obtain ⟨t1, ht1, e1⟩ := gW_attain α hα h01 hne
    obtain ⟨t2, ht2, e2⟩ := gW_attain α hα h02 (hne.mono (convexHull_mono hsub))
    set F1 := ∑ i, xi α (t1 i)
    set F2 := ∑ i, xi α (t2 i)
    have hF1 : 0 ≤ F1 := F_nonneg α hα h01 ht1
    have hF2 : 0 ≤ F2 := F_nonneg α hα h02 ht2
    have hxl : 0 ≤ xi α (1 - l) := xi_nonneg α _ hα (by linarith) (by linarith)
    set p : Fin (N + 1) → ℝ := l • (Fin.cons 0 t1 : Fin (N + 1) → ℝ)
      + (1 - l) • (Fin.cons 1 t2 : Fin (N + 1) → ℝ) with hp
    have hpmem : p ∈ convexHull ℝ W :=
      (convex_convexHull ℝ W) (cons_mem_hull 0 h1 ht1) (cons_mem_hull 1 h2 ht2) hl0.le
        (by linarith) (by ring)
    have hFp : ∑ i, xi α (p i) ≤ xi α (1 - l) + l * F1 + (1 - l) * F2 := by
      rw [Fin.sum_univ_succ]
      have hp0 : p 0 = 1 - l := by simp [hp]
      have hps : ∀ i : Fin N, p i.succ = l * t1 i + (1 - l) * t2 i := by
        intro i; simp [hp]
      rw [hp0]
      have hconv : ∀ i : Fin N, xi α (p i.succ) ≤ l * xi α (t1 i) + (1 - l) * xi α (t2 i) := by
        intro i
        rw [hps i]
        have := (xi_convexOn α hα).2 (hull01 h01 ht1 i) (hull01 h02 ht2 i) hl0.le
          (by linarith : (0:ℝ) ≤ 1 - l) (by ring)
        simpa [smul_eq_mul] using this
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hconv i)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
      linarith
    have hR : 0 ≤ xi α (1 - l) + l * F1 + (1 - l) * F2 := by
      have : 0 ≤ l * F1 := mul_nonneg hl0.le hF1
      have : 0 ≤ (1 - l) * F2 := mul_nonneg (by linarith) hF2
      linarith
    calc Ex (gW α W) ≤ Ex (ENNReal.ofReal (xi α (1 - l) + l * F1 + (1 - l) * F2)) := by
          apply Ex_mono
          exact (iInf₂_le p hpmem).trans (ENNReal.ofReal_le_ofReal hFp)
      _ = ENNReal.ofReal (Real.exp (xi α (1 - l))) * ENNReal.ofReal (Real.exp F1) ^ l
            * ENNReal.ofReal (Real.exp F2) ^ (1 - l) := by
          rw [Ex_ofReal hR, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
            ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← Real.exp_mul, ← Real.exp_mul,
            ← Real.exp_add, ← Real.exp_add]
          congr 2; ring
      _ = _ := by rw [e1, e2, Ex_ofReal hF1, Ex_ofReal hF2]
  · rw [gW_empty α hne, Ex_top, ENNReal.top_rpow_of_pos hl0,
      ENNReal.mul_top (by simp [Real.exp_pos]),
      ENNReal.top_mul (by
        intro h
        rcases (ENNReal.rpow_eq_zero_iff).1 h with ⟨h0, _⟩ | ⟨_, h3⟩
        · exact Ex_ne_zero _ h0
        · linarith)]
    exact le_top

lemma hull_step_zero {N : ℕ} (α : ℝ) (hα : 0 < α) (W : Set (Fin (N + 1) → ℝ))
    (S2 : Set (Fin N → ℝ)) (h02 : Is01 S2)
    (h2 : ∀ s ∈ S2, (Fin.cons 1 s : Fin (N + 1) → ℝ) ∈ W) :
    Ex (gW α W) ≤ ENNReal.ofReal (1 + α) * Ex (gW α S2) := by
  by_cases hne : (convexHull ℝ S2).Nonempty
  · obtain ⟨t2, ht2, e2⟩ := gW_attain α hα h02 hne
    set F2 := ∑ i, xi α (t2 i)
    have hF2 : 0 ≤ F2 := F_nonneg α hα h02 ht2
    have hpmem := cons_mem_hull 1 h2 ht2
    have hFp : ∑ i, xi α ((Fin.cons 1 t2 : Fin (N + 1) → ℝ) i) = Real.log (1 + α) + F2 := by
      rw [Fin.sum_univ_succ]; simp [xi_one, F2]
    have hlog : 0 ≤ Real.log (1 + α) := Real.log_nonneg (by linarith)
    calc Ex (gW α W) ≤ Ex (ENNReal.ofReal (Real.log (1 + α) + F2)) := by
          apply Ex_mono
          exact (iInf₂_le _ hpmem).trans (le_of_eq (by rw [hFp]))
      _ = _ := by
          rw [Ex_ofReal (by linarith), e2, Ex_ofReal hF2, Real.exp_add,
            Real.exp_log (by linarith), ENNReal.ofReal_mul (by linarith)]
  · rw [gW_empty α hne, Ex_top, ENNReal.mul_top (by simp; linarith)]
    exact le_top

end TalConvP

namespace TalConvP

open TalagrandConc.ConvexHull MeasureTheory
open scoped ENNReal

universe u

structure Fam {Ω : Type u} {N : ℕ} (W : (Fin N → Ω) → Set (Fin N → ℝ))
    [MeasurableSpace Ω] : Prop where
  h01 : ∀ x, Is01 (W x)
  meas : ∀ s, MeasurableSet {x | s ∈ W x}
  cyl : ∀ x x' s, s ∈ W x → (∀ i, s i = 0 → x i = x' i) → s ∈ W x'
  mono : ∀ x s s', s ∈ W x → (∀ i, s' i = 0 ∨ s' i = 1) → s ≤ s' → s' ∈ W x

lemma meas_of_fam {Ω : Type u} [MeasurableSpace Ω] {N : ℕ} {W : (Fin N → Ω) → Set (Fin N → ℝ)}
    (h01 : ∀ x, Is01 (W x)) (hm : ∀ s, MeasurableSet {x | s ∈ W x})
    (Φ : Set (Fin N → ℝ) → ℝ≥0∞) : Measurable (fun x => Φ (W x)) := by
  classical
  let code : (Fin N → Ω) → ((Fin N → Bool) → Bool) := fun x b => decide (vec b ∈ W x)
  let Φ' : ((Fin N → Bool) → Bool) → ℝ≥0∞ := fun c => Φ {s | ∃ b, c b = true ∧ vec b = s}
  have hcode : Measurable code := by
    apply measurable_pi_lambda
    intro b
    apply measurable_to_bool
    have : (fun x => code x b) ⁻¹' {true} = {x | vec b ∈ W x} := by
      ext x; simp [code]
    rw [this]; exact hm _
  have heq : (fun x => Φ (W x)) = Φ' ∘ code := by
    funext x
    simp only [Function.comp, Φ', code]
    congr 1
    ext s
    constructor
    · intro hs
      obtain ⟨b, rfl⟩ := is01_sub_range (h01 x) hs
      exact ⟨b, by simpa using hs, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      simpa using hb
  rw [heq]
  exact (measurable_of_countable Φ').comp hcode

lemma outer_bound {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (α : ℝ) (hα : 0 < α) (A : ℝ) (hA : 0 < A) (b : Ω → ℝ) (hb : Measurable b)
    (hb0 : ∀ ω, 0 ≤ b ω) (hbA : ∀ ω, b ω ≤ A) :
    ∫⁻ ω, ENNReal.ofReal (A ^ (-α) * (1 + α - α * (b ω / A))) ∂μ
      ≤ (∫⁻ ω, ENNReal.ofReal (b ω) ∂μ) ^ (-α) := by
  set K := A ^ (-α) with hK
  have hK0 : 0 < K := Real.rpow_pos_of_pos hA _
  set k := K * α / A with hk
  have hk0 : 0 ≤ k := by positivity
  have hX : ∀ ω, ENNReal.ofReal (K * (1 + α - α * (b ω / A))) + ENNReal.ofReal (k * b ω)
      = ENNReal.ofReal (K * (1 + α)) := by
    intro ω
    have h1 : b ω / A ≤ 1 := (div_le_one hA).2 (hbA ω)
    have h2 : 0 ≤ K * (1 + α - α * (b ω / A)) := by
      apply mul_nonneg hK0.le; nlinarith
    rw [← ENNReal.ofReal_add h2 (mul_nonneg hk0 (hb0 ω))]
    congr 1; rw [hk]; field_simp; ring
  have hYm : Measurable fun ω => ENNReal.ofReal (k * b ω) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hb)
  have hsum := lintegral_add_right (μ := μ) (fun ω => ENNReal.ofReal (K * (1 + α - α * (b ω / A))))
    hYm
  simp only [hX, lintegral_const, measure_univ, mul_one] at hsum
  have hY : ∫⁻ ω, ENNReal.ofReal (k * b ω) ∂μ = ENNReal.ofReal k * ∫⁻ ω, ENNReal.ofReal (b ω) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1; funext ω; rw [ENNReal.ofReal_mul hk0]
  set pD := ∫⁻ ω, ENNReal.ofReal (b ω) ∂μ with hpD
  have hpD_fin : pD ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := A))
    calc pD ≤ ∫⁻ _ : Ω, ENNReal.ofReal A ∂μ := lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (hbA ω))
      _ = ENNReal.ofReal A := by simp
  set p := pD.toReal with hp
  have hpD' : pD = ENNReal.ofReal p := (ENNReal.ofReal_toReal hpD_fin).symm
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  rw [hY, hpD', ← ENNReal.ofReal_mul hk0] at hsum
  have hX' : ∫⁻ ω, ENNReal.ofReal (K * (1 + α - α * (b ω / A))) ∂μ
      = ENNReal.ofReal (K * (1 + α) - k * p) := by
    rw [ENNReal.ofReal_sub _ (mul_nonneg hk0 hp0)]
    exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top hsum.symm
  rw [hX', hpD']
  rcases hp0.lt_or_eq with hpp | hpp
  · rw [ENNReal.ofReal_rpow_of_pos hpp]
    apply ENNReal.ofReal_le_ofReal
    have hq : 0 < p / A := div_pos hpp hA
    have hb := bern α (p / A) hα hq
    have e1 : K * (1 + α) - k * p = K * (1 + α - α * (p / A)) := by rw [hk]; field_simp; try ring
    have e2 : K * (p / A) ^ (-α) = p ^ (-α) := by
      rw [Real.div_rpow hpp.le hA.le, hK]; try field_simp
    rw [e1, ← e2]
    exact mul_le_mul_of_nonneg_left hb hK0.le
  · rw [← hpp, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith)]
    exact le_top

lemma inner_bound {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) (α : ℝ) (hα : 0 < α)
    (G E1 E2 : Y → ℝ≥0∞) (hE1 : AEMeasurable E1 ν) (hE2 : AEMeasurable E2 ν)
    (m1 m2 : ℝ≥0∞) (hm1 : m1 ≠ ⊤) (hm2 : m2 ≠ ⊤) (hm2pos : m2 ≠ 0) (h12 : m1 ≤ m2)
    (hI1 : ∫⁻ y, E1 y ∂ν ≤ m1 ^ (-α)) (hI2 : ∫⁻ y, E2 y ∂ν ≤ m2 ^ (-α))
    (hpos : ∀ l : ℝ, 0 < l → l ≤ 1 → ∀ y,
      G y ≤ ENNReal.ofReal (Real.exp (xi α (1 - l))) * E1 y ^ l * E2 y ^ (1 - l))
    (hzero : ∀ y, G y ≤ ENNReal.ofReal (1 + α) * E2 y) :
    ∫⁻ y, G y ∂ν ≤ ENNReal.ofReal (m2.toReal ^ (-α) * (1 + α - α * (m1.toReal / m2.toReal))) := by
  set A := m2.toReal with hAdef
  set B := m1.toReal with hBdef
  have hA : 0 < A := ENNReal.toReal_pos hm2pos hm2
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  have hBA : B ≤ A := ENNReal.toReal_mono hm2 h12
  have em2 : m2 = ENNReal.ofReal A := (ENNReal.ofReal_toReal hm2).symm
  have em1 : m1 = ENNReal.ofReal B := (ENNReal.ofReal_toReal hm1).symm
  rcases hB0.lt_or_eq with hB | hB
  · set r := B / A with hr
    have hr0 : 0 < r := div_pos hB hA
    have hr1 : r ≤ 1 := (div_le_one hA).2 hBA
    set D := 1 + α - α * r with hD
    have hD0 : 0 < D := by rw [hD]; nlinarith
    set l := r / D with hl
    have hl0 : 0 < l := div_pos hr0 hD0
    have hl1 : l ≤ 1 := by rw [hl, div_le_one hD0, hD]; nlinarith
    have hrl : r * (1 + α * l) = l * (1 + α) := by rw [hl]; field_simp; rw [hD]; ring
    have hxi := xi_eq_of α l r hα hl0 hr0 hrl
    calc ∫⁻ y, G y ∂ν ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (xi α (1 - l))) * (E1 y ^ l * E2 y ^ (1 - l)) ∂ν :=
          lintegral_mono (fun y => by rw [← mul_assoc]; exact hpos l hl0 hl1 y)
      _ = ENNReal.ofReal (Real.exp (xi α (1 - l))) * ∫⁻ y, E1 y ^ l * E2 y ^ (1 - l) ∂ν :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp (xi α (1 - l))) * ((∫⁻ y, E1 y ∂ν) ^ l * (∫⁻ y, E2 y ∂ν) ^ (1 - l)) := by
          gcongr
          exact ENNReal.lintegral_mul_norm_pow_le hE1 hE2 hl0.le (by linarith) (by ring)
      _ ≤ ENNReal.ofReal (Real.exp (xi α (1 - l))) * ((m1 ^ (-α)) ^ l * (m2 ^ (-α)) ^ (1 - l)) := by
          gcongr
      _ = ENNReal.ofReal (A ^ (-α) * (1 + α - α * (B / A))) := by
          rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, em1, em2,
            ENNReal.ofReal_rpow_of_pos hB, ENNReal.ofReal_rpow_of_pos hA,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [← hr, ← hD]
          rw [Real.rpow_def_of_pos hB, Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hA,
            ← Real.exp_log hD0, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hxi,
            hr, Real.log_div hB.ne' hA.ne']
          congr 1; ring
  · have hm1z : m1 = 0 := by rw [em1, ← hB, ENNReal.ofReal_zero]
    calc ∫⁻ y, G y ∂ν ≤ ∫⁻ y, ENNReal.ofReal (1 + α) * E2 y ∂ν := lintegral_mono hzero
      _ = ENNReal.ofReal (1 + α) * ∫⁻ y, E2 y ∂ν := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (1 + α) * m2 ^ (-α) := by gcongr
      _ = _ := by
          rw [em2, ENNReal.ofReal_rpow_of_pos hA, ← ENNReal.ofReal_mul (by linarith),
            ← hB]
          congr 1; ring

end TalConvP

namespace TalConvP

open TalagrandConc.ConvexHull MeasureTheory
open scoped ENNReal

universe v

lemma cons00 {N : ℕ} : (Fin.cons (0:ℝ) (0 : Fin N → ℝ) : Fin (N + 1) → ℝ) = 0 := by
  funext j; cases j using Fin.cases <;> simp

lemma cons_mp {Ω : Type v} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) :
    MeasurePreserving (fun z : Ω × (Fin N → Ω) => (Fin.cons z.1 z.2 : Fin (N + 1) → Ω))
      (μ.prod (Measure.pi fun _ : Fin N => μ)) (Measure.pi fun _ : Fin (N + 1) => μ) ∧
    MeasurableEmbedding (fun z : Ω × (Fin N → Ω) => (Fin.cons z.1 z.2 : Fin (N + 1) → Ω)) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => μ) 0).symm
  have e : ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Ω) 0).symm
      = (fun z : Ω × (Fin N → Ω) => (Fin.cons z.1 z.2 : Fin (N + 1) → Ω)) := by
    funext z
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
    simp [Fin.insertNthEquiv, Fin.insertNth_zero']
  refine ⟨?_, ?_⟩
  · rw [← e]; exact h
  · rw [← e]; exact MeasurableEquiv.measurableEmbedding _

lemma fam_W1 {Ω : Type v} [MeasurableSpace Ω] {N : ℕ} {W : (Fin (N + 1) → Ω) → Set (Fin (N + 1) → ℝ)}
    (hW : Fam W) (c : ℝ) (hc : c = 0 ∨ c = 1) (ω : Ω) (hcm : Measurable (fun y : Fin N → Ω => (Fin.cons ω y : Fin (N + 1) → Ω))) :
    Fam (fun y : Fin N → Ω => {s : Fin N → ℝ | (Fin.cons c s : Fin (N + 1) → ℝ) ∈ W (Fin.cons ω y)}) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y s hs i
    have := hW.h01 _ _ hs i.succ
    simpa using this
  · intro s
    exact (hW.meas _).preimage hcm
  · intro y y' s hs h
    apply hW.cyl _ _ _ hs
    intro j
    cases j using Fin.cases with
    | zero => intro _; simp
    | succ i => intro hi; simp only [Fin.cons_succ] at hi ⊢; exact h i hi
  · intro y s s' hs h01' hle
    apply hW.mono _ _ _ hs
    · intro j
      cases j using Fin.cases with
      | zero => simpa using hc
      | succ i => simpa using h01' i
    · intro j
      cases j using Fin.cases with
      | zero => simp
      | succ i => simpa using hle i

theorem G {Ω : Type v} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (α : ℝ) (hα : 0 < α) : ∀ (N : ℕ) (W : (Fin N → Ω) → Set (Fin N → ℝ)), Fam W →
    ∫⁻ x, Ex (gW α (W x)) ∂(Measure.pi fun _ : Fin N => μ)
      ≤ (Measure.pi (fun _ : Fin N => μ) {x | (0 : Fin N → ℝ) ∈ W x}) ^ (-α) := by
  intro N
  induction N with
  | zero =>
    intro W hW
    by_cases hD : ∃ x0, (0 : Fin 0 → ℝ) ∈ W x0
    · obtain ⟨x0, hx0⟩ := hD
      have hall : ∀ x, (0 : Fin 0 → ℝ) ∈ W x := by
        intro x; rw [Subsingleton.elim x x0]; exact hx0
      have hset : {x | (0 : Fin 0 → ℝ) ∈ W x} = Set.univ := Set.eq_univ_of_forall hall
      rw [hset, measure_univ, ENNReal.one_rpow]
      have hle : ∀ x, Ex (gW α (W x)) ≤ 1 := by
        intro x
        have h0 : gW α (W x) = 0 := by
          apply le_antisymm _ (by simp)
          refine (iInf₂_le (0 : Fin 0 → ℝ) (subset_convexHull ℝ _ (hall x))).trans ?_
          simp
        rw [h0, ← ENNReal.ofReal_zero, Ex_ofReal le_rfl, Real.exp_zero, ENNReal.ofReal_one]
      calc ∫⁻ x, Ex (gW α (W x)) ∂(Measure.pi fun _ : Fin 0 => μ)
          ≤ ∫⁻ _, 1 ∂(Measure.pi fun _ : Fin 0 => μ) := lintegral_mono hle
        _ = 1 := by simp
    · push Not at hD
      have hset : {x | (0 : Fin 0 → ℝ) ∈ W x} = ∅ := Set.eq_empty_of_forall_notMem hD
      rw [hset, measure_empty, ENNReal.zero_rpow_of_neg (by linarith)]
      exact le_top
  | succ N ih =>
    intro W hW
    obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
    set P := Measure.pi fun _ : Fin N => μ with hP
    obtain ⟨hmp, hemb⟩ := cons_mp μ N
    have hcm : ∀ ω : Ω, Measurable (fun y : Fin N → Ω => (Fin.cons ω y : Fin (N + 1) → Ω)) :=
      fun ω => hmp.measurable.comp measurable_prodMk_left
    set W1 : Ω → (Fin N → Ω) → Set (Fin N → ℝ) :=
      fun ω y => {s | (Fin.cons 0 s : Fin (N + 1) → ℝ) ∈ W (Fin.cons ω y)} with hW1
    set W2 : (Fin N → Ω) → Set (Fin N → ℝ) :=
      fun y => {s | (Fin.cons 1 s : Fin (N + 1) → ℝ) ∈ W (Fin.cons ω₀ y)} with hW2
    have f1 : ∀ ω, Fam (W1 ω) := fun ω => fam_W1 hW 0 (Or.inl rfl) ω (hcm ω)
    have f2 : Fam W2 := fam_W1 hW 1 (Or.inr rfl) ω₀ (hcm ω₀)
    have link : ∀ ω y s, s ∈ W2 y → (Fin.cons 1 s : Fin (N + 1) → ℝ) ∈ W (Fin.cons ω y) := by
      intro ω y s hs
      apply hW.cyl _ _ _ hs
      intro j
      cases j using Fin.cases with
      | zero => intro h; simp at h
      | succ i => intro _; simp
    have sub : ∀ ω y, W1 ω y ⊆ W2 y := by
      intro ω y s hs
      have h01s := (f1 ω).h01 y s hs
      have hm : (Fin.cons 1 s : Fin (N + 1) → ℝ) ∈ W (Fin.cons ω y) := by
        apply hW.mono _ _ _ hs
        · intro j
          cases j using Fin.cases with
          | zero => simp
          | succ i => simpa using h01s i
        · intro j
          cases j using Fin.cases with
          | zero => simp
          | succ i => simp
      show (Fin.cons 1 s : Fin (N + 1) → ℝ) ∈ W (Fin.cons ω₀ y)
      apply hW.cyl _ _ _ hm
      intro j
      cases j using Fin.cases with
      | zero => intro h; simp at h
      | succ i => intro _; simp
    set D := {x : Fin (N + 1) → Ω | (0 : Fin (N + 1) → ℝ) ∈ W x} with hDdef
    have hD : MeasurableSet D := hW.meas 0
    have hpre : MeasurableSet ((fun z : Ω × (Fin N → Ω) => (Fin.cons z.1 z.2 : Fin (N + 1) → Ω)) ⁻¹' D) :=
      hD.preimage hmp.measurable
    have hPD : (Measure.pi fun _ : Fin (N + 1) => μ) D
        = ∫⁻ ω, P {y | (0 : Fin N → ℝ) ∈ W1 ω y} ∂μ := by
      rw [← hmp.measure_preimage hD.nullMeasurableSet, Measure.prod_apply hpre]
      congr 1; funext ω; congr 1
      ext y; simp [hW1, hDdef, cons00]
    have hFm : Measurable (fun x : Fin (N + 1) → Ω => Ex (gW α (W x))) :=
      meas_of_fam hW.h01 hW.meas (fun S => Ex (gW α S))
    have hint : ∫⁻ x, Ex (gW α (W x)) ∂(Measure.pi fun _ : Fin (N + 1) => μ)
        = ∫⁻ ω, ∫⁻ y, Ex (gW α (W (Fin.cons ω y))) ∂P ∂μ := by
      rw [← hmp.lintegral_comp_emb hemb]
      exact lintegral_prod _ (hFm.comp hmp.measurable).aemeasurable
    have hD1m : Measurable (fun ω => P {y | (0 : Fin N → ℝ) ∈ W1 ω y}) := by
      have := measurable_measure_prodMk_left (ν := P) hpre
      convert this using 2 with ω
      congr 1; ext y; simp [hW1, hDdef, cons00]
    have hle12 : ∀ ω, P {y | (0 : Fin N → ℝ) ∈ W1 ω y} ≤ P {y | (0 : Fin N → ℝ) ∈ W2 y} :=
      fun ω => measure_mono (fun y hy => sub ω y hy)
    by_cases ha : P {y | (0 : Fin N → ℝ) ∈ W2 y} = 0
    · have h0 : (Measure.pi fun _ : Fin (N + 1) => μ) D = 0 := by
        rw [hPD]
        apply le_antisymm _ (by simp)
        calc ∫⁻ ω, P {y | (0 : Fin N → ℝ) ∈ W1 ω y} ∂μ ≤ ∫⁻ _ : Ω, 0 ∂μ :=
              lintegral_mono (fun ω => (hle12 ω).trans (le_of_eq ha))
          _ = 0 := by simp
      rw [h0, ENNReal.zero_rpow_of_neg (by linarith)]
      exact le_top
    · set a := P {y | (0 : Fin N → ℝ) ∈ W2 y} with hadef
      have ha_top : a ≠ ⊤ := measure_ne_top _ _
      have hA : 0 < a.toReal := ENNReal.toReal_pos ha ha_top
      rw [hint]
      calc ∫⁻ ω, ∫⁻ y, Ex (gW α (W (Fin.cons ω y))) ∂P ∂μ
          ≤ ∫⁻ ω, ENNReal.ofReal (a.toReal ^ (-α) * (1 + α - α *
              ((P {y | (0 : Fin N → ℝ) ∈ W1 ω y}).toReal / a.toReal))) ∂μ := by
            apply lintegral_mono
            intro ω
            apply inner_bound P α hα _ (fun y => Ex (gW α (W1 ω y))) (fun y => Ex (gW α (W2 y)))
              ((meas_of_fam (f1 ω).h01 (f1 ω).meas (fun S => Ex (gW α S))).aemeasurable)
              ((meas_of_fam f2.h01 f2.meas (fun S => Ex (gW α S))).aemeasurable)
              _ _ (measure_ne_top _ _) ha_top ha (hle12 ω) (ih _ (f1 ω)) (ih _ f2)
            · intro l hl0 hl1 y
              exact hull_step_pos α hα (W (Fin.cons ω y)) (W1 ω y) (W2 y) ((f1 ω).h01 y) (f2.h01 y)
                (sub ω y) (fun s hs => hs) (fun s hs => link ω y s hs) l hl0 hl1
            · intro y
              exact hull_step_zero α hα (W (Fin.cons ω y)) (W2 y) (f2.h01 y)
                (fun s hs => link ω y s hs)
        _ ≤ (∫⁻ ω, ENNReal.ofReal ((P {y | (0 : Fin N → ℝ) ∈ W1 ω y}).toReal) ∂μ) ^ (-α) :=
            outer_bound μ α hα a.toReal hA _ hD1m.ennreal_toReal (fun ω => ENNReal.toReal_nonneg)
              (fun ω => ENNReal.toReal_mono ha_top (hle12 ω))
        _ = _ := by
            rw [hPD]
            congr 1
            apply lintegral_congr
            intro ω
            exact ENNReal.ofReal_toReal (measure_ne_top _ _)

end TalConvP

namespace TalConvP

open TalagrandConc.ConvexHull MeasureTheory
open scoped ENNReal

universe w

def mrg {Ω : Type w} {N : ℕ} (b : Fin N → Bool) (x z : Fin N → Ω) : Fin N → Ω :=
  fun i => if b i then z i else x i

lemma mrg_meas {Ω : Type w} [MeasurableSpace Ω] {N : ℕ} (b : Fin N → Bool) :
    Measurable (fun p : (Fin N → Ω) × (Fin N → Ω) => mrg b p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  by_cases hb : b i
  · simp only [mrg, hb, if_true]; exact (measurable_pi_apply i).comp measurable_snd
  · simp only [mrg, hb]; exact (measurable_pi_apply i).comp measurable_fst

lemma mrg_cyl {Ω : Type w} {N : ℕ} (b : Fin N → Bool) {x x' : Fin N → Ω}
    (h : ∀ i, b i = false → x i = x' i) (z : Fin N → Ω) : mrg b x z = mrg b x' z := by
  funext i; unfold mrg; by_cases hb : b i
  · simp [hb]
  · simp only [hb]; exact h i (by simpa using hb)

lemma mrg_map {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ}
    (b : Fin N → Bool) :
    Measure.map (fun p : (Fin N → Ω) × (Fin N → Ω) => mrg b p.1 p.2)
      ((Measure.pi fun _ : Fin N => μ).prod (Measure.pi fun _ : Fin N => μ))
      = Measure.pi fun _ : Fin N => μ := by
  classical
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (mrg_meas b) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (Fin N → Ω) × (Fin N → Ω) => mrg b p.1 p.2) ⁻¹' Set.univ.pi s
      = Set.univ.pi (fun i => if b i then Set.univ else s i)
        ×ˢ Set.univ.pi (fun i => if b i then s i else Set.univ) := by
    ext ⟨x, z⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := h i; by_cases hb : b i <;> simp_all [mrg]
      · have := h i; by_cases hb : b i <;> simp_all [mrg]
    · rintro ⟨h1, h2⟩ i
      have := h1 i; have := h2 i
      by_cases hb : b i <;> simp_all [mrg]
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hb : b i <;> simp [hb]

/-- the measurable kernel set `S_b`. -/
def Sb {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) {N : ℕ} (A : Set (Fin N → Ω))
    (b : Fin N → Bool) : Set (Fin N → Ω) :=
  {x | 0 < (Measure.pi fun _ : Fin N => μ) {z | mrg b x z ∈ A}}

lemma Sb_meas {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ}
    {A : Set (Fin N → Ω)} (hA : MeasurableSet A) (b : Fin N → Bool) :
    MeasurableSet (Sb μ A b) := by
  have hM : MeasurableSet {p : (Fin N → Ω) × (Fin N → Ω) | mrg b p.1 p.2 ∈ A} :=
    hA.preimage (mrg_meas b)
  have := measurable_measure_prodMk_left (ν := Measure.pi fun _ : Fin N => μ) hM
  exact measurableSet_lt measurable_const this

lemma Sb_cyl {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) {N : ℕ}
    (A : Set (Fin N → Ω)) (b : Fin N → Bool) {x x' : Fin N → Ω}
    (h : ∀ i, b i = false → x i = x' i) (hx : x ∈ Sb μ A b) : x' ∈ Sb μ A b := by
  unfold Sb at hx ⊢
  simp only [Set.mem_setOf_eq] at hx ⊢
  have : {z | mrg b x z ∈ A} = {z | mrg b x' z ∈ A} := by
    ext z; simp [mrg_cyl b h z]
  rwa [← this]

lemma Sb_sub {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) {N : ℕ}
    (A : Set (Fin N → Ω)) (b : Fin N → Bool) {x : Fin N → Ω} (hx : x ∈ Sb μ A b) :
    vec b ∈ U A x := by
  unfold Sb at hx
  simp only [Set.mem_setOf_eq] at hx
  obtain ⟨z, hz⟩ := nonempty_of_measure_ne_zero hx.ne'
  refine ⟨fun i => ?_, mrg b x z, hz, fun i hi => ?_⟩
  · unfold vec; by_cases hb : b i <;> simp [hb]
  · unfold vec at hi; unfold mrg
    by_cases hb : b i
    · simp [hb] at hi
    · simp [hb]

lemma Sb_null {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ}
    {A : Set (Fin N → Ω)} (hA : MeasurableSet A) (b : Fin N → Bool) :
    (Measure.pi fun _ : Fin N => μ) (A \ Sb μ A b) = 0 := by
  set P := Measure.pi fun _ : Fin N => μ with hP
  set M := {p : (Fin N → Ω) × (Fin N → Ω) | mrg b p.1 p.2 ∈ A} with hMdef
  have hM : MeasurableSet M := hA.preimage (mrg_meas b)
  have hnu := measurable_measure_prodMk_left (ν := P) hM
  set Z := {x : Fin N → Ω | P (Prod.mk x ⁻¹' M) = 0} with hZ
  have hZm : MeasurableSet Z := hnu (measurableSet_singleton 0)
  have hMZ : MeasurableSet (M ∩ Prod.fst ⁻¹' Z) := hM.inter (hZm.preimage measurable_fst)
  refine le_antisymm ?_ (by simp)
  calc P (A \ Sb μ A b)
      = Measure.map (fun p : (Fin N → Ω) × (Fin N → Ω) => mrg b p.1 p.2) (P.prod P) (A \ Sb μ A b) := by
        rw [mrg_map μ b]
    _ = (P.prod P) ((fun p : (Fin N → Ω) × (Fin N → Ω) => mrg b p.1 p.2) ⁻¹' (A \ Sb μ A b)) :=
        Measure.map_apply (mrg_meas b) (hA.diff (Sb_meas μ hA b))
    _ ≤ (P.prod P) (M ∩ Prod.fst ⁻¹' Z) := by
        apply measure_mono
        rintro ⟨x, z⟩ ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        simp only [Set.mem_preimage, hZ, Set.mem_setOf_eq]
        have hc : ∀ i, b i = false → mrg b x z i = x i := by
          intro i hi; unfold mrg; simp [hi]
        have h2' : ¬ 0 < P {z' | mrg b x z' ∈ A} := by
          intro hpos
          exact h2 (Sb_cyl μ A b (fun i hi => (hc i hi).symm) hpos)
        exact nonpos_iff_eq_zero.1 (not_lt.1 h2')
    _ = 0 := by
        rw [Measure.prod_apply hMZ]
        apply le_antisymm _ (by simp)
        calc ∫⁻ x, P (Prod.mk x ⁻¹' (M ∩ Prod.fst ⁻¹' Z)) ∂P ≤ ∫⁻ _, 0 ∂P := by
              apply lintegral_mono
              intro x
              by_cases hx : x ∈ Z
              · exact (measure_mono (fun z hz => hz.1)).trans (le_of_eq hx)
              · have : Prod.mk x ⁻¹' (M ∩ Prod.fst ⁻¹' Z) = ∅ := by
                  ext z; simp [hx]
                show P (Prod.mk x ⁻¹' (M ∩ Prod.fst ⁻¹' Z)) ≤ 0
                rw [this, measure_empty]
          _ = 0 := by simp

/-- the measurable pattern family below `U A`. -/
def Wp {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) {N : ℕ} (A : Set (Fin N → Ω))
    (x : Fin N → Ω) : Set (Fin N → ℝ) :=
  {s | ∃ b, s = vec b ∧ ∀ b', b ≤ b' → x ∈ Sb μ A b'}

lemma vec_le {N : ℕ} {b c : Fin N → Bool} (h : vec b ≤ vec c) : b ≤ c := by
  intro i
  rw [Bool.le_iff_imp]
  intro hb
  by_contra hc
  have h1 : vec b i = 1 := by simp [vec, hb]
  have h2 : vec c i = 0 := by simp [vec, hc]
  have := h i
  rw [h1, h2] at this
  norm_num at this

lemma vec_inj {N : ℕ} {b c : Fin N → Bool} (h : vec b = vec c) : b = c :=
  le_antisymm (vec_le (le_of_eq h)) (vec_le (le_of_eq h.symm))

lemma fam_Wp {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ}
    {A : Set (Fin N → Ω)} (hA : MeasurableSet A) : Fam (Wp μ A) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x s ⟨b, rfl, _⟩ i
    unfold vec; by_cases hb : b i <;> simp [hb]
  · intro s
    have : {x | s ∈ Wp μ A x} = ⋃ b ∈ {b : Fin N → Bool | s = vec b},
        ⋂ b' ∈ {b' : Fin N → Bool | b ≤ b'}, Sb μ A b' := by
      ext x; simp [Wp]
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) (fun b _ =>
      MeasurableSet.biInter (Set.to_countable _) (fun b' _ => Sb_meas μ hA b'))
  · rintro x x' s ⟨b, rfl, hb⟩ h
    refine ⟨b, rfl, fun b' hbb' => Sb_cyl μ A b' (fun i hi => ?_) (hb b' hbb')⟩
    apply h i
    have : b i = false := by
      have h3 := hbb' i
      rw [hi] at h3
      exact Bool.eq_false_iff.2 (fun ht => by simpa using (Bool.le_iff_imp.1 h3) ht)
    unfold vec; simp [this]
  · rintro x s s' ⟨b, rfl, hb⟩ h01' hle
    obtain ⟨c, rfl⟩ := is01_sub_range (S := {s'}) (fun t ht i => by rw [ht]; exact h01' i) rfl
    exact ⟨c, rfl, fun b' hcb' => hb b' ((vec_le hle).trans hcb')⟩

lemma Wp_sub {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) {N : ℕ} (A : Set (Fin N → Ω))
    (x : Fin N → Ω) : Wp μ A x ⊆ U A x := by
  rintro s ⟨b, rfl, hb⟩
  exact Sb_sub μ A b (hb b le_rfl)

lemma Wp_measure {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ}
    {A : Set (Fin N → Ω)} (hA : MeasurableSet A) :
    (Measure.pi fun _ : Fin N => μ) A
      ≤ (Measure.pi fun _ : Fin N => μ) {x | (0 : Fin N → ℝ) ∈ Wp μ A x} := by
  set P := Measure.pi fun _ : Fin N => μ
  have h0 : (0 : Fin N → ℝ) = vec (fun _ => false) := by funext i; simp [vec]
  have hset : A \ {x | (0 : Fin N → ℝ) ∈ Wp μ A x} ⊆ ⋃ b', A \ Sb μ A b' := by
    intro x ⟨hxA, hx⟩
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_diff, not_exists, not_and, not_not] at hcon
    exact hx ⟨fun _ => false, h0, fun b' _ => hcon b' hxA⟩
  have hnull : P (A \ {x | (0 : Fin N → ℝ) ∈ Wp μ A x}) = 0 :=
    measure_mono_null hset (measure_iUnion_null (fun b' => Sb_null μ hA b'))
  calc P A ≤ P ({x | (0 : Fin N → ℝ) ∈ Wp μ A x} ∪ (A \ {x | (0 : Fin N → ℝ) ∈ Wp μ A x})) :=
        measure_mono (by rw [Set.union_diff_self]; exact Set.subset_union_right)
    _ ≤ P {x | (0 : Fin N → ℝ) ∈ Wp μ A x} + P (A \ {x | (0 : Fin N → ℝ) ∈ Wp μ A x}) :=
        measure_union_le _ _
    _ = _ := by rw [hnull, add_zero]

end TalConvP

open TalagrandConc.ConvexHull MeasureTheory ENNReal in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (α : ℝ) (hα : 0 < α) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hmeas : Measurable fun x => fAlpha α A x) :
    ∫⁻ x, EReal.exp ((fAlpha α A x : ℝ≥0∞) : EReal) ∂(Measure.pi fun _ : Fin N => μ)
      ≤ (Measure.pi (fun _ : Fin N => μ) A) ^ (-α) := by
  calc ∫⁻ x, EReal.exp ((fAlpha α A x : ℝ≥0∞) : EReal) ∂(Measure.pi fun _ : Fin N => μ)
      = ∫⁻ x, TalConvP.Ex (TalConvP.gW α (U A x)) ∂(Measure.pi fun _ : Fin N => μ) := rfl
    _ ≤ ∫⁻ x, TalConvP.Ex (TalConvP.gW α (TalConvP.Wp μ A x)) ∂(Measure.pi fun _ : Fin N => μ) :=
        lintegral_mono (fun x => TalConvP.Ex_mono (TalConvP.gW_mono α (TalConvP.Wp_sub μ A x)))
    _ ≤ (Measure.pi (fun _ : Fin N => μ) {x | (0 : Fin N → ℝ) ∈ TalConvP.Wp μ A x}) ^ (-α) :=
        TalConvP.G μ α hα N _ (TalConvP.fam_Wp μ hA)
    _ ≤ (Measure.pi (fun _ : Fin N => μ) A) ^ (-α) :=
        by
          rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
          exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow (TalConvP.Wp_measure μ hA) hα.le)
