-- Prove2me | solution 1 for QAlgorithms.Papers.BansalGupta19.mirrorDescent_regret
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:28:05.221616+00:00
-- url     : https://prove2.me/submissions/8921a818-5884-4c0f-ac29-e1177050b41b

import Definitions.Def_QAlgorithms_Defs_ConvexOpt
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open QAlgorithms

set_option backward.isDefEq.respectTransparency false

private lemma support_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {f : E → ℝ} (hf : ConvexOn ℝ K f) {a b : E}
    (ha : a ∈ K) (hb : b ∈ K) (hd : DifferentiableAt ℝ f a) :
    f a - f b ≤ fderiv ℝ f a (a - b) := by
  have hconv := hf.comp_affineMap (AffineMap.lineMap a b)
  have hdline : HasDerivAt (f ∘ AffineMap.lineMap a b)
      (fderiv ℝ f a (b - a)) (0 : ℝ) := by
    simpa using hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap : HasDerivAt (AffineMap.lineMap a b) (b - a) (0 : ℝ))
      (by simp)
  have hs := hconv.le_slope_of_hasDerivAt (by simpa using ha)
    (by simpa using hb) (by norm_num : (0 : ℝ) < 1) hdline
  simp only [slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one] at hs
  rw [← neg_sub b a, map_neg]
  linarith

private lemma divergence_lower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : E → ℝ} {α : ℝ} (hh : IsStronglyConvexWrt h α) (a b : E) :
    α / 2 * ‖a - b‖ ^ 2 ≤ bregmanDiv h a b := by
  have := hh.2 b a
  dsimp [bregmanDiv]
  linarith

private lemma projection_decreases {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : E → ℝ} (hd : Differentiable ℝ h) {K : Set E} (hK : Convex ℝ K)
    {p b a : E} (hp : IsBregmanProjection h K p b) (ha : a ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hh : IsStronglyConvexWrt h α) :
    bregmanDiv h a b ≤ bregmanDiv h a p := by
  have hm : IsMinOn (fun y => bregmanDiv h y p) K b := hp.2
  have hder : HasFDerivAt (𝕜 := ℝ) (fun y => bregmanDiv h y p)
      (fderiv ℝ h b - fderiv ℝ h p) b := by
    have h1 : HasFDerivAt (𝕜 := ℝ) (fun y => h y - h p) (fderiv ℝ h b) b :=
      (hd b).hasFDerivAt.sub_const (h p)
    have h2 : HasFDerivAt (𝕜 := ℝ) (fun y => fderiv ℝ h p y - fderiv ℝ h p p)
        (fderiv ℝ h p) b := (fderiv ℝ h p).hasFDerivAt.sub_const (fderiv ℝ h p p)
    convert h1.sub (𝕜 := ℝ) h2 using 1
    all_goals first | rfl | (funext y; simp [bregmanDiv, map_sub])
  have hdir := hm.localize.hasFDerivWithinAt_nonneg hder.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hK.segment_subset hp.1 ha))
  simp only [sub_apply, map_sub] at hdir
  have hn : 0 ≤ bregmanDiv h b p :=
    (mul_nonneg (by positivity) (sq_nonneg _)).trans (divergence_lower hh b p)
  simp only [bregmanDiv, map_sub] at hn ⊢
  linarith

private lemma dual_young {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E →L[ℝ] ℝ) (v : E) {α η : ℝ} (hα : 0 < α) (hη : 0 ≤ η) :
    η * g v - α / 2 * ‖v‖ ^ 2 ≤ η ^ 2 * ‖g‖ ^ 2 / (2 * α) := by
  have hg : g v ≤ ‖g‖ * ‖v‖ := (le_abs_self _).trans (g.le_opNorm v)
  have hmul := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg hη) hα.le
  apply (le_div_iff₀ (by positivity : 0 < 2 * α)).2
  nlinarith [sq_nonneg (α * ‖v‖ - η * ‖g‖)]

private lemma mirror_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h f : E → ℝ} {K : Set E} (hK : Convex ℝ K)
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (hh : IsStronglyConvexWrt h α)
    {a b p z : E} (hz : z ∈ K) (ha : a ∈ K) (hf : ConvexOn ℝ K f)
    (hd : DifferentiableAt ℝ f a)
    (hu : fderiv ℝ h p = fderiv ℝ h a - η • fderiv ℝ f a)
    (hp : IsBregmanProjection h K p b) :
    η * (f a - f z) ≤ bregmanDiv h z a - bregmanDiv h z b +
      η ^ 2 * ‖fderiv ℝ f a‖ ^ 2 / (2 * α) := by
  have hproj := projection_decreases hh.1 hK hp hz hα.le hh
  have hlow := divergence_lower hh p a
  have hyoung := dual_young (fderiv ℝ f a) (a - p) hα hη.le
  rw [norm_sub_rev a p] at hyoung
  have hsupport := mul_le_mul_of_nonneg_left (support_bound hf ha hz hd) hη.le
  have hid : bregmanDiv h z p - bregmanDiv h z a =
      -bregmanDiv h p a + η * (fderiv ℝ f a (z - a) + fderiv ℝ f a (a - p)) := by
    simp only [bregmanDiv, hu, sub_apply, smul_apply, smul_eq_mul, map_sub]
    ring
  simp only [map_sub] at hsupport hid hyoung
  linarith

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKint : (interior K).Nonempty) (T : ℕ) (f : ℕ → E → ℝ)
    (hfdiff : ∀ t ∈ Finset.Icc 1 T, Differentiable ℝ (f t))
    (hfconv : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ K (f t)) (h : E → ℝ) (αh : ℝ) (hαh : 0 < αh)
    (hh : IsStronglyConvexWrt h αh) (η : ℝ) (hη : 0 < η) (x0 : E) (x : ℕ → E)
    (hx : IsMirrorDescentRun h K η f x0 T x) (xstar : E) (hxstar : xstar ∈ K) :
    ∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t xstar ≤
      bregmanDiv h xstar x0 / η +
        η * (∑ t ∈ Finset.Icc 1 T, ‖fderiv ℝ (f t) (x t)‖ ^ 2) / (2 * αh) := by
  have hnonneg : 0 ≤ bregmanDiv h xstar x0 :=
    (mul_nonneg (by positivity) (sq_nonneg _)).trans (divergence_lower hh xstar x0)
  by_cases hT : T = 0
  · subst T
    simpa using div_nonneg hnonneg hη.le
  have hTpos : 1 ≤ T := by omega
  have hxK : ∀ t ∈ Finset.Icc 1 T, x t ∈ K := by
    intro t ht
    obtain ⟨htlo, hthi⟩ := Finset.mem_Icc.mp ht
    by_cases ht1 : t = 1
    · simpa [ht1] using hx.1.1
    · obtain ⟨p, _, hp⟩ := hx.2 (t - 1) (by omega) (by omega)
      simpa [Nat.sub_add_cancel htlo] using hp.1
  let P : ℕ → ℝ := fun t => if t ≤ T then bregmanDiv h xstar (x t) else 0
  have hstep : ∀ t ∈ Finset.Icc 1 T,
      η * (f t (x t) - f t xstar) ≤ P t - P (t + 1) +
        η ^ 2 * ‖fderiv ℝ (f t) (x t)‖ ^ 2 / (2 * αh) := by
    intro t ht
    obtain ⟨htlo, hthi⟩ := Finset.mem_Icc.mp ht
    by_cases htlast : t < T
    · obtain ⟨p, hu, hp⟩ := hx.2 t htlo htlast
      simpa only [P, if_pos hthi, if_pos (show t + 1 ≤ T by omega)] using
        mirror_step hKconv hαh hη hh hxstar (hxK t ht)
          (hfconv t ht) (hfdiff t ht (x t)) hu hp
    · have hl := divergence_lower hh xstar (x t)
      have hy := dual_young (fderiv ℝ (f t) (x t)) (x t - xstar) hαh hη.le
      rw [norm_sub_rev (x t) xstar] at hy
      have hs := mul_le_mul_of_nonneg_left
        (support_bound (hfconv t ht) (hxK t ht) hxstar (hfdiff t ht (x t))) hη.le
      simp only [P, if_pos hthi, if_neg (show ¬t + 1 ≤ T by omega), sub_zero]
      linarith
  have htel : (∑ t ∈ Finset.Icc 1 T, (P t - P (t + 1))) = P 1 := by
    have ht := Finset.sum_Icc_sub hTpos (fun t => -P t)
    simpa only [neg_sub_neg, show P (T + 1) = 0 by simp [P], neg_zero,
      zero_sub, neg_neg] using ht
  have hsum : η * (∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t xstar) ≤
      P 1 + η ^ 2 * (∑ t ∈ Finset.Icc 1 T, ‖fderiv ℝ (f t) (x t)‖ ^ 2) / (2 * αh) := by
    calc
      _ = ∑ t ∈ Finset.Icc 1 T, η * (f t (x t) - f t xstar) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      _ ≤ ∑ t ∈ Finset.Icc 1 T, (P t - P (t + 1) +
          η ^ 2 * ‖fderiv ℝ (f t) (x t)‖ ^ 2 / (2 * αh)) := Finset.sum_le_sum hstep
      _ = _ := by rw [Finset.sum_add_distrib, htel, ← Finset.sum_div, ← Finset.mul_sum]
  have hinitial : P 1 ≤ bregmanDiv h xstar x0 := by
    simpa only [P, if_pos hTpos] using
      projection_decreases hh.1 hKconv hx.1 hxstar hαh.le hh
  have htotal : η * (∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t xstar) ≤
      bregmanDiv h xstar x0 +
        η ^ 2 * (∑ t ∈ Finset.Icc 1 T, ‖fderiv ℝ (f t) (x t)‖ ^ 2) / (2 * αh) := by
    linarith
  apply (mul_le_mul_iff_right₀ hη).mp
  calc
    _ ≤ _ := htotal
    _ = _ := by field_simp [ne_of_gt hη, ne_of_gt hαh]
