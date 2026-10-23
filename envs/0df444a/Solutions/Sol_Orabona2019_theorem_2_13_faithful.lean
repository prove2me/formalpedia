-- Prove2me | solution 1 for Orabona2019.theorem_2_13_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:17:51.19482+00:00
-- url     : https://prove2.me/submissions/7fd34d53-96db-40ac-9d03-8fff187a8eb2

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ModernOnlineLearning_OGD_Defs

open ModernOnlineLearning.OGD

namespace OR84

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- gradient inequality for a convex function -/
theorem grad_ineq {C : Set E} {f : E → ℝ} (hf : ConvexOn ℝ C f) {x y g : E}
    (hx : x ∈ C) (hy : y ∈ C) (hg : HasGradientAt f g x) :
    f x + inner ℝ g (y - x) ≤ f y := by
  let L := AffineMap.lineMap (k := ℝ) x y
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (f ∘ L) := by
    have h1 := hf.comp_affineMap L
    refine h1.subset ?_ (convex_Icc 0 1)
    intro s hs
    show L s ∈ C
    exact hf.1.lineMap_mem hx hy hs
  have hd : HasDerivAt (f ∘ L) (inner ℝ g (y - x)) 0 := by
    have hL : HasDerivAt L (y - x) 0 := AffineMap.hasDerivAt_lineMap
    have hF : HasFDerivAt f (InnerProductSpace.toDual ℝ E g) (L 0) := by
      have : L 0 = x := by simp [L]
      rw [this]; exact hasGradientAt_iff_hasFDerivAt.mp hg
    have := hF.comp_hasDerivAt (0 : ℝ) hL
    simpa using this
  have := hconv.le_slope_of_hasDerivAt (x := 0) (y := 1) (by simp) (by simp) one_pos hd
  rw [slope_def_field] at this
  simp [L] at this
  linarith

/-- metric projection onto a convex set is nonexpansive towards points of the set -/
theorem proj_le {V : Set E} (hV : Convex ℝ V) {y p u : E}
    (hp : OnlineConvexOpt.FirstOrder.IsMetricProjection V y p) (hu : u ∈ V) :
    ‖p - u‖ ^ 2 ≤ ‖y - u‖ ^ 2 := by
  obtain ⟨hpV, hmin⟩ := hp
  have : Nonempty V := ⟨⟨p, hpV⟩⟩
  have hinf : ‖y - p‖ = ⨅ w : V, ‖y - w‖ := by
    apply le_antisymm
    · apply le_ciInf; intro w
      have := hmin w w.2; rwa [dist_eq_norm, dist_eq_norm] at this
    · exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨p, hpV⟩ : V)
  have hin := (norm_eq_iInf_iff_real_inner_le_zero hV hpV).mp hinf u hu
  have e : y - u = (y - p) + (p - u) := by abel
  rw [e, norm_add_sq_real]
  have : inner ℝ (y - p) (p - u) = - inner ℝ (y - p) (u - p) := by
    rw [← inner_neg_right, neg_sub]
  nlinarith [sq_nonneg ‖y - p‖]

theorem tele (a : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, (a t - a (t + 1)) = a 1 - a (T + 1) := by
  induction T with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring

theorem tele_bound (a η : ℕ → ℝ) (R : ℝ) (T : ℕ) (hT : 1 ≤ T)
    (ha : ∀ t, 1 ≤ t → t ≤ T + 1 → 0 ≤ a t ∧ a t ≤ R)
    (hη : ∀ t, 1 ≤ t → t ≤ T → 0 < η t)
    (hm : ∀ t, 1 ≤ t → t + 1 ≤ T → η (t + 1) ≤ η t) :
    ∑ t ∈ Finset.Icc 1 T, (a t - a (t + 1)) / (2 * η t) ≤ R / (2 * η T) - a (T + 1) / (2 * η T) := by
  induction T, hT using Nat.le_induction with
  | base =>
    simp
    have := (ha 1 le_rfl (by omega)).2
    have hη1 := hη 1 le_rfl le_rfl
    rw [div_le_iff₀ (by positivity), sub_mul, div_mul_cancel₀ _ (by positivity),
      div_mul_cancel₀ _ (by positivity)]
    linarith
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ih' := ih (fun t h1 h2 => ha t h1 (by omega)) (fun t h1 h2 => hη t h1 (by omega))
      (fun t h1 h2 => hm t h1 (by omega))
    have hηn := hη n hn (by omega)
    have hηn1 := hη (n + 1) (by omega) le_rfl
    have hmn := hm n hn le_rfl
    obtain ⟨h0, hR⟩ := ha (n + 1) (by omega) (by omega)
    have key : (R - a (n + 1)) * (1 / (2 * η n) - 1 / (2 * η (n + 1))) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (by linarith)
      rw [sub_nonpos]
      apply one_div_le_one_div_of_le (by positivity); linarith
    have e1 : R / (2 * η n) - a (n + 1) / (2 * η n) = (R - a (n + 1)) * (1 / (2 * η n)) := by ring
    have e2 : (a (n + 1) - a (n + 1 + 1)) / (2 * η (n + 1)) =
        a (n + 1) * (1 / (2 * η (n + 1))) - a (n + 1 + 1) / (2 * η (n + 1)) := by ring
    have e3 : R / (2 * η (n + 1)) = R * (1 / (2 * η (n + 1))) := by ring
    rw [e2, e3]
    rw [e1] at ih'
    nlinarith [key]

end OR84

open OR84 in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (V : Set E) (hV : V.Nonempty) (hc : IsClosed V)
    (hv : Convex ℝ V)
    (loss : ℕ → E → ℝ) (η : ℕ → ℝ) (x g : ℕ → E) (T : ℕ)
    (hT : 1 ≤ T) (u : E) (hu : u ∈ V)
    (hloss : ∀ t ∈ Finset.Icc 1 T,
      ∃ U : Set E, IsOpen U ∧ V ⊆ U ∧ ConvexOn ℝ U (loss t) ∧ DifferentiableOn ℝ (loss t) U)
    (hη : ∀ t ∈ Finset.Icc 1 T, 0 < η t)
    (hmono : ∀ t ∈ Finset.Icc 1 (T - 1), η (t + 1) ≤ η t)
    (hrun : IsOGDRun V loss η x g T) :
    (Bornology.IsBounded V →
      regret loss x u T ≤
        Metric.diam V ^ 2 / (2 * η T) +
          ∑ t ∈ Finset.Icc 1 T, (η t / 2) * ‖g t‖ ^ 2 -
            ‖x (T + 1) - u‖ ^ 2 / (2 * η T)) ∧
    (∀ η₀ : ℝ, (∀ t ∈ Finset.Icc 1 T, η t = η₀) →
      regret loss x u T ≤
        ‖u - x 1‖ ^ 2 / (2 * η₀) + (η₀ / 2) * ∑ t ∈ Finset.Icc 1 T, ‖g t‖ ^ 2 -
          ‖x (T + 1) - u‖ ^ 2 / (2 * η₀)) := by
  obtain ⟨-, -, -, hx1, hstep⟩ := hrun
  -- iterates stay in V
  have hxV : ∀ t, 1 ≤ t → t ≤ T + 1 → x t ∈ V := by
    intro t h1 h2
    induction t with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact hx1
      · exact ((hstep n (Finset.mem_Icc.mpr ⟨hn, by omega⟩)).2.2.2.2).1
  set D : ℕ → ℝ := fun t => ‖x t - u‖ ^ 2 with hD
  -- per-round bound
  have hround : ∀ t ∈ Finset.Icc 1 T, loss t (x t) - loss t u ≤
      (D t - D (t + 1)) / (2 * η t) + η t / 2 * ‖g t‖ ^ 2 := by
    intro t ht
    obtain ⟨hηt, ⟨C, -, hVC, hcv⟩, -, hgrad, hproj⟩ := hstep t ht
    have h1 := grad_ineq hcv (hVC (hxV t (Finset.mem_Icc.mp ht).1 (by have := (Finset.mem_Icc.mp ht).2; omega)))
      (hVC hu) hgrad
    have h2 := proj_le hv hproj hu
    have e : x t - η t • g t - u = (x t - u) - η t • g t := by abel
    rw [e, norm_sub_sq_real (x t - u) (η t • g t), inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hηt] at h2
    have hin : inner ℝ (g t) (u - x t) = - inner ℝ (x t - u) (g t) := by
      rw [real_inner_comm, ← inner_neg_left, neg_sub]
    rw [hin] at h1
    have : D t - D (t + 1) ≥ 2 * η t * inner ℝ (x t - u) (g t) - η t ^ 2 * ‖g t‖ ^ 2 := by
      simp only [hD]; nlinarith [h2]
    rw [ge_iff_le, ← sub_nonneg] at this
    have hpos : 0 < 2 * η t := by positivity
    rw [div_add' _ _ _ hpos.ne', le_div_iff₀ hpos]
    nlinarith [this]
  have hreg : regret loss x u T ≤ ∑ t ∈ Finset.Icc 1 T, (D t - D (t + 1)) / (2 * η t) +
      ∑ t ∈ Finset.Icc 1 T, η t / 2 * ‖g t‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum hround
  constructor
  · intro hb
    have hD : ∀ t, 1 ≤ t → t ≤ T + 1 → 0 ≤ D t ∧ D t ≤ Metric.diam V ^ 2 := by
      intro t h1 h2
      refine ⟨sq_nonneg _, ?_⟩
      have := Metric.dist_le_diam_of_mem hb (hxV t h1 h2) hu
      rw [dist_eq_norm] at this
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    have := tele_bound D η (Metric.diam V ^ 2) T hT hD
      (fun t h1 h2 => hη t (Finset.mem_Icc.mpr ⟨h1, h2⟩))
      (fun t h1 h2 => hmono t (Finset.mem_Icc.mpr ⟨h1, by omega⟩))
    linarith
  · intro η₀ hη₀
    have hs : ∑ t ∈ Finset.Icc 1 T, (D t - D (t + 1)) / (2 * η t) = (D 1 - D (T + 1)) / (2 * η₀) := by
      rw [← tele, Finset.sum_div]
      apply Finset.sum_congr rfl; intro t ht; rw [hη₀ t ht]
    have hs2 : ∑ t ∈ Finset.Icc 1 T, η t / 2 * ‖g t‖ ^ 2 = η₀ / 2 * ∑ t ∈ Finset.Icc 1 T, ‖g t‖ ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t ht; rw [hη₀ t ht]
    rw [hs, hs2] at hreg
    have : D 1 = ‖u - x 1‖ ^ 2 := by simp only [hD]; rw [norm_sub_rev]
    rw [this, sub_div] at hreg
    linarith
