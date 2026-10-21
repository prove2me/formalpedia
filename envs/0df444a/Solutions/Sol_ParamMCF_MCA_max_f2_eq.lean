-- Prove2me | solution 1 for ParamMCF.MCA.max_f2_eq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T23:46:03.253444+00:00
-- url     : https://prove2.me/submissions/70c07e7d-b06a-4393-96d4-6a1d7a1bce7c

import Mathlib
import Definitions.Def_ParamMCF_MCA_Model

namespace ParamMCF.MCA

/-- A continuous function that is nonpositive on negatives is nonpositive at zero. -/
lemma pmcf_nonpos_at_zero (φ : ℝ → ℝ) (hφ : ContinuousAt φ 0) (h : ∀ s, s < 0 → φ s ≤ 0) :
    φ 0 ≤ 0 := by
  have ht : Filter.Tendsto φ (nhdsWithin 0 (Set.Iio 0)) (nhds (φ 0)) :=
    hφ.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => h s hs)

/-- A continuous function that is nonnegative on positives is nonnegative at zero. -/
lemma pmcf_nonneg_at_zero (φ : ℝ → ℝ) (hφ : ContinuousAt φ 0) (h : ∀ s, 0 < s → 0 ≤ φ s) :
    0 ≤ φ 0 := by
  have ht : Filter.Tendsto φ (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ 0)) :=
    hφ.tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => h s hs)

/-- Under the shape condition, `g'' = 0` on `(-∞, 0]`. -/
lemma pmcf_f2_zero_nonpos (g : ℝ → ℝ)
    (hg3 : Differentiable ℝ (deriv g) ∧ Differentiable ℝ (deriv (deriv g)))
    (hshape : MonotoneOn (deriv (deriv g)) (Set.Ici 0) ∧
      (∀ x, 0 ≤ x → 0 ≤ deriv (deriv g) x) ∧
      AntitoneOn (deriv (deriv g)) (Set.Iio 0) ∧
      (∀ x, x < 0 → deriv (deriv g) x ≤ 0)) :
    ∀ x, x ≤ 0 → deriv (deriv g) x = 0 := by
  have hc : Continuous (deriv (deriv g)) := hg3.2.continuous
  have h0 : deriv (deriv g) 0 = 0 := le_antisymm
    (pmcf_nonpos_at_zero _ hc.continuousAt hshape.2.2.2) (hshape.2.1 0 le_rfl)
  intro x hx
  rcases eq_or_lt_of_le hx with h | h
  · rw [h, h0]
  · apply le_antisymm (hshape.2.2.2 x h)
    have ht : Filter.Tendsto (deriv (deriv g)) (nhdsWithin 0 (Set.Iio 0))
        (nhds (deriv (deriv g) 0)) := hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hle : deriv (deriv g) 0 ≤ deriv (deriv g) x := by
      apply le_of_tendsto ht
      filter_upwards [Ioo_mem_nhdsLT h] with y hy
      exact hshape.2.2.1 (Set.mem_Iio.2 h) (Set.mem_Iio.2 hy.2) hy.1.le
    linarith [hshape.2.1 0 le_rfl]

/-- Under the shape condition, `|g''|` is monotone on `ℝ`. -/
lemma pmcf_absf2_mono (g : ℝ → ℝ)
    (hg3 : Differentiable ℝ (deriv g) ∧ Differentiable ℝ (deriv (deriv g)))
    (hshape : MonotoneOn (deriv (deriv g)) (Set.Ici 0) ∧
      (∀ x, 0 ≤ x → 0 ≤ deriv (deriv g) x) ∧
      AntitoneOn (deriv (deriv g)) (Set.Iio 0) ∧
      (∀ x, x < 0 → deriv (deriv g) x ≤ 0)) :
    Monotone (fun ξ => |deriv (deriv g) ξ|) := by
  have hz := pmcf_f2_zero_nonpos g hg3 hshape
  intro x y hxy
  simp only
  by_cases hx : x ≤ 0
  · rw [hz x hx, abs_zero]; exact abs_nonneg _
  · push_neg at hx
    have hy : 0 < y := lt_of_lt_of_le hx hxy
    rw [abs_of_nonneg (hshape.2.1 x hx.le), abs_of_nonneg (hshape.2.1 y hy.le)]
    exact hshape.1 (Set.mem_Ici.2 hx.le) (Set.mem_Ici.2 hy.le) hxy

theorem max_f2_eq_sol (g : ℝ → ℝ) (hg : IsMarginalCost g)
    (hg3 : Differentiable ℝ (deriv g) ∧ Differentiable ℝ (deriv (deriv g)))
    (hshape : MonotoneOn (deriv (deriv g)) (Set.Ici 0) ∧
      (∀ x, 0 ≤ x → 0 ≤ deriv (deriv g) x) ∧
      AntitoneOn (deriv (deriv g)) (Set.Iio 0) ∧
      (∀ x, x < 0 → deriv (deriv g) x ≤ 0))
    (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs) (i : Fin K) :
    sSup ((fun ξ => |deriv (deriv g) ξ|) '' Set.Icc (xs i.castSucc) (xs i.succ)) =
      max |deriv (deriv g) (xs i.castSucc)| |deriv (deriv g) (xs i.succ)| := by
  have hm := pmcf_absf2_mono g hg3 hshape
  have hlt : xs i.castSucc < xs i.succ := hxs (Fin.castSucc_lt_succ (i := i))
  have hgr : IsGreatest ((fun ξ => |deriv (deriv g) ξ|) '' Set.Icc (xs i.castSucc) (xs i.succ))
      (|deriv (deriv g) (xs i.succ)|) := by
    refine ⟨⟨xs i.succ, Set.right_mem_Icc.2 hlt.le, rfl⟩, ?_⟩
    rintro _ ⟨ξ, hξ, rfl⟩
    exact hm hξ.2
  rw [hgr.csSup_eq, max_eq_right (hm hlt.le)]

end ParamMCF.MCA

open ParamMCF.MCA in
theorem solution (g : ℝ → ℝ) (hg : IsMarginalCost g)
    (hg3 : Differentiable ℝ (deriv g) ∧ Differentiable ℝ (deriv (deriv g)))
    (hshape : MonotoneOn (deriv (deriv g)) (Set.Ici 0) ∧
      (∀ x, 0 ≤ x → 0 ≤ deriv (deriv g) x) ∧
      AntitoneOn (deriv (deriv g)) (Set.Iio 0) ∧
      (∀ x, x < 0 → deriv (deriv g) x ≤ 0))
    (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs) (i : Fin K) :
    sSup ((fun ξ => |deriv (deriv g) ξ|) '' Set.Icc (xs i.castSucc) (xs i.succ)) =
      max |deriv (deriv g) (xs i.castSucc)| |deriv (deriv g) (xs i.succ)| :=
  max_f2_eq_sol g hg hg3 hshape K xs hxs i
