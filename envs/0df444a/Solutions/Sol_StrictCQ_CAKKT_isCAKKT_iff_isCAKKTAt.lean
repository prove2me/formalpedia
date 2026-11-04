-- Prove2me | solution 1 for StrictCQ.CAKKT.isCAKKT_iff_isCAKKTAt
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T01:05:02.607677+00:00
-- url     : https://prove2.me/submissions/28a114d5-bc8b-4a0d-a85a-61f556d37dc1

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_StrictCQ_CAKKT_Conditions

open Filter Topology
open scoped InnerProductSpace
open StrictCQ.CAKKT

theorem solution {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : xs ∈ C.feasible)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) :
    C.IsCAKKT f xs ↔ C.IsCAKKTAt f xs := by
  constructor
  · rintro ⟨x, lam, mu, hmu, hx, hgrad, hcomp⟩
    classical
    set mu' : ℕ → Fin p → ℝ := fun k j => if C.g j xs = 0 then mu k j else 0 with hmu'
    -- each `|mu k j * g j (x k)|` tends to zero
    have hterm : ∀ j, Tendsto (fun k => |mu k j * C.g j (x k)|) atTop (𝓝 0) := by
      intro j
      refine squeeze_zero (fun _ => abs_nonneg _) (fun k => ?_) hcomp
      have h1 : 0 ≤ ∑ i, |lam k i * C.h i (x k)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have h2 : |mu k j * C.g j (x k)| ≤ ∑ j, |mu k j * C.g j (x k)| :=
        Finset.single_le_sum (f := fun j => |mu k j * C.g j (x k)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      linarith
    -- inactive multipliers tend to zero
    have hmu0 : ∀ j, C.g j xs ≠ 0 → Tendsto (fun k => mu k j) atTop (𝓝 0) := by
      intro j hj
      have hneg : C.g j xs < 0 := lt_of_le_of_ne (hxs.2 j) hj
      have hgc : Tendsto (fun k => C.g j (x k)) atTop (𝓝 (C.g j xs)) :=
        ((hC.2 j).continuous.tendsto xs).comp hx
      have hev : ∀ᶠ k in atTop, C.g j (x k) < C.g j xs / 2 :=
        hgc.eventually (gt_mem_nhds (by linarith))
      have hb : ∀ᶠ k in atTop, |mu k j| ≤ |mu k j * C.g j (x k)| / (-(C.g j xs) / 2) := by
        filter_upwards [hev] with k hk
        rw [le_div_iff₀ (by linarith), abs_mul]
        have : -(C.g j xs) / 2 ≤ |C.g j (x k)| := by
          rw [abs_of_neg (by linarith)]; linarith
        exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
      have hlim : Tendsto (fun k => |mu k j * C.g j (x k)| / (-(C.g j xs) / 2)) atTop (𝓝 0) := by
        simpa using (hterm j).div_const (-(C.g j xs) / 2)
      exact squeeze_zero_norm' (hb.mono fun k hk => by simpa [Real.norm_eq_abs] using hk) hlim
    -- difference of the two gradient expressions tends to zero
    have hgradc : ∀ j, Continuous (gradient (C.g j)) := by
      intro j
      have : gradient (C.g j) = fun z =>
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (C.g j) z) := rfl
      rw [this]
      exact (InnerProductSpace.toDual ℝ _).symm.continuous.comp
        ((hC.2 j).continuous_fderiv one_ne_zero)
    have hdiff : Tendsto (fun k => ∑ j, (mu k j - mu' k j) • gradient (C.g j) (x k)) atTop
        (𝓝 0) := by
      have : ∀ j, Tendsto (fun k => (mu k j - mu' k j) • gradient (C.g j) (x k)) atTop (𝓝 0) := by
        intro j
        by_cases hj : C.g j xs = 0
        · simp [hmu', hj]
        · have h1 : Tendsto (fun k => mu k j - mu' k j) atTop (𝓝 0) := by
            simpa [hmu', hj] using hmu0 j hj
          have h2 : Tendsto (fun k => gradient (C.g j) (x k)) atTop
              (𝓝 (gradient (C.g j) xs)) := ((hgradc j).tendsto xs).comp hx
          simpa using h1.smul h2
      simpa using tendsto_finset_sum Finset.univ fun j _ => this j
    refine ⟨x, lam, mu', fun k j => ?_, fun k j hj => by simp [hmu', hj], hx, ?_, ?_⟩
    · by_cases hj : C.g j xs = 0 <;> simp [hmu', hj, hmu k j]
    · have := hgrad.sub hdiff
      rw [sub_zero] at this
      refine this.congr' (Eventually.of_forall fun k => ?_)
      simp only [sub_smul, Finset.sum_sub_distrib]
      abel
    · refine squeeze_zero (fun k => by positivity) (fun k => ?_) hcomp
      have : ∑ j, |mu' k j * C.g j (x k)| ≤ ∑ j, |mu k j * C.g j (x k)| := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hj : C.g j xs = 0
        · simp [hmu', hj]
        · simp only [hmu', hj, if_false, zero_mul, abs_zero]; exact abs_nonneg _
      linarith
  · rintro ⟨x, lam, mu, hmu, -, hx, hgrad, hcomp⟩
    exact ⟨x, lam, mu, hmu, hx, hgrad, hcomp⟩
