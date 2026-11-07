-- Prove2me | solution 1 for WolffPASTA.Main.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:07:40.907614+00:00
-- url     : https://prove2.me/submissions/656e3ff6-d9dc-4448-9d2c-63c56b979ae5

import Mathlib
import Definitions.Def_WolffPASTA_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open WolffPASTA.Main

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : ℝ → Ω → ℕ) (lam : ℝ) (hlam : 0 < lam) (hA : IsPoissonProcess P A lam)
    (U : ℝ → Ω → ℝ) (hU : ∀ s ω, 0 ≤ s → 0 ≤ U s ω ∧ U s ω ≤ 1)
    (hjoint : JointlyMeasurable U) :
    ∀ ω, ∀ h : ℝ, 0 < h → ∀ (n : ℕ) (t : ℝ), n * h ≤ t → t ≤ (n + 1) * h →
      R U A lam (n * h) ω - lam * h ≤ R U A lam t ω ∧
        R U A lam t ω ≤ R U A lam ((n + 1) * h) ω + lam * h := by
  intro ω h hh n t h1 h2
  -- the section `g` of `U` at `ω`, extended to all of `ℝ`
  set g : ℝ → ℝ := fun s => U (max s 0) ω with hg
  have hgm : Measurable g := by
    have hm : Measurable (fun p : Ω × Set.Ici (0 : ℝ) => U p.2 p.1) := hjoint
    have hsec : Measurable (fun s : Set.Ici (0 : ℝ) => U s ω) :=
      hm.comp (measurable_const.prodMk measurable_id)
    have : Measurable (fun s : ℝ => (⟨max s 0, Set.mem_Ici.mpr (le_max_right _ _)⟩ : Set.Ici (0:ℝ))) :=
      (measurable_id.max measurable_const).subtype_mk
    exact hsec.comp this
  have hg01 : ∀ s, 0 ≤ g s ∧ g s ≤ 1 := fun s => hU _ ω (le_max_right _ _)
  have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := (1:ℝ))).mono_fun hgm.aestronglyMeasurable ?_
    refine Eventually.of_forall (fun s => ?_)
    simp only [Real.norm_eq_abs, abs_one]
    rw [abs_of_nonneg (hg01 s).1]; exact (hg01 s).2
  -- integral identity
  have hI : ∀ x, 0 ≤ x → ∫ s in (0:ℝ)..x, U s ω = ∫ s in (0:ℝ)..x, g s := by
    intro x hx
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [Set.uIcc_of_le hx] at hs
    simp [hg, max_eq_left hs.1]
  have hinc : ∀ a b, a ≤ b → 0 ≤ ∫ s in a..b, g s ∧ ∫ s in a..b, g s ≤ b - a := by
    intro a b hab
    refine ⟨intervalIntegral.integral_nonneg hab (fun s _ => (hg01 s).1), ?_⟩
    have := intervalIntegral.integral_mono_on hab (hgi a b) (intervalIntegrable_const (c := (1:ℝ)))
      (fun s _ => (hg01 s).2)
    simpa using this
  have hsplit : ∀ a b, ∫ s in (0:ℝ)..b, g s = (∫ s in (0:ℝ)..a, g s) + ∫ s in a..b, g s :=
    fun a b => (intervalIntegral.integral_add_adjacent_intervals (hgi 0 a) (hgi a b)).symm
  -- t * V t = ∫₀ᵗ U
  have htV : ∀ x, 0 ≤ x → x * V U x ω = ∫ s in (0:ℝ)..x, g s := by
    intro x hx
    rw [← hI x hx]
    simp only [V]
    rcases hx.lt_or_eq with hx' | hx'
    · field_simp
    · subst hx'; simp
  -- T k ω ≥ 0, so Y is monotone
  have hT : ∀ k, 0 ≤ T A k ω := fun k => Real.sInf_nonneg (fun x hx => hx.1)
  have hYmono : ∀ a b, a ≤ b → Y U A a ω ≤ Y U A b ω := by
    intro a b hab
    simp only [Y]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Icc_subset_Icc le_rfl (hA.mono ω hab)
    · intro k _ _; exact (hU _ ω (hT k)).1
  have h0 : (0:ℝ) ≤ n * h := by positivity
  have ht0 : 0 ≤ t := le_trans h0 h1
  have h3 : (0:ℝ) ≤ (n + 1) * h := by positivity
  have hRx : ∀ x, 0 ≤ x → R U A lam x ω = Y U A x ω - lam * ∫ s in (0:ℝ)..x, g s := by
    intro x hx
    simp only [R]
    rw [mul_assoc, htV x hx]
  rw [hRx _ h0, hRx _ ht0, hRx _ h3]
  have e1 := hsplit (n * h) t
  have e2 := hsplit t ((n + 1) * h)
  obtain ⟨a1, b1⟩ := hinc _ _ h1
  obtain ⟨a2, b2⟩ := hinc _ _ h2
  have y1 := hYmono _ _ h1
  have y2 := hYmono _ _ h2
  have hnh : ((n:ℝ) + 1) * h = n * h + h := by ring
  constructor
  · have : lam * (∫ s in (0:ℝ)..t, g s) ≤ lam * (∫ s in (0:ℝ)..(n * h), g s) + lam * h := by
      rw [← mul_add]; apply mul_le_mul_of_nonneg_left _ hlam.le
      rw [e1]; linarith
    linarith
  · have : lam * (∫ s in (0:ℝ)..((n + 1) * h), g s) ≤ lam * (∫ s in (0:ℝ)..t, g s) + lam * h := by
      rw [← mul_add]; apply mul_le_mul_of_nonneg_left _ hlam.le
      rw [e2]; linarith
    linarith
