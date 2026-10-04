-- Prove2me | solution 1 for TeschlODE.Stability.constant_on_omegaLimitSet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:54:14.097294+00:00
-- url     : https://prove2.me/submissions/84705e07-13b3-4ee2-84b1-09eae3385b6a

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow
import Definitions.Def_TeschlODE_Stability_semiOrbit
import Definitions.Def_TeschlODE_Stability_omegaLimitSet

open TeschlODE.Stability in
theorem P087d9e7e_aux {n : ℕ}
    (M : Set (EuclideanSpace ℝ (Fin n)))
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (L : EuclideanSpace ℝ (Fin n) → ℝ) (hL : ContinuousOn L U) (hLbdd : BddBelow (L '' U))
    (x : EuclideanSpace ℝ (Fin n)) (horb : semiOrbit 1 I Φ x ⊆ U)
    (hmono : ∀ t₀ ∈ I x, ∀ t₁ ∈ I x, 0 < t₀ → t₀ < t₁ → L (Φ t₁ x) ≤ L (Φ t₀ x))
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ omegaLimitSet M 1 I Φ x ∩ U) :
    L y = sInf ((fun t => L (Φ t x)) '' {t | t ∈ I x ∧ 0 < t}) := by
  obtain ⟨⟨_, t, htI, htinf, hty⟩, hyU⟩ := hy
  simp only [one_mul] at htinf
  set S : Set ℝ := {t | t ∈ I x ∧ 0 < t} with hS
  have hmem : ∀ s ∈ S, Φ s x ∈ U := fun s hs => horb ⟨s, hs.1, by simpa using hs.2, rfl⟩
  have hbdd : BddBelow ((fun t => L (Φ t x)) '' S) := by
    obtain ⟨b, hb⟩ := hLbdd
    refine ⟨b, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hb ⟨Φ s x, hmem s hs, rfl⟩
  have hpos : ∀ᶠ k in Filter.atTop, 0 < t k := htinf.eventually_gt_atTop 0
  have h1 : Filter.Tendsto (fun k => L (Φ (t k) x)) Filter.atTop (nhds (L y)) := by
    have hw : Filter.Tendsto (fun k => Φ (t k) x) Filter.atTop (nhdsWithin y U) :=
      tendsto_nhdsWithin_iff.2 ⟨hty, hpos.mono fun k hk => hmem (t k) ⟨htI k, hk⟩⟩
    exact (hL y hyU).tendsto.comp hw
  have h2 : Filter.Tendsto (fun k => L (Φ (t k) x)) Filter.atTop
      (nhds (sInf ((fun t => L (Φ t x)) '' S))) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [hpos] with k hk
      exact lt_of_lt_of_le ha (csInf_le hbdd ⟨t k, ⟨htI k, hk⟩, rfl⟩)
    · intro b hb
      have hne : ((fun t => L (Φ t x)) '' S).Nonempty := by
        obtain ⟨k, hk⟩ := hpos.exists
        exact ⟨_, t k, ⟨htI k, hk⟩, rfl⟩
      obtain ⟨_, ⟨s, hs, rfl⟩, hsb⟩ := exists_lt_of_csInf_lt hne hb
      filter_upwards [htinf.eventually_gt_atTop s] with k hk
      exact lt_of_le_of_lt (hmono s hs.1 (t k) (htI k) hs.2 hk) hsb
  exact tendsto_nhds_unique h1 h2

open TeschlODE.Stability in
theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hUM : U ⊆ M)
    (L : EuclideanSpace ℝ (Fin n) → ℝ) (hL : ContinuousOn L U) (hLbdd : BddBelow (L '' U))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M) (horb : semiOrbit 1 I Φ x ⊆ U)
    (hmono : ∀ t₀ ∈ I x, ∀ t₁ ∈ I x, 0 < t₀ → t₀ < t₁ → L (Φ t₁ x) ≤ L (Φ t₀ x)) :
    ∀ y ∈ omegaLimitSet M 1 I Φ x ∩ U, ∀ z ∈ omegaLimitSet M 1 I Φ x ∩ U, L y = L z := by
  intro y hy z hz
  rw [P087d9e7e_aux M I Φ U L hL hLbdd x horb hmono y hy,
    P087d9e7e_aux M I Φ U L hL hLbdd x horb hmono z hz]
