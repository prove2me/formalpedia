-- Prove2me | solution 1 for TypeICutPointExists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:07:18.09559+00:00
-- url     : https://prove2.me/submissions/5747d3b0-c6a6-438e-953b-56ea76ec371e

import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_dGamma
import Definitions.Def_Tablet_IsLSI
import Definitions.Def_Tablet_ArcGeodesicResolution
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_CurveArcEval
import Definitions.Def_Tablet_TypeICutMinimalPair
import Definitions.Def_Tablet_TypeICutPointExists
import Theorems.Thm_ArcGeodesicResolution
import Theorems.Thm_CurveArcEval
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_TypeICutMinimalPair


set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ)
    (δ ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hnlsi : ¬ IsLSI γ δ ε) :
    ∃ (t t' : ℝ) (ht0 : 0 ≤ t) (htl : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht'l : t' ≤ γ.len) (β : ℝ),
      β = (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len ∧
      β = dGamma γ t t' ∧
      δ ≤ β ∧ β ≤ γ.len / 2 ∧
      dist (γ.toFun t) (γ.toFun t') ≤ ε * β ∧
      (δ < β → ε * β ≤ dist (γ.toFun t) (γ.toFun t')) ∧
      (δ < β → ¬ IsClosedCurve (curveArc γ hclosed t t' ht0 htl ht'0 ht'l)) ∧
      (δ < β → IsLSI (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) δ ε) := by
-- BODY
  -- Step 1: failure of l.s.i. produces an admissible pair.
  have hfail : ∃ s₀ ∈ Set.Icc (0 : ℝ) γ.len, ∃ s₀' ∈ Set.Icc (0 : ℝ) γ.len,
      δ ≤ dGamma γ s₀ s₀' ∧ dist (γ.toFun s₀) (γ.toFun s₀') ≤ ε * dGamma γ s₀ s₀' := by
    by_contra hc
    refine hnlsi ⟨hpg, ?_⟩
    intro a ha b hb hsep
    by_contra hlt
    exact hc ⟨a, ha, b, hb, hsep, le_of_lt (not_le.mp hlt)⟩
  obtain ⟨s₀, hs₀, s₀', hs₀', hsep₀, hcon₀⟩ := hfail
  -- Steps 2-5: the minimizing pair.
  obtain ⟨t, t', ht, ht', hsep, hcon, hβδ, hβL, hmin⟩ :=
    TypeICutMinimalPair γ hclosed δ ε hδ s₀ s₀' hs₀ hs₀' hsep₀ hcon₀
  obtain ⟨ht0, htl⟩ := ht
  obtain ⟨ht'0, ht'l⟩ := ht'
  -- General Fact 3: on pairs whose counter-clockwise arc is at most half the total length,
  -- the circle distance is that arc length.
  have hd : ∀ a b : ℝ, dGamma γ a b = min |a - b| (γ.len - |a - b|) := by
    intro a b; simp only [dGamma, if_pos hclosed]
  have hGF3 : ∀ a b : ℝ, (if a ≤ b then b - a else (γ.len - a) + b) ≤ γ.len / 2 →
      dGamma γ a b = (if a ≤ b then b - a else (γ.len - a) + b) := by
    intro a b hab
    rw [hd]
    by_cases h : a ≤ b
    · rw [if_pos h] at hab ⊢
      rw [abs_of_nonpos (by linarith : a - b ≤ 0), min_eq_left (by linarith)]
      ring
    · have h' : b < a := not_le.mp h
      rw [if_neg h] at hab ⊢
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b), min_eq_right (by linarith)]
      ring
  -- The arc and its evaluation dictionary.
  obtain ⟨hAlen, σ, hσ0, hσend, hσmem, hσell⟩ :=
    CurveArcEval γ hclosed t t' ht0 htl ht'0 ht'l
  have hAL2 : (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len ≤ γ.len / 2 := by
    rw [hAlen]; exact hβL
  have hALδ : δ ≤ (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len := by
    rw [hAlen]; exact hβδ
  have hAdG : dGamma γ t t' = (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len := by
    rw [hAlen]; exact hGF3 t t' hβL
  have hA0 : (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun 0 = γ.toFun t := by
    rw [(hσmem 0 ⟨le_refl 0, (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len_nonneg⟩).2, hσ0]
  have hAend : (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun
      (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len = γ.toFun t' := by
    rw [(hσmem _ ⟨(curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len_nonneg, le_refl _⟩).2, hσend]
  have hAlip : ∀ x y : ℝ, dist ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun x)
      ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun y) ≤ |x - y| := by
    intro x y
    simpa [Real.dist_eq] using (CurveLipschitz (curveArc γ hclosed t t' ht0 htl ht'0 ht'l)).dist_le_mul x y
  -- The strict minimality half: a pair strictly inside the arc is strictly shorter than the
  -- minimum, so it cannot lie in the admissible set.
  have hstrict : ∀ p ∈ Set.Icc (0:ℝ) (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len,
      ∀ p' ∈ Set.Icc (0:ℝ) (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len, p ≤ p' →
      δ ≤ p' - p → p' - p < (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len →
      ε * (p' - p) < dist ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun p)
        ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun p') := by
    intro p hp p' hp' hpp hδle hlt
    obtain ⟨hσp, hAp⟩ := hσmem p hp
    obtain ⟨hσp', hAp'⟩ := hσmem p' hp'
    have hell := hσell p hp p' hp' hpp
    have hdg : dGamma γ (σ p) (σ p') = p' - p := by
      rw [hGF3 (σ p) (σ p') (by rw [hell]; linarith)]
      exact hell
    by_contra hcon2
    have hle2 : dist (γ.toFun (σ p)) (γ.toFun (σ p')) ≤ ε * dGamma γ (σ p) (σ p') := by
      rw [hdg, ← hAp, ← hAp']
      exact not_lt.mp hcon2
    have hkey := hmin (σ p) hσp (σ p') hσp' (by rw [hdg]; exact hδle) hle2
    rw [hell, ← hAlen] at hkey
    linarith
  -- Step 8.
  have hstep8 : δ < (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len →
      ε * (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len ≤ dist (γ.toFun t) (γ.toFun t') := by
    intro hδA
    rw [← hA0, ← hAend]
    by_contra hcontra
    have hD : dist ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun 0)
        ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun
          (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len)
        < ε * (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len := not_le.mp hcontra
    have hρ : 0 < ε * (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len
        - dist ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun 0)
          ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun
            (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len) := by linarith
    have hden : (0:ℝ) < ε + 1 := by linarith
    have hη0 : 0 < min ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len - δ)
        ((ε * (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len
          - dist ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun 0)
            ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun
              (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len)) / (ε + 1)) :=
      lt_min (by linarith) (div_pos hρ hden)
    set η : ℝ := min ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len - δ)
        ((ε * (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len
          - dist ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun 0)
            ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun
              (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len)) / (ε + 1)) with hηdef
    have hηle : η ≤ (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len - δ := by
      rw [hηdef]; exact min_le_left _ _
    have hηρ : (ε + 1) * η ≤ ε * (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len
        - dist ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun 0)
          ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun
            (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len) := by
      have h1 : η ≤ (ε * (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len
          - dist ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun 0)
            ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun
              (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len)) / (ε + 1) := by
        rw [hηdef]; exact min_le_right _ _
      have h2 := (le_div_iff₀ hden).mp h1
      linarith
    have hp : (η/2) ∈ Set.Icc (0:ℝ) (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len :=
      ⟨by linarith, by linarith⟩
    have hp' : ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len - η/2)
        ∈ Set.Icc (0:ℝ) (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len :=
      ⟨by linarith, by linarith⟩
    have hkey := hstrict (η/2) hp ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len - η/2) hp'
      (by linarith) (by linarith) (by linarith)
    have h1 : dist ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun (η/2))
        ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun 0) ≤ η/2 := by
      have h := hAlip (η/2) 0
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ η/2 - 0)] at h
      linarith
    have h2 : dist ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun
        (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len)
        ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun
          ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len - η/2)) ≤ η/2 := by
      have h := hAlip (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len
        ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len - η/2)
      rw [abs_of_nonneg (by linarith :
        (0:ℝ) ≤ (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len
          - ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len - η/2))] at h
      linarith
    have htri := dist_triangle4 ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun (η/2))
      ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun 0)
      ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun
        (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len)
      ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun
        ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len - η/2))
    nlinarith [hkey, htri, h1, h2, hηρ]
  -- Step 9.
  have hstep9 : δ < (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len →
      ¬ IsClosedCurve (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) := by
    intro hδA hcA
    have h8 := hstep8 hδA
    have h : (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun
        (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len
        = (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun 0 := hcA
    rw [hAend, hA0] at h
    have hz : dist (γ.toFun t) (γ.toFun t') = 0 := by rw [h]; exact dist_self _
    have hpos : 0 < ε * (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len :=
      mul_pos hε0 (by linarith)
    linarith
  -- Step 10.
  have hstep10 : δ < (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len →
      IsLSI (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) δ ε := by
    intro hδA
    refine ⟨?_, ?_⟩
    · obtain ⟨k, s, hres⟩ := hpg
      obtain ⟨kA, sA, _, hresA, _, _⟩ :=
        ArcGeodesicResolution γ hclosed k s hres t t' ht0 htl ht'0 ht'l
      exact ⟨kA, sA, hresA⟩
    · have hnc := hstep9 hδA
      have hdA : ∀ x y : ℝ,
          dGamma (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) x y = |x - y| := by
        intro x y; simp only [dGamma, if_neg hnc]
      have main : ∀ p ∈ Set.Icc (0:ℝ) (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len,
          ∀ p' ∈ Set.Icc (0:ℝ) (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len, p ≤ p' →
          δ ≤ p' - p → ε * (p' - p) ≤ dist ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun p)
            ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun p') := by
        intro p hp p' hp' hpp hδle
        rcases lt_or_ge (p' - p) (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len with hlt | hge
        · exact le_of_lt (hstrict p hp p' hp' hpp hδle hlt)
        · obtain ⟨hp0, hp1⟩ := hp
          obtain ⟨hp'0, hp'1⟩ := hp'
          have hpz : p = 0 := by linarith
          have hp'z : p' = (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len := by linarith
          rw [hpz, hp'z, hA0, hAend]
          have h8 := hstep8 hδA
          have hrw : ε * ((curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len - 0)
              = ε * (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len := by ring
          rw [hrw]
          exact h8
      intro p hp p' hp' hsepA
      rw [hdA] at hsepA ⊢
      rcases le_total p p' with h | h
      · rw [abs_of_nonpos (by linarith : p - p' ≤ 0)]
        have hrw : ε * -(p - p') = ε * (p' - p) := by ring
        rw [hrw]
        refine main p hp p' hp' h ?_
        rw [abs_of_nonpos (by linarith : p - p' ≤ 0)] at hsepA
        linarith
      · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ p - p'), dist_comm]
        have hrw : ε * (p - p') = ε * (p - p') := by ring
        refine main p' hp' p hp h ?_
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ p - p')] at hsepA
        linarith
  exact ⟨t, t', ht0, htl, ht'0, ht'l,
    (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len, rfl, hAdG.symm, hALδ, hAL2,
    by rw [← hAdG]; exact hcon, hstep8, hstep9, hstep10⟩
