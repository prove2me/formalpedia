-- Prove2me | solution 1 for RestrictLSI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:10:55.003979+00:00
-- url     : https://prove2.me/submissions/dbd10f11-dc82-4d1f-abc0-68dfa03a91bd

import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_IsLSI
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_RestrictLSI

set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E) (δ ε : ℝ)
    (t t' u u' : ℝ)
    (ht : 0 ≤ t) (htt' : t ≤ t') (ht'l : t' ≤ γ.len)
    (hu : t ≤ u) (huu' : u ≤ u') (hu't : u' ≤ t')
    (hu0 : 0 ≤ u) (hu'l : u' ≤ γ.len)
    (hlsi : IsLSI (curveRestrict γ t t' ht htt' ht'l) δ ε)
    (hnct : ¬ IsClosedCurve (curveRestrict γ t t' ht htt' ht'l))
    (hncu : ¬ IsClosedCurve (curveRestrict γ u u' hu0 huu' hu'l))
    (hpg : IsPiecewiseGeodesic (curveRestrict γ u u' hu0 huu' hu'l)) :
    IsLSI (curveRestrict γ u u' hu0 huu' hu'l) δ ε := by
-- BODY
  refine ⟨hpg, ?_⟩
  intro x hx y hy hsep
  have hlenU : (curveRestrict γ u u' hu0 huu' hu'l).len = u' - u := rfl
  rw [hlenU, Set.mem_Icc] at hx hy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have hdU : dGamma (curveRestrict γ u u' hu0 huu' hu'l) x y = |x - y| := by
    simp only [dGamma, if_neg hncu]
  have hevU : ∀ z : ℝ, 0 ≤ z → z ≤ u' - u →
      (curveRestrict γ u u' hu0 huu' hu'l).toFun z = γ.toFun (u + z) := by
    intro z hz0 hz1
    show γ.toFun (u + min (u' - u) (max 0 z)) = γ.toFun (u + z)
    rw [max_eq_right hz0, min_eq_right hz1]
  set σ : ℝ := (u - t) + x with hσ
  set τ : ℝ := (u - t) + y with hτ
  have hσ0 : 0 ≤ σ := by simp only [hσ]; linarith
  have hσ1 : σ ≤ t' - t := by simp only [hσ]; linarith
  have hτ0 : 0 ≤ τ := by simp only [hτ]; linarith
  have hτ1 : τ ≤ t' - t := by simp only [hτ]; linarith
  have hdT : dGamma (curveRestrict γ t t' ht htt' ht'l) σ τ = |x - y| := by
    simp only [dGamma, if_neg hnct, hσ, hτ]
    congr 1
    ring
  have hevT : ∀ z : ℝ, 0 ≤ z → z ≤ t' - t →
      (curveRestrict γ t t' ht htt' ht'l).toFun z = γ.toFun (t + z) := by
    intro z hz0 hz1
    show γ.toFun (t + min (t' - t) (max 0 z)) = γ.toFun (t + z)
    rw [max_eq_right hz0, min_eq_right hz1]
  have hlenT : (curveRestrict γ t t' ht htt' ht'l).len = t' - t := rfl
  have key := hlsi.2 σ (by rw [hlenT, Set.mem_Icc]; exact ⟨hσ0, hσ1⟩)
    τ (by rw [hlenT, Set.mem_Icc]; exact ⟨hτ0, hτ1⟩)
    (by rw [hdT]; rw [hdU] at hsep; exact hsep)
  rw [hdT, hevT σ hσ0 hσ1, hevT τ hτ0 hτ1] at key
  rw [hdU, hevU x hx0 hx1, hevU y hy0 hy1]
  have h1 : t + σ = u + x := by simp only [hσ]; ring
  have h2 : t + τ = u + y := by simp only [hτ]; ring
  rw [h1, h2] at key
  exact key
