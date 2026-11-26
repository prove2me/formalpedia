-- Prove2me | solution 1 for RestrictPiecewiseGeodesic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:07:14.914361+00:00
-- url     : https://prove2.me/submissions/e84adda7-ba9f-4932-9fa0-775c8f4cccd7

import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_RestrictPiecewiseGeodesic

set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E)
    (k : ℕ) (s : ℕ → ℝ) (hres : IsGeodesicResolution γ k s) (p q : ℕ)
    (hpq : p ≤ q) (hqk : q ≤ k)
    (ha : 0 ≤ s p) (hab : s p ≤ s q) (hb : s q ≤ γ.len) :
    IsGeodesicResolution (curveRestrict γ (s p) (s q) ha hab hb) (q - p)
      (fun j => s (p + j) - s p) := by
-- BODY
  have restrict_isGeodesicOn : ∀ (a b : ℝ) (ha' : 0 ≤ a) (hab' : a ≤ b) (hb' : b ≤ γ.len)
      (x y : ℝ) (hx : 0 ≤ x) (hy : y ≤ b - a), IsGeodesicOn γ (a + x) (a + y) →
      IsGeodesicOn (curveRestrict γ a b ha' hab' hb') x y := by
    intro a b ha' hab' hb' x y hx hy hg s' hs t ht
    obtain ⟨hs0, hs1⟩ := hs
    obtain ⟨ht0, ht1⟩ := ht
    have hsv : min (b - a) (max 0 s') = s' := by
      rw [max_eq_right (le_trans hx hs0), min_eq_right (le_trans hs1 hy)]
    have htv : min (b - a) (max 0 t) = t := by
      rw [max_eq_right (le_trans hx ht0), min_eq_right (le_trans ht1 hy)]
    show dist (γ.toFun (a + min (b - a) (max 0 s'))) (γ.toFun (a + min (b - a) (max 0 t))) = |s' - t|
    rw [hsv, htv]
    have := hg (a + s') ⟨by linarith, by linarith⟩ (a + t) ⟨by linarith, by linarith⟩
    rw [this]
    congr 1
    ring
  obtain ⟨hmono, hs0, hsk, hedge⟩ := hres
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    have : s (p + i) ≤ s (p + j) := by
      refine hmono ?_ ?_ (by omega)
      · exact ⟨Nat.zero_le _, by simp only [Set.mem_Icc] at hi; omega⟩
      · exact ⟨Nat.zero_le _, by simp only [Set.mem_Icc] at hj; omega⟩
    simpa using this
  · simp
  · show s (p + (q - p)) - s p = (curveRestrict γ (s p) (s q) ha hab hb).len
    have : p + (q - p) = q := by omega
    rw [this]; rfl
  · intro i hi
    have hpi : p + i < q := by omega
    have hgeo : IsGeodesicOn γ (s (p + i)) (s (p + i + 1)) := hedge (p + i) (by omega)
    have hle1 : s (p + (i + 1)) ≤ s q := by
      refine hmono ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ (by omega)
    have hge : s p ≤ s (p + i) := by
      refine hmono ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ (by omega)
    have key := restrict_isGeodesicOn (s p) (s q) ha hab hb
      (s (p + i) - s p) (s (p + (i + 1)) - s p) (by linarith) (by linarith)
      (by
        have h1 : s p + (s (p + i) - s p) = s (p + i) := by ring
        have h2 : s p + (s (p + (i + 1)) - s p) = s (p + (i + 1)) := by ring
        rw [h1, h2]
        have : p + (i + 1) = p + i + 1 := by omega
        rw [this]; exact hgeo)
    have hidx : p + (i + 1) = p + i + 1 := by omega
    simpa [hidx] using key
