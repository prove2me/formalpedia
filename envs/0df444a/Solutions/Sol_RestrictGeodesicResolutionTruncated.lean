-- Prove2me | solution 1 for RestrictGeodesicResolutionTruncated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:08.288676+00:00
-- url     : https://prove2.me/submissions/d9de068c-fe9b-48b1-ad44-e5ea0b9d6d73

import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_RestrictGeodesicResolutionTruncated

set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (η : Curve E)
    (k : ℕ) (s : ℕ → ℝ) (hres : IsGeodesicResolution η k s)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ η.len)
    (jA jB : ℕ) (hjAk : jA < k) (hsjA : s jA ≤ a) (hajA : a ≤ s (jA + 1))
    (hjB1 : 1 ≤ jB) (hjBk : jB ≤ k) (hsjB : s (jB - 1) ≤ b) (hbjB : b ≤ s jB) :
    IsGeodesicResolution (curveRestrict η a b ha hab.le hb) (jB - jA)
      (fun i => if i = 0 then 0 else if i = jB - jA then b - a else s (jA + i) - a) := by
-- BODY
  obtain ⟨hmono, hs0, hsk, hedge⟩ := hres
  have smono : ∀ p q : ℕ, p ≤ q → q ≤ k → s p ≤ s q := by
    intro p q hpq hqk
    exact hmono (Set.mem_Icc.mpr ⟨Nat.zero_le _, le_trans hpq hqk⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hqk⟩) hpq
  have hjAB : jA < jB := by
    by_contra hcon
    have hcon' : jB ≤ jA := Nat.not_lt.mp hcon
    have : s jB ≤ s jA := smono jB jA hcon' (le_of_lt hjAk)
    linarith
  -- transport of a geodesic edge of `η` through `curveRestrict`
  have restrict_geo : ∀ x y : ℝ, 0 ≤ x → y ≤ b - a → IsGeodesicOn η (a + x) (a + y) →
      IsGeodesicOn (curveRestrict η a b ha hab.le hb) x y := by
    intro x y hx hy hg u hu v hv
    obtain ⟨hu0, hu1⟩ := hu
    obtain ⟨hv0, hv1⟩ := hv
    have huv : min (b - a) (max 0 u) = u := by
      rw [max_eq_right (le_trans hx hu0), min_eq_right (le_trans hu1 hy)]
    have hvv : min (b - a) (max 0 v) = v := by
      rw [max_eq_right (le_trans hx hv0), min_eq_right (le_trans hv1 hy)]
    show dist (η.toFun (a + min (b - a) (max 0 u))) (η.toFun (a + min (b - a) (max 0 v)))
        = |u - v|
    rw [huv, hvv]
    have := hg (a + u) ⟨by linarith, by linarith⟩ (a + v) ⟨by linarith, by linarith⟩
    rw [this]
    congr 1
    ring
  have geo_mono : ∀ p q p' q' : ℝ, p ≤ p' → q' ≤ q → IsGeodesicOn η p q → IsGeodesicOn η p' q' := by
    intro p q p' q' hpp hqq hg u hu v hv
    exact hg u ⟨le_trans hpp hu.1, le_trans hu.2 hqq⟩ v ⟨le_trans hpp hv.1, le_trans hv.2 hqq⟩
  set K := jB - jA with hKdef
  have hK1 : 1 ≤ K := by omega
  set r : ℕ → ℝ := fun i => if i = 0 then 0 else if i = K then b - a else s (jA + i) - a with hrdef
  have hr0 : r 0 = 0 := by
    have h1 : r 0 = if (0:ℕ) = 0 then (0:ℝ) else if (0:ℕ) = K then b - a else s (jA + 0) - a := rfl
    rw [h1, if_pos rfl]
  have hrK : r K = b - a := by
    have h1 : r K = if K = 0 then (0:ℝ) else if K = K then b - a else s (jA + K) - a := rfl
    rw [h1, if_neg (by omega : ¬ (K = 0)), if_pos rfl]
  have hrmid : ∀ i : ℕ, i ≠ 0 → i ≠ K → r i = s (jA + i) - a := by
    intro i hi0 hiK
    have h1 : r i = if i = 0 then (0:ℝ) else if i = K then b - a else s (jA + i) - a := rfl
    rw [h1, if_neg hi0, if_neg hiK]
  have hrmono : ∀ i j : ℕ, i ≤ j → j ≤ K → r i ≤ r j := by
    intro i j hij hjK
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · subst hi0
      rw [hr0]
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · rw [hj0, hr0]
      · by_cases hjK' : j = K
        · rw [hjK', hrK]; linarith
        · rw [hrmid j (by omega) hjK']
          have h1 : s (jA + 1) ≤ s (jA + j) := smono (jA + 1) (jA + j) (by omega) (by omega)
          linarith
    · by_cases hjK' : j = K
      · rw [hjK', hrK]
        by_cases hiK' : i = K
        · rw [hiK', hrK]
        · rw [hrmid i (by omega) hiK']
          have h1 : s (jA + i) ≤ s (jB - 1) := smono (jA + i) (jB - 1) (by omega) (by omega)
          linarith
      · rw [hrmid i (by omega) (by omega), hrmid j (by omega) hjK']
        have h1 : s (jA + i) ≤ s (jA + j) := smono (jA + i) (jA + j) (by omega) (by omega)
        linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p _ q hq hpq
    exact hrmono p q hpq (Set.mem_Icc.mp hq).2
  · exact hr0
  · rw [hrK]; rfl
  · intro i hi
    have hi0' : (0:ℝ) ≤ r i := by
      have := hrmono 0 i (Nat.zero_le _) (by omega)
      rwa [hr0] at this
    have hi1' : r (i + 1) ≤ b - a := by
      have := hrmono (i + 1) K (by omega) le_rfl
      rwa [hrK] at this
    refine restrict_geo (r i) (r (i + 1)) hi0' hi1' ?_
    by_cases hz : i = 0
    · subst hz
      rw [hr0, add_zero]
      show IsGeodesicOn η a (a + r 1)
      by_cases hone : (1:ℕ) = K
      · -- K = 1, the single edge is the whole window
        have h1 : r 1 = b - a := by rw [hone]; exact hrK
        rw [h1]
        have hab' : a + (b - a) = b := by ring
        rw [hab']
        have hjBeq : jB = jA + 1 := by omega
        refine geo_mono (s jA) (s (jA + 1)) a b hsjA ?_ (hedge jA hjAk)
        rw [← hjBeq]; exact hbjB
      · rw [hrmid 1 (by omega) hone]
        have hab' : a + (s (jA + 1) - a) = s (jA + 1) := by ring
        rw [hab']
        exact geo_mono (s jA) (s (jA + 1)) a (s (jA + 1)) hsjA le_rfl (hedge jA hjAk)
    · by_cases hlast : i + 1 = K
      · rw [hlast, hrK, hrmid i hz (by omega)]
        have e1 : a + (s (jA + i) - a) = s (jA + i) := by ring
        have e2 : a + (b - a) = b := by ring
        rw [e1, e2]
        have hidx : jA + i = jB - 1 := by omega
        rw [hidx]
        have hedgeB : IsGeodesicOn η (s (jB - 1)) (s (jB - 1 + 1)) := hedge (jB - 1) (by omega)
        have hidx2 : jB - 1 + 1 = jB := by omega
        rw [hidx2] at hedgeB
        exact geo_mono (s (jB - 1)) (s jB) (s (jB - 1)) b le_rfl hbjB hedgeB
      · rw [hrmid i hz (by omega), hrmid (i + 1) (by omega) hlast]
        have e1 : a + (s (jA + i) - a) = s (jA + i) := by ring
        have e2 : a + (s (jA + (i + 1)) - a) = s (jA + (i + 1)) := by ring
        rw [e1, e2]
        have hidx : jA + (i + 1) = jA + i + 1 := by omega
        rw [hidx]
        exact hedge (jA + i) (by omega)
