-- Prove2me | solution 1 for PartitionChordSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:54:33.33423+00:00
-- url     : https://prove2.me/submissions/78b6f701-e23d-4b90-aa4a-ed3db9846c25

import Definitions.Def_Tablet_CurrentChordEstimate
import Definitions.Def_Tablet_CurrentResolutionAdditive
import Definitions.Def_Tablet_RestrictCurrentFormula
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_PartitionChordSum
import Theorems.Thm_CurrentChordEstimate
import Theorems.Thm_CurrentResolutionAdditive
import Theorems.Thm_RestrictCurrentFormula


set_option autoImplicit false

theorem _root_.solution {E : Type*} [MetricSpace E] (g : Curve E) (ω : Form1 E) (m : ℕ)
    (hm : 1 ≤ m) (u : ℕ → ℝ)
    (hu : ∀ i, i < m → (i : ℝ) * g.len / m ≤ u i ∧ u i ≤ ((i : ℝ) + 1) * g.len / m) :
    |curveCurrent g ω
        - ∑ i ∈ Finset.range m,
            ω.f (g.toFun (u i))
              * (ω.pi (g.toFun (((i : ℝ) + 1) * g.len / m))
                  - ω.pi (g.toFun ((i : ℝ) * g.len / m)))|
      ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * g.len ^ 2 / m := by
-- BODY
  have hL : (0:ℝ) ≤ g.len := g.len_nonneg
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hmne : (m:ℝ) ≠ 0 := ne_of_gt hmR
  set s : ℕ → ℝ := fun i => (i : ℝ) * g.len / m with hs
  have hscast : ∀ i : ℕ, s (i + 1) = ((i:ℝ) + 1) * g.len / m := by
    intro i; simp only [hs]; push_cast; ring
  have hstep : ∀ i : ℕ, s (i + 1) - s i = g.len / m := by
    intro i; rw [hscast i]; simp only [hs]; field_simp; ring
  have hnn : ∀ i : ℕ, 0 ≤ s i := by intro i; simp only [hs]; positivity
  have hLm : (0:ℝ) ≤ g.len / m := by positivity
  have hmonoi : ∀ i : ℕ, s i ≤ s (i + 1) := by
    intro i; have := hstep i; linarith
  have hle : ∀ i : ℕ, i < m → s (i + 1) ≤ g.len := by
    intro i hi
    have h1 : ((i:ℝ) + 1) ≤ (m:ℝ) := by exact_mod_cast hi
    have h2 : ((i:ℝ) + 1) * g.len / m ≤ (m:ℝ) * g.len / m := by gcongr
    have h3 : (m:ℝ) * g.len / m = g.len := by field_simp
    rw [hscast i]; linarith [h2, h3.le, h3.ge]
  have hsmono : MonotoneOn s (Set.Icc 0 m) := by
    intro i _ j _ hij
    have hij' : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
    simp only [hs]
    gcongr
  have hs0 : s 0 = 0 := by simp [hs]
  have hsm : s m = g.len := by simp only [hs]; field_simp
  have hres := CurrentResolutionAdditive g ω m s hsmono hs0 hsm
  have hA : (0:ℝ) ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) :=
    mul_nonneg ω.fLip.coe_nonneg ω.piLip.coe_nonneg
  have key : ∀ i ∈ Finset.range m,
      |(∫ t in (s i)..(s (i+1)), ω.f (g.toFun t) * deriv (ω.pi ∘ g.toFun) t)
          - ω.f (g.toFun (u i)) * (ω.pi (g.toFun (s (i+1))) - ω.pi (g.toFun (s i)))|
        ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * (g.len / m) ^ 2 / 2 := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have ha : 0 ≤ s i := hnn i
    have hab : s i ≤ s (i+1) := hmonoi i
    have hb : s (i+1) ≤ g.len := hle i hi'
    have hΔ : (0:ℝ) ≤ s (i+1) - s i := by linarith
    have hu1 : s i ≤ u i := (hu i hi').1
    have hu2 : u i ≤ s (i+1) := by rw [hscast i]; exact (hu i hi').2
    have hval : ∀ v : ℝ,
        (curveRestrict g (s i) (s (i+1)) ha hab hb).toFun v
          = g.toFun (s i + min (s (i+1) - s i) (max 0 v)) := fun _ => rfl
    have hlenσ : (curveRestrict g (s i) (s (i+1)) ha hab hb).len = s (i+1) - s i := rfl
    have e0 : (curveRestrict g (s i) (s (i+1)) ha hab hb).toFun 0 = g.toFun (s i) := by
      rw [hval]; congr 1; rw [max_self, min_eq_right hΔ]; ring
    have eL : (curveRestrict g (s i) (s (i+1)) ha hab hb).toFun
        (curveRestrict g (s i) (s (i+1)) ha hab hb).len = g.toFun (s (i+1)) := by
      rw [hlenσ, hval]; congr 1; rw [max_eq_right hΔ, min_self]; ring
    have eu : (curveRestrict g (s i) (s (i+1)) ha hab hb).toFun (u i - s i) = g.toFun (u i) := by
      rw [hval]; congr 1
      rw [max_eq_right (by linarith), min_eq_right (by linarith)]; ring
    have hchord := CurrentChordEstimate (curveRestrict g (s i) (s (i+1)) ha hab hb) ω
      (u i - s i) (by linarith) (by rw [hlenσ]; linarith)
    rw [e0, eL, eu, RestrictCurrentFormula g (s i) (s (i+1)) ha hab hb ω] at hchord
    have hlen2 : (curveRestrict g (s i) (s (i+1)) ha hab hb).len = g.len / m := by
      rw [hlenσ]; exact hstep i
    rw [hlen2] at hchord
    exact hchord
  rw [hres]
  have hsumeq : ∑ i ∈ Finset.range m,
      ω.f (g.toFun (u i)) * (ω.pi (g.toFun (((i:ℝ)+1) * g.len / m))
        - ω.pi (g.toFun ((i:ℝ) * g.len / m)))
      = ∑ i ∈ Finset.range m,
        ω.f (g.toFun (u i)) * (ω.pi (g.toFun (s (i+1))) - ω.pi (g.toFun (s i))) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hscast i]
  rw [hsumeq, ← Finset.sum_sub_distrib]
  calc |∑ i ∈ Finset.range m,
          ((∫ t in (s i)..(s (i+1)), ω.f (g.toFun t) * deriv (ω.pi ∘ g.toFun) t)
            - ω.f (g.toFun (u i)) * (ω.pi (g.toFun (s (i+1))) - ω.pi (g.toFun (s i))))|
      ≤ ∑ i ∈ Finset.range m,
          |(∫ t in (s i)..(s (i+1)), ω.f (g.toFun t) * deriv (ω.pi ∘ g.toFun) t)
            - ω.f (g.toFun (u i)) * (ω.pi (g.toFun (s (i+1))) - ω.pi (g.toFun (s i)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range m, (ω.fLip : ℝ) * (ω.piLip : ℝ) * (g.len / m) ^ 2 / 2 :=
        Finset.sum_le_sum key
    _ = (m:ℝ) * ((ω.fLip : ℝ) * (ω.piLip : ℝ) * (g.len / m) ^ 2 / 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ((ω.fLip : ℝ) * (ω.piLip : ℝ) * g.len ^ 2 / m) / 2 := by field_simp
    _ ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * g.len ^ 2 / m := by
        have hx : (0:ℝ) ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * g.len ^ 2 / m := by positivity
        linarith
