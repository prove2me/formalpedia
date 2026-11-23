-- Prove2me | solution 1 for TIESharp.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:32:54.601542+00:00
-- url     : https://prove2.me/submissions/e31b758c-09a1-41d1-8f84-f3d80972e824

import Mathlib
import Definitions.Def_TIESharp_Nonneg

set_option autoImplicit false

open scoped BigOperators
open MeasureTheory Set

namespace TIESharp

private lemma myerson_tail (q : ℝ → ℝ) (hq : AntitoneOn q (Set.Ici 0))
    (hint : IntegrableOn q (Set.Ioi 0)) {v s : ℝ} (hv : 0 ≤ v) (hs : 0 ≤ s) :
    (∫ u in Set.Ioi s, q u) + (s - v) * q s ≤ ∫ u in Set.Ioi v, q u := by
  have hInt (a : ℝ) (ha : 0 ≤ a) : IntegrableOn q (Set.Ioi a) :=
    hint.mono_set (Set.Ioi_subset_Ioi ha)
  rcases le_total v s with hvs | hsv
  · have hIoc : IntegrableOn q (Set.Ioc v s) :=
      hint.mono_set (fun u hu => hv.trans_lt hu.1)
    have hsplit : (∫ u in Set.Ioi v, q u) =
        (∫ u in Set.Ioc v s, q u) + ∫ u in Set.Ioi s, q u := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi hvs]
      exact setIntegral_union (Set.Ioc_disjoint_Ioi (le_refl s)) measurableSet_Ioi
        hIoc (hInt s hs)
    have hcomp : (s - v) * q s ≤ ∫ u in Set.Ioc v s, q u := by
      have hcint : IntegrableOn (fun _ : ℝ => q s) (Set.Ioc v s) := by
        apply integrableOn_const <;> simp [Real.volume_Ioc]
      have hmono := setIntegral_mono_on hcint hIoc measurableSet_Ioc
        (fun u hu => hq (hv.trans hu.1.le) hs hu.2)
      simpa [setIntegral_const, Real.volume_Ioc, max_eq_left (sub_nonneg.mpr hvs)] using hmono
    linarith
  · have hIoc : IntegrableOn q (Set.Ioc s v) :=
      hint.mono_set (fun u hu => hs.trans_lt hu.1)
    have hsplit : (∫ u in Set.Ioi s, q u) =
        (∫ u in Set.Ioc s v, q u) + ∫ u in Set.Ioi v, q u := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi hsv]
      exact setIntegral_union (Set.Ioc_disjoint_Ioi (le_refl v)) measurableSet_Ioi
        hIoc (hInt v hv)
    have hcomp : (∫ u in Set.Ioc s v, q u) ≤ (v - s) * q s := by
      have hcint : IntegrableOn (fun _ : ℝ => q s) (Set.Ioc s v) := by
        apply integrableOn_const <;> simp [Real.volume_Ioc]
      have hmono := setIntegral_mono_on hIoc hcint measurableSet_Ioc
        (fun u hu => hq hs (hs.trans hu.1.le) hu.1.le)
      simpa [setIntegral_const, Real.volume_Ioc, max_eq_left (sub_nonneg.mpr hsv)] using hmono
    linarith

end TIESharp

open TIESharp

theorem solution (n m : ℕ) (Q : Fin m → Fin n → (Fin n → ℝ) → ℝ)
    (hQnn : ∀ j i (c : Fin n → ℝ), (∀ a, 0 ≤ c a) → 0 ≤ Q j i c)
    (hQsum : ∀ j (c : Fin n → ℝ), (∀ a, 0 ≤ c a) → ∑ i, Q j i c = 1)
    (hQmono : ∀ j i (c : Fin n → ℝ), (∀ a, 0 ≤ c a) →
      AntitoneOn (fun s => Q j i (Function.update c i s)) (Set.Ici 0))
    (hQint : ∀ j i (c : Fin n → ℝ), (∀ a, 0 ≤ c a) →
      MeasureTheory.IntegrableOn (fun u => Q j i (Function.update c i u)) (Set.Ioi 0))
    (y : (Fin n → Fin m → ℝ) → (Fin m → Fin n) → ℝ)
    (hy : ∀ b : Fin n → Fin m → ℝ, Nonneg b →
      (∀ A, 0 ≤ y b A) ∧ ∑ A, y b A = 1 ∧
      ∀ i j, ∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => A j = i), y b A
        = Q j i (fun a => b a j)) :
    ∀ (b : Fin n → Fin m → ℝ) (i : Fin n) (ti bi : Fin m → ℝ),
      Nonneg b → (∀ j, 0 ≤ ti j) → (∀ j, 0 ≤ bi j) →
        (∑ j, ((Function.update b i bi) i j * Q j i (fun a => Function.update b i bi a j)
            + ∫ u in Set.Ioi ((Function.update b i bi) i j),
                Q j i (Function.update (fun a => Function.update b i bi a j) i u)))
          - ∑ j, ti j * ∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => A j = i),
              y (Function.update b i bi) A
        ≤ (∑ j, ((Function.update b i ti) i j * Q j i (fun a => Function.update b i ti a j)
            + ∫ u in Set.Ioi ((Function.update b i ti) i j),
                Q j i (Function.update (fun a => Function.update b i ti a j) i u)))
          - ∑ j, ti j * ∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => A j = i),
              y (Function.update b i ti) A := by
  intro b i ti bi hb hti hbi
  have hupdate (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) : Nonneg (Function.update b i r) := by
    intro a j
    by_cases hai : a = i
    · subst a
      simpa using hr j
    · simpa [Function.update_of_ne hai] using hb a j
  have hmarg (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (j : Fin m) :
      (∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => A j = i),
        y (Function.update b i r) A) = Q j i (fun a => Function.update b i r a j) :=
    (hy (Function.update b i r) (hupdate r hr)).2.2 i j
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j hj
  let q : ℝ → ℝ := fun u => Q j i (Function.update (fun a => b a j) i u)
  have hbase : ∀ a, 0 ≤ b a j := fun a => hb a j
  have hkey := TIESharp.myerson_tail q (hQmono j i (fun a => b a j) hbase)
    (hQint j i (fun a => b a j) hbase) (hti j) (hbi j)
  have hcol (r : Fin m → ℝ) :
      (fun a => Function.update b i r a j) =
        Function.update (fun a => b a j) i (r j) := by
    funext a
    by_cases hai : a = i
    · subst a
      simp
    · simp [Function.update_of_ne hai]
  rw [hmarg bi hbi j, hmarg ti hti j]
  simp only [Function.update_self, hcol, Function.update_idem]
  change (bi j * q (bi j) + ∫ u in Set.Ioi (bi j), q u) - ti j * q (bi j) ≤
    (ti j * q (ti j) + ∫ u in Set.Ioi (ti j), q u) - ti j * q (ti j)
  calc
    (bi j * q (bi j) + ∫ u in Set.Ioi (bi j), q u) - ti j * q (bi j) =
        (∫ u in Set.Ioi (bi j), q u) + (bi j - ti j) * q (bi j) := by ring
    _ ≤ ∫ u in Set.Ioi (ti j), q u := hkey
    _ = (ti j * q (ti j) + ∫ u in Set.Ioi (ti j), q u) - ti j * q (ti j) := by ring
