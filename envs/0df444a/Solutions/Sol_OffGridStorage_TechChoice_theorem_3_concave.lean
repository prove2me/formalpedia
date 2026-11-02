-- Prove2me | solution 1 for OffGridStorage.TechChoice.theorem_3_concave
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:22:06.339142+00:00
-- url     : https://prove2.me/submissions/8a77a209-e84e-46e0-bbee-3f132adb021d

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model

open MeasureTheory OffGridStorage.TechChoice

namespace OffGridConcaveAux

lemma rep (p : Params) (he1 : p.e ≤ 1) (he0 : 0 < p.e) (s K : ℝ) (hK : 0 ≤ K) :
    min s p.DH + min (p.e * pos (s - p.DH)) K =
      min s (min (p.DH + p.e * (s - p.DH)) (p.DH + K)) := by
  unfold pos
  rcases le_total s p.DH with h | h
  · rw [max_eq_left (by linarith), mul_zero, min_eq_left hK, min_eq_left h, add_zero]
    have h1 : s ≤ p.DH + p.e * (s - p.DH) := by nlinarith
    rw [min_eq_left (le_min h1 (by linarith))]
  · rw [max_eq_right (by linarith), min_eq_right h]
    have h1 : p.DH + p.e * (s - p.DH) ≤ s := by nlinarith
    rcases le_total (p.e * (s - p.DH)) K with h2 | h2
    · rw [min_eq_left h2, min_eq_left (by linarith : p.DH + p.e * (s - p.DH) ≤ p.DH + K),
        min_eq_right h1]
    · rw [min_eq_right h2, min_eq_right (by linarith : p.DH + K ≤ p.DH + p.e * (s - p.DH)),
        min_eq_right (by linarith : p.DH + K ≤ s)]

lemma pt_concave (p : Params) (v Q1 K1 Q2 K2 a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * min (Q1 * v) (min (p.DH + p.e * (Q1 * v - p.DH)) (p.DH + K1)) +
      b * min (Q2 * v) (min (p.DH + p.e * (Q2 * v - p.DH)) (p.DH + K2)) ≤
    min ((a * Q1 + b * Q2) * v) (min (p.DH + p.e * ((a * Q1 + b * Q2) * v - p.DH))
      (p.DH + (a * K1 + b * K2))) := by
  have m1 := min_le_left (Q1 * v) (min (p.DH + p.e * (Q1 * v - p.DH)) (p.DH + K1))
  have m2 := min_le_right (Q1 * v) (min (p.DH + p.e * (Q1 * v - p.DH)) (p.DH + K1))
  have m3 := min_le_left (p.DH + p.e * (Q1 * v - p.DH)) (p.DH + K1)
  have m4 := min_le_right (p.DH + p.e * (Q1 * v - p.DH)) (p.DH + K1)
  have n1 := min_le_left (Q2 * v) (min (p.DH + p.e * (Q2 * v - p.DH)) (p.DH + K2))
  have n2 := min_le_right (Q2 * v) (min (p.DH + p.e * (Q2 * v - p.DH)) (p.DH + K2))
  have n3 := min_le_left (p.DH + p.e * (Q2 * v - p.DH)) (p.DH + K2)
  have n4 := min_le_right (p.DH + p.e * (Q2 * v - p.DH)) (p.DH + K2)
  set A := min (Q1 * v) (min (p.DH + p.e * (Q1 * v - p.DH)) (p.DH + K1))
  set B := min (Q2 * v) (min (p.DH + p.e * (Q2 * v - p.DH)) (p.DH + K2))
  have hb' : b = 1 - a := by linarith
  subst hb'
  refine le_min ?_ (le_min ?_ ?_)
  · nlinarith [mul_le_mul_of_nonneg_left m1 ha, mul_le_mul_of_nonneg_left n1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left (m2.trans m3) ha, mul_le_mul_of_nonneg_left (n2.trans n3) hb]
  · nlinarith [mul_le_mul_of_nonneg_left (m2.trans m4) ha, mul_le_mul_of_nonneg_left (n2.trans n4) hb]

end OffGridConcaveAux

open OffGridConcaveAux in
theorem solution (p : Params) (hp : Standing p) :
    ConcaveOn ℝ {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2}
      (fun x => profitF p x.1 x.2) := by
  obtain ⟨hDH, hDL, he0, he1, hcQ, hcK, hg, hT⟩ := hp
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at *
    constructor
    · nlinarith [mul_nonneg ha hx.1, mul_nonneg hb hy.1]
    · nlinarith [mul_nonneg ha hx.2, mul_nonneg hb hy.2]
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    set H : ℝ → ℝ → ℝ → ℝ := fun Q K v =>
      min (Q * v) (min (p.DH + p.e * (Q * v - p.DH)) (p.DH + K)) with hH
    have hHc : ∀ Q K, Continuous (H Q K) := by intro Q K; simp only [hH]; fun_prop
    have hint : ∀ Q K : ℝ, 0 ≤ K → (∫ v in Set.Icc (0:ℝ) 1,
        (min (Q * v) p.DH + min (p.e * pos (Q * v - p.DH)) K)) = ∫ v in Set.Icc (0:ℝ) 1, H Q K v := by
      intro Q K hK
      congr 1; funext v
      exact rep p he1 he0 (Q * v) K hK
    have hKab : 0 ≤ a * x.2 + b * y.2 := by nlinarith [mul_nonneg ha hx.2, mul_nonneg hb hy.2]
    unfold profitF
    rw [hint _ _ hx.2, hint _ _ hy.2, hint _ _ hKab]
    have hI : ∀ Q K, IntegrableOn (H Q K) (Set.Icc (0:ℝ) 1) := fun Q K =>
      (hHc Q K).continuousOn.integrableOn_compact isCompact_Icc
    have key : a * (∫ v in Set.Icc (0:ℝ) 1, H x.1 x.2 v) + b * (∫ v in Set.Icc (0:ℝ) 1, H y.1 y.2 v)
        ≤ ∫ v in Set.Icc (0:ℝ) 1, H (a * x.1 + b * y.1) (a * x.2 + b * y.2) v := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hI _ _).const_mul a)
        ((hI _ _).const_mul b)]
      apply setIntegral_mono_on (((hI _ _).const_mul a).add ((hI _ _).const_mul b)) (hI _ _)
        measurableSet_Icc
      intro v _
      exact pt_concave p v x.1 x.2 y.1 y.2 a b ha hb hab
    have hT0 : (0:ℝ) ≤ p.T := Nat.cast_nonneg _
    have hg0 : 0 ≤ p.g := by linarith
    have := mul_le_mul_of_nonneg_left key (mul_nonneg hT0 hg0)
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith
