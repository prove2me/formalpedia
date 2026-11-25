-- Prove2me | solution 1 for PIW.AdelicOrbitU.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:38:28.503446+00:00
-- url     : https://prove2.me/submissions/c10a24d7-f283-48ac-b9f0-11cb81b533ca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf
import Theorems.Thm_PIW_AdelicOrbitU_glue_mul
import Theorems.Thm_PIW_AdelicOrbitU_norm_id
import Theorems.Thm_PIW_AdelicOrbitU_norm_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
namespace PIW.AdelicOrbitU
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (ι : R →+* S) (s : S →+* S) (Θ : S) (D Bt P Q a b : R)
    (hΘ : Θ ^ 2 = ι D) (hsΘ : s Θ = -Θ) (hsι : ∀ r, s (ι r) = ι r) (hPQ : P ^ 2 - D * Q ^ 2 = 1)
    (Bi K i4 : R) (hB : Bt * Bi = 1) (hK : Q * D * K = 1) (h4 : (4 : R) * i4 = 1) (hU : UnitChoice R) :
    ∃ lam : S, lam * s lam = 1 ∧ IsUnit (ι Bt - s lam * (ι a + ι b * Θ)) := by
  let p : Fin 4 → R := ![1, -1, P, -P]
  let q : Fin 4 → R := ![0, 0, Q, -Q]
  have hnorm : ∀ i, p i ^ 2 - D * q i ^ 2 = 1 := by
    intro i
    fin_cases i <;> simp [p, q] <;> linear_combination hPQ
  obtain ⟨f, hf⟩ : ∃ f : Fin 4 → R, ∀ i,
      f i = (Bt - p i * a + q i * b * D) ^ 2 - D * (q i * a - p i * b) ^ 2 := ⟨_, fun _ => rfl⟩
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    set I := Ideal.span (Set.range f) with hI
    have hm : ∀ i, f i ∈ I := fun i => Ideal.subset_span ⟨i, rfl⟩
    have e0 : f 0 = (Bt - 1 * a + 0 * b * D) ^ 2 - D * (0 * a - 1 * b) ^ 2 := (hf 0).trans rfl
    have e1 : f 1 = (Bt - (-1) * a + 0 * b * D) ^ 2 - D * (0 * a - (-1) * b) ^ 2 := (hf 1).trans rfl
    have e2 : f 2 = (Bt - P * a + Q * b * D) ^ 2 - D * (Q * a - P * b) ^ 2 := (hf 2).trans rfl
    have e3 : f 3 = (Bt - (-P) * a + (-Q) * b * D) ^ 2 - D * ((-Q) * a - (-P) * b) ^ 2 :=
      (hf 3).trans rfl
    have ha : a ∈ I := by
      have h : a = (i4 * Bi) * (f 1 - f 0) := by
        rw [e0, e1]
        linear_combination (-a) * h4 + (-4 * a * i4) * hB
      rw [h]
      exact I.mul_mem_left _ (sub_mem (hm 1) (hm 0))
    have hx : P * a - Q * b * D ∈ I := by
      have h : P * a - Q * b * D = (i4 * Bi) * (f 3 - f 2) := by
        rw [e2, e3]
        linear_combination (-(P * a - Q * b * D)) * h4 + (-4 * (P * a - Q * b * D) * i4) * hB
      rw [h]
      exact I.mul_mem_left _ (sub_mem (hm 3) (hm 2))
    have hb : b ∈ I := by
      have h : b = K * (P * a - (P * a - Q * b * D)) := by
        linear_combination (-b) * hK
      rw [h]
      exact I.mul_mem_left _ (sub_mem (I.mul_mem_left _ ha) hx)
    have h1 : (1 : R) = Bi ^ 2 * f 0 + (Bi ^ 2 * (2 * Bt - a)) * a + (Bi ^ 2 * D * b) * b := by
      rw [e0]
      linear_combination (-(Bt * Bi + 1)) * hB
    have hmem : Bi ^ 2 * f 0 + (Bi ^ 2 * (2 * Bt - a)) * a + (Bi ^ 2 * D * b) * b ∈ I :=
      add_mem (add_mem (I.mul_mem_left _ (hm 0)) (I.mul_mem_left _ ha)) (I.mul_mem_left _ hb)
    rw [← h1] at hmem
    exact (Ideal.eq_top_iff_one _).mpr hmem
  obtain ⟨e, hid, hor, hsum1, hunit⟩ := hU 4 f hspan
  have hidS : ∀ i, ι (e i) * ι (e i) = ι (e i) := fun i => by rw [← map_mul, hid i]
  have horS : ∀ i j, i ≠ j → ι (e i) * ι (e j) = 0 := fun i j h => by
    rw [← map_mul, hor i j h, map_zero]
  have hE1 : ∑ i, ι (e i) = 1 := by rw [← map_sum, hsum1, map_one]
  have hsl : s (∑ i, ι (e i) * (ι (p i) + ι (q i) * Θ)) =
      ∑ i, ι (e i) * (ι (p i) - ι (q i) * Θ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_add, map_mul, hsι, hsι, hsι, hsΘ]
    ring
  have hn : ∀ i, (ι (p i) + ι (q i) * Θ) * (ι (p i) - ι (q i) * Θ) = 1 := fun i => by
    rw [norm_one _ _ _ _ hΘ, ← map_pow, ← map_pow, ← map_mul, ← map_sub, hnorm i, map_one]
  refine ⟨∑ i, ι (e i) * (ι (p i) + ι (q i) * Θ), ?_, ?_⟩
  · rw [hsl, glue_mul _ hidS horS]
    simp only [hn, mul_one]
    exact hE1
  · rw [hsl]
    set w := ι a + ι b * Θ with hw
    have hz : ι Bt - (∑ i, ι (e i) * (ι (p i) - ι (q i) * Θ)) * w =
        ∑ i, ι (e i) * (ι Bt - (ι (p i) - ι (q i) * Θ) * w) := by
      have h : ∑ i, ι (e i) * (ι Bt - (ι (p i) - ι (q i) * Θ) * w) =
          (∑ i, ι (e i)) * ι Bt - (∑ i, ι (e i) * (ι (p i) - ι (q i) * Θ)) * w := by
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [h, hE1, one_mul]
    rw [hz]
    have hsz : s (∑ i, ι (e i) * (ι Bt - (ι (p i) - ι (q i) * Θ) * w)) =
        ∑ i, ι (e i) * (ι Bt - (ι (p i) + ι (q i) * Θ) * (ι a - ι b * Θ)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hw, map_mul, map_sub, map_add, hsι, hsΘ]
      ring
    have hprod : (∑ i, ι (e i) * (ι Bt - (ι (p i) - ι (q i) * Θ) * w)) *
        s (∑ i, ι (e i) * (ι Bt - (ι (p i) - ι (q i) * Θ) * w)) = ι (∑ i, e i * f i) := by
      rw [hsz, glue_mul _ hidS horS, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hw, norm_id _ _ _ _ _ _ _ hΘ, hf i, map_mul]
      simp only [map_sub, map_add, map_mul, map_pow]
    have hu := hunit.map ι
    rw [← hprod] at hu
    exact isUnit_of_mul_isUnit_left hu
end PIW.AdelicOrbitU
