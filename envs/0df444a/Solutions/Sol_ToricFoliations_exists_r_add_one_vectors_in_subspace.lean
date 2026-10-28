-- Prove2me | solution 1 for ToricFoliations.exists_r_add_one_vectors_in_subspace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:23:24.892193+00:00
-- url     : https://prove2.me/submissions/7bd733a1-e19b-457c-a7d1-f5b271659bab

import Mathlib
import Definitions.Def_ToricFoliations

open scoped BigOperators

namespace S216TF
open ToricFoliations

lemma div_le_one_of_dvd {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a ∣ b) : (a : ℚ) / b ≤ 1 := by
  rw [div_le_one (by exact_mod_cast hb)]
  exact_mod_cast Nat.le_of_dvd hb h

lemma D_le_one {n : ℕ} (C : WallData n) (i : Fin (n + 1)) : divisorIntersection C i ≤ 1 := by
  unfold divisorIntersection
  split_ifs with h
  · exact div_le_one_of_dvd C.mWall_pos C.mSigma'_pos C.wall_dvd_sigma'
  · have hi : i.val ≤ n - 1 := by
      have : i.val ≠ n := fun e => h (Fin.ext e)
      have := i.isLt; omega
    have hle : C.a i ≤ C.a (wallIndex n C.hn) := C.sorted _ _ (by simp [wallIndex]; omega)
    have han : (0 : ℚ) < C.a (wallIndex n C.hn) := by exact_mod_cast C.an_pos
    have hms : (0 : ℚ) < C.mSigma := by exact_mod_cast C.mSigma_pos
    have hw0 : (0 : ℚ) ≤ C.mWall := by positivity
    have hmle : (C.mWall : ℚ) ≤ C.mSigma := by
      exact_mod_cast Nat.le_of_dvd C.mSigma_pos C.wall_dvd_sigma
    have hle' : (C.a i : ℚ) ≤ C.a (wallIndex n C.hn) := by exact_mod_cast hle
    rw [div_le_one (by positivity)]
    calc (C.a i : ℚ) * C.mWall ≤ C.a (wallIndex n C.hn) * C.mWall :=
          mul_le_mul_of_nonneg_right hle' hw0
      _ ≤ C.a (wallIndex n C.hn) * C.mSigma := mul_le_mul_of_nonneg_left hmle han.le

lemma length_le {n : ℕ} (C : WallData n) (V : Submodule ℂ (Complexified n)) [DecidablePred (fun i : Fin (n+1) => toComplex (C.v i) ∈ V)] :
    curveLength C V ≤ ((Finset.univ.filter fun i : Fin (n+1) => toComplex (C.v i) ∈ V).card : ℚ) := by
  classical
  unfold curveLength
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs
  · simpa using D_le_one C i
  · simp

end S216TF

open ToricFoliations in
theorem solution {n r : ℕ} (C : WallData n)
    (V : Submodule ℂ (Complexified n))
    (hrank : Module.finrank ℂ V = r)
    (hlong : r < curveLength C V) :
    ∃ ι : Fin (r + 1) → Fin (n + 1),
      Function.Injective ι ∧
        ∀ j : Fin (r + 1), toComplex (C.v (ι j)) ∈ V := by
  classical
  set S := Finset.univ.filter fun i : Fin (n+1) => toComplex (C.v i) ∈ V
  have h1 := S216TF.length_le C V
  have hcard : r + 1 ≤ S.card := by
    have : (r : ℚ) < S.card := lt_of_lt_of_le hlong h1
    exact_mod_cast this
  refine ⟨fun j => S.orderEmbOfFin rfl (Fin.castLE hcard j), ?_, ?_⟩
  · intro a b hab
    have := (S.orderEmbOfFin rfl).injective hab
    exact Fin.castLE_injective hcard this
  · intro j
    have := S.orderEmbOfFin_mem rfl (Fin.castLE hcard j)
    exact (Finset.mem_filter.mp this).2
