-- Prove2me | solution 1 for OAI.rational_prime_three_interval_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:47:51.584693+00:00
-- url     : https://prove2.me/submissions/c21b7f88-827a-4284-beb1-fd196c03d3e8

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Theorems.Thm_OAI_rational_prime_three_interval_real_count
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
namespace OAI
theorem _root_.solution :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ((Real.log 2) / 20) * (Y / Real.log Y) ≤
        (((Finset.Ioc ⌊Y / 3⌋₊ ⌊Y⌋₊).filter Nat.Prime).card : ℝ) := by
  obtain ⟨Y₀, hY₀⟩ := rational_prime_three_interval_real_count
  refine ⟨max 729 Y₀, ?_⟩
  intro Y hY
  have hY729 : (729 : ℝ) ≤ Y := le_trans (le_max_left _ _) hY
  have hfloor : ⌊Y / 3⌋₊ ≤ ⌊Y⌋₊ :=
    Nat.floor_mono (by linarith : Y / 3 ≤ Y)
  have hsubset : Nat.primesLE ⌊Y / 3⌋₊ ⊆ Nat.primesLE ⌊Y⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.mem_primesLE.mp hp).1.trans hfloor, (Nat.mem_primesLE.mp hp).2⟩
  have hset : (Finset.Ioc ⌊Y / 3⌋₊ ⌊Y⌋₊).filter Nat.Prime =
      Nat.primesLE ⌊Y⌋₊ \ Nat.primesLE ⌊Y / 3⌋₊ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hp⟩
      exact ⟨⟨hhi, hp⟩, fun hh => (not_le_of_gt hlo) hh.1⟩
    · rintro ⟨⟨hhi, hp⟩, hnot⟩
      exact ⟨⟨lt_of_not_ge (fun hle => hnot ⟨hle, hp⟩), hhi⟩, hp⟩
  have hcard : ((Finset.Ioc ⌊Y / 3⌋₊ ⌊Y⌋₊).filter Nat.Prime).card =
      Nat.primeCounting ⌊Y⌋₊ - Nat.primeCounting ⌊Y / 3⌋₊ := by
    rw [hset, Finset.card_sdiff_of_subset hsubset,
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  have hpile : Nat.primeCounting ⌊Y / 3⌋₊ ≤ Nat.primeCounting ⌊Y⌋₊ := by
    rw [← Nat.primesLE_card_eq_primeCounting,
      ← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_le_card hsubset
  rw [hcard, Nat.cast_sub hpile]
  exact hY₀ Y (le_trans (le_max_right _ _) hY)
end OAI
