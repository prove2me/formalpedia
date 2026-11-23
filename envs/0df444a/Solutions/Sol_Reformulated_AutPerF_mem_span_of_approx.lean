-- Prove2me | solution 1 for Reformulated.AutPerF.mem_span_of_approx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:38.732683+00:00
-- url     : https://prove2.me/submissions/68fa8f74-ba7e-4835-937a-2ab61bcfe927

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap



set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u
namespace Reformulated.AutPerF
theorem _root_.solution {A : Type*} [CommRing A] (q ξ : A) [IsAdicComplete (span {q}) A]
    (K : Set A) (h : ∀ x ∈ K, ∃ a, ∃ y ∈ K, x = ξ * a + q * y) {x : A} (hx : x ∈ K) :
    x ∈ span {ξ} := by
  choose! a s hs hxs using h
  have hK : ∀ n, s^[n] x ∈ K := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => rw [Function.iterate_succ_apply']; exact hs _ ih
  let b : ℕ → A := fun n => ∑ i ∈ Finset.range n, q ^ i * a (s^[i] x)
  have hb : ∀ n, x = ξ * b n + q ^ n * s^[n] x := by
    intro n
    induction n with
    | zero => simp [b]
    | succ n ih =>
      have h1 := hxs _ (hK n)
      simp only [b] at ih ⊢
      rw [Finset.sum_range_succ, Function.iterate_succ_apply']
      linear_combination ih + q ^ n * h1
  have hmem : ∀ (n : ℕ) (z : A), z ∈ (span {q} ^ n • ⊤ : Ideal A) ↔ q ^ n ∣ z := by
    intro n z
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := span {q}) (M := A) inferInstance (f := b) (by
    intro m n hle
    rw [SModEq.sub_mem, hmem]
    induction n, hle using Nat.le_induction with
    | base => simp
    | succ n hle ih =>
      simp only [b] at ih ⊢
      rw [Finset.sum_range_succ, ← sub_sub]
      exact dvd_sub ih ((pow_dvd_pow q hle).mul_right _))
  have : x - ξ * L = 0 := by
    refine IsHausdorff.haus (I := span {q}) (M := A) inferInstance _ fun n => ?_
    have h1 := hL n
    rw [SModEq.sub_mem, hmem] at h1 ⊢
    have : x - ξ * L - 0 = ξ * (b n - L) + q ^ n * s^[n] x := by linear_combination hb n
    rw [this]
    exact dvd_add (h1.mul_left _) (dvd_mul_right _ _)
  rw [sub_eq_zero.1 this]
  exact Ideal.mul_mem_right _ _ (mem_span_singleton_self _)
end Reformulated.AutPerF
