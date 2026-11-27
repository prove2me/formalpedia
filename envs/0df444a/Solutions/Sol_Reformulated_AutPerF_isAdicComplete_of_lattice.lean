-- Prove2me | solution 1 for Reformulated.AutPerF.isAdicComplete_of_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:31:53.474509+00:00
-- url     : https://prove2.me/submissions/002621f3-88e7-4120-a389-8b340141fc16

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope
import Theorems.Thm_Reformulated_AutPerF_mem_span_natCast_pow_iff
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap



set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
variable {A Q : Type*} [CommRing A] [CommRing Q]
namespace Reformulated.AutPerF
theorem _root_.solution (p N : ℕ) [IsAdicComplete (span {(p : A)}) A] (f : A →+* Q)
    (hp : IsUnit (p : Q)) (D : Subring Q) (h₁ : ∀ a, f a ∈ D)
    (h₂ : ∀ d ∈ D, ∃ a, f a = (p : Q) ^ N * d)
    (h₃ : ∀ x, (∀ k : ℕ, ∃ a, f x = (p : Q) ^ k * f a) → f x = 0) :
    IsAdicComplete (span {(p : D)}) D where
  haus' x hx := by
    simp only [SModEq.zero, mem_span_natCast_pow_iff] at hx
    obtain ⟨a, ha⟩ := h₂ x x.2
    have : f a = 0 := h₃ a fun k => by
      obtain ⟨y, hy⟩ := hx k
      obtain ⟨b, hb⟩ := h₂ y y.2
      refine ⟨b, ?_⟩
      rw [ha, hb, hy]; push_cast; ring
    rw [ha] at this
    exact Subtype.ext ((hp.pow N).mul_right_eq_zero.1 this)
  prec' d hd := by
    simp only [SModEq.sub_mem, mem_span_natCast_pow_iff] at hd ⊢
    have hs : ∀ k, ∃ b, (p : Q) ^ k * f b = (p : Q) ^ N * ((d (k + 1) : Q) - d k) := by
      intro k
      obtain ⟨y, hy⟩ := (dvd_neg.2 (hd k.le_succ))
      obtain ⟨b, hb⟩ := h₂ y y.2
      refine ⟨b, ?_⟩
      have := congrArg Subtype.val hy
      push_cast at this
      rw [hb, mul_left_comm, ← this]; ring
    choose b hb using hs
    obtain ⟨a0, ha0⟩ := h₂ (d 0) (d 0).2
    let a : ℕ → A := fun k => a0 + ∑ i ∈ Finset.range k, (p : A) ^ i * b i
    have ha : ∀ k, f (a k) = (p : Q) ^ N * d k := by
      intro k
      induction k with
      | zero => simpa [a] using ha0
      | succ k ih =>
        have : a (k + 1) = a k + (p : A) ^ k * b k := by
          simp only [a, Finset.sum_range_succ, add_assoc]
        rw [this, map_add, ih, map_mul, map_pow, map_natCast, hb]; ring
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := span {(p : A)}) a (fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_span_natCast_pow_iff, ← dvd_neg, neg_sub]
      simp only [a, add_sub_add_left_eq_sub]
      rw [← Finset.sum_Ico_eq_sub _ hmn]
      exact Finset.dvd_sum fun i hi => (pow_dvd_pow _ (Finset.mem_Ico.1 hi).1).mul_right _)
    simp only [SModEq.sub_mem, mem_span_natCast_pow_iff] at hL
    obtain ⟨c, hc⟩ := hL N
    refine ⟨d N - ⟨f c, h₁ c⟩, fun k => ?_⟩
    obtain ⟨e, he⟩ := hL (N + k)
    have h5 : (p : D) ^ k ∣ d (N + k) - (d N - ⟨f c, h₁ c⟩) := by
      refine ⟨⟨f e, h₁ e⟩, Subtype.ext ((hp.pow N).mul_left_cancel ?_)⟩
      have e1 := congrArg f hc
      have e2 := congrArg f he
      rw [map_sub, ha, map_mul, map_pow, map_natCast] at e1 e2
      push_cast
      linear_combination e2 - e1
    have := dvd_add (hd (Nat.le_add_left k N)) h5
    rwa [sub_add_sub_cancel] at this
end Reformulated.AutPerF
