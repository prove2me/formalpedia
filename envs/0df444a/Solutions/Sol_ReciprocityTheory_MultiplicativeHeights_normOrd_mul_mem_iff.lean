-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.normOrd_mul_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:23:33.51806+00:00
-- url     : https://prove2.me/submissions/90b73388-9b82-4549-b2cd-c1247f7637a5

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_NormOrdLengthResidue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {B : Type} [CommRing B] [IsDedekindDomain B] {P : Ideal B}
    [hP : P.IsMaximal] {n : ℕ} {a : B} (ha : a ∈ P ^ n) (ha' : a ∉ P ^ (n + 1)) (b : B) :
    b * a ∈ P ^ (n + 1) ↔ b ∈ P := by
  constructor
  · intro h
    by_contra hb
    have hcop : IsCoprime (Ideal.span {b}) (P ^ (n + 1)) := by
      refine IsCoprime.pow_right ?_
      rw [Ideal.isCoprime_iff_sup_eq]
      obtain ⟨y, i, hi, hyi⟩ := hP.exists_inv hb
      rw [Ideal.eq_top_iff_one, ← hyi]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self b)))
        (Ideal.mem_sup_right hi)
    rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, Submodule.mem_sup] at hcop
    obtain ⟨y, hy, z, hz, hyz⟩ := hcop
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    apply ha'
    have : a = r * (b * a) + z * a := by
      calc a = (r * b + z) * a := by rw [hyz, one_mul]
        _ = r * (b * a) + z * a := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_right _ _ hz)
  · intro hb
    rw [pow_succ']
    exact Ideal.mul_mem_mul hb ha
end ReciprocityTheory.MultiplicativeHeights
