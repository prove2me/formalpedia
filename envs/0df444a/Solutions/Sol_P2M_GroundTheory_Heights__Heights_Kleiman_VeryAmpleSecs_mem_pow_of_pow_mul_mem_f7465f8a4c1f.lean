-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_mem_pow_of_pow_mul_mem_f7465f8a4c1f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:16.828606+00:00
-- url     : https://prove2.me/submissions/ae3a421e-62d4-44cf-a9da-5b7556f7b7ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSecsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleSecs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSecs
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSecs
theorem _root_.solution {A : Type*} [CommRing A] [Algebra A Ω] {L Q : Submodule A Ω}
    (hLQ : L * Q = 1) {r : ℕ} {h : Fin (r + 1) → Ω} (hL : Submodule.span A (Set.range h) = L)
    {s : Ω} {n : ℕ} (hs : ∀ j, ∃ e, h j ^ e * s ∈ L ^ (n + e)) : s ∈ L ^ n := by
  set C : Ideal A := (L ^ n).colon {s}
  have key : ∀ j, ∀ q ∈ Q, ∀ a : A, algebraMap A Ω a = h j * q → a ∈ C.radical := by
    intro j q hq a ha
    obtain ⟨e, he⟩ := hs j
    refine ⟨e, ?_⟩
    rw [Submodule.mem_colon_singleton, Algebra.smul_def, map_pow, ha]
    have hm := Submodule.mul_mem_mul (Submodule.pow_mem_pow Q hq e) he
    have hQL : Q ^ e * L ^ (n + e) = L ^ n := by
      calc Q ^ e * L ^ (n + e) = L ^ n * (L * Q) ^ e := by ring
        _ = L ^ n := by rw [hLQ, one_pow, mul_one]
    rw [hQL] at hm
    convert hm using 1
    ring
  have h1 : (1 : Submodule A Ω) ≤ Submodule.map (Algebra.linearMap A Ω) (C.radical : Submodule A A) := by
    rw [← hLQ, ← hL, ← Submodule.span_eq Q, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, q, hq, rfl⟩
    have hjq : h j * q ∈ L * Q := Submodule.mul_mem_mul (hL ▸ Submodule.subset_span ⟨j, rfl⟩) hq
    rw [hLQ, Submodule.mem_one] at hjq
    obtain ⟨a, ha⟩ := hjq
    exact ⟨a, key j q hq a ha, ha⟩
  obtain ⟨a, ⟨m, hm⟩, ha1⟩ := h1 (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  have ha1' : algebraMap A Ω a = 1 := ha1
  rw [Submodule.mem_colon_singleton, Algebra.smul_def, map_pow, ha1', one_pow, one_mul] at hm
  exact hm
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSecs
