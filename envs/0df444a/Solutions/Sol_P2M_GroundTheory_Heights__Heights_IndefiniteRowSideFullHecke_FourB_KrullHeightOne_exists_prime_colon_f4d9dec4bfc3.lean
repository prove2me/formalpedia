-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_KrullHeightOne_exists_prime_colon_f4d9dec4bfc3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:45.375165+00:00
-- url     : https://prove2.me/submissions/4c2e6a12-65c9-49ad-9b2d-1e4a1d08278b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsKrullHeightOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PKrullHeightOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open Ideal
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
namespace KrullHeightOne
theorem _root_.solution {A : Type*} [CommRing A] [IsNoetherianRing A]
    (p q : A) (hqp : ¬ q ∣ p) :
    ∃ (a : A) (P : Ideal A), P.IsPrime ∧ ¬ q ∣ a * p ∧ ∀ x, x ∈ P ↔ q ∣ x * (a * p) := by
  let mk := Ideal.Quotient.mk (Ideal.span {q})
  let M := Submodule.span A {mk p}
  have hx : (⟨mk p, Submodule.mem_span_singleton_self _⟩ : M) ≠ 0 := by
    intro h
    apply hqp
    have : mk p = 0 := congrArg Subtype.val h
    rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
  obtain ⟨P, hP, -⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hx
  obtain ⟨hPp, y, hy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 y.2
  have key : ∀ x, x ∈ P ↔ q ∣ x * (a * p) := by
    intro x
    rw [hy, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Subtype.val_inj]
    change x • (y : A ⧸ Ideal.span {q}) = 0 ↔ _
    rw [← ha, smul_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, mul_assoc]
  refine ⟨a, P, hPp, fun h => hPp.ne_top ?_, key⟩
  rw [Ideal.eq_top_iff_one, key, one_mul]
  exact h
end KrullHeightOne
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
