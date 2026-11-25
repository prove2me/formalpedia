-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_tens_mul_tens_59d725813d88
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:42:03.171843+00:00
-- url     : https://prove2.me/submissions/aff1fae2-d03a-4f0f-bfe9-fa2855c80ed4

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_tens_mul_c3492ccc8731
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_tens_eq_zero_39ca149e5dc3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open MonoidAlgebra
variable {k : Type} [Field k] {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
variable {L : I → Type} [∀ i, Fintype (L i)] [DecidableEq I] (E : ∀ i, L i → MonoidAlgebra k (G i))
  (S : (∀ i, L i) → Prop)
variable (hidem : ∀ i l, E i l * E i l = E i l) (hcen : ∀ i l a, E i l * a = a * E i l)
  (horth : ∀ i l l', l ≠ l' → E i l * E i l' = 0)
include hidem horth
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (a b : ∀ i, L i) : tens (fun i => E i (a i)) * tens (fun i => E i (b i)) =
    open Classical in if a = b then tens (fun i => E i (a i)) else 0 := by
  rw [tens_mul]
  split_ifs with e
  · subst e; exact congrArg tens (funext fun i => hidem i _)
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp e
    exact tens_eq_zero _ i (horth i _ _ hi)
end Formalism.BasicNotions.Examples₂.NZ
