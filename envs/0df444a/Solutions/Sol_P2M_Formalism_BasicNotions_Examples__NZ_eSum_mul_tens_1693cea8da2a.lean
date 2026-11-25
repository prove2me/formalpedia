-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_eSum_mul_tens_1693cea8da2a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:51:39.109332+00:00
-- url     : https://prove2.me/submissions/8e5b5044-74bc-46d7-a35e-1fdd54a77de4

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_tens_mul_tens_59d725813d88

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
theorem _root_.solution (b : ∀ i, L i) : eSum E S * tens (fun i => E i (b i)) =
    open Classical in if S b then tens (fun i => E i (b i)) else 0 := by
  classical
  unfold eSum
  rw [Finset.sum_mul, Finset.sum_eq_single b]
  · split_ifs
    · rw [tens_mul_tens E hidem horth, if_pos rfl]
    · simp
  · intro a _ hab
    split_ifs
    · rw [tens_mul_tens E hidem horth, if_neg hab]
    · simp
  · intro h; exact absurd (Finset.mem_univ b) h
end Formalism.BasicNotions.Examples₂.NZ
