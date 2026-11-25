-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_eSum_idem_d70afd6df18d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:29:29.47821+00:00
-- url     : https://prove2.me/submissions/4b42bbb2-ed21-4dc0-bfb0-1cfc3bc42b6b

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_eSum_mul_tens_1693cea8da2a

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
theorem _root_.solution : eSum E S * eSum E S = eSum E S := by
  classical
  conv_lhs => rhs; unfold eSum
  rw [Finset.mul_sum]
  unfold eSum
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with hb
  · have := eSum_mul_tens E S hidem horth b
    rw [if_pos hb] at this
    exact this
  · simp
end Formalism.BasicNotions.Examples₂.NZ
