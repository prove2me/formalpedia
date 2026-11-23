-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_eSum_coeff_c97526e39ca4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:22.78405+00:00
-- url     : https://prove2.me/submissions/a1cdf020-b9a3-42c9-9e04-24053d3bfa97

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD

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
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (g : ∀ i, G i) : (eSum E S).coeff g =
    open Classical in ∑ a : (∀ i, L i), if S a then ∏ i, (E i (a i)).coeff (g i) else 0 := by
  classical
  unfold eSum
  rw [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rfl
  · rfl
end Formalism.BasicNotions.Examples₂.NZ
