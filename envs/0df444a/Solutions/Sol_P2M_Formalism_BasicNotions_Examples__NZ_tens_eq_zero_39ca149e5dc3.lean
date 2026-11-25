-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_tens_eq_zero_39ca149e5dc3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:32:43.033802+00:00
-- url     : https://prove2.me/submissions/c052fb90-737c-4815-b604-96eec28a9820

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_tens_coeff_b71da958868c

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
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (x : ∀ i, MonoidAlgebra k (G i)) (i : I) (h : x i = 0) : tens x = 0 := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [tens_coeff]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; rfl)
end Formalism.BasicNotions.Examples₂.NZ
