-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_tens_central_cbb464e8d5bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:42:01.944142+00:00
-- url     : https://prove2.me/submissions/eff9101c-47fc-4462-bcda-5bc55d1ced55

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_tens_mul_c3492ccc8731
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_tens_single_731751eea0f3
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_commute_of_single_11fa7f76e614

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
theorem _root_.solution (x : ∀ i, MonoidAlgebra k (G i)) (h : ∀ i a, x i * a = a * x i)
    (a : MonoidAlgebra k (∀ i, G i)) : tens x * a = a * tens x := by
  classical
  refine commute_of_single _ (fun g => ?_) a
  rw [← tens_single, tens_mul, tens_mul]
  exact congrArg tens (funext fun i => h i _)
end Formalism.BasicNotions.Examples₂.NZ
