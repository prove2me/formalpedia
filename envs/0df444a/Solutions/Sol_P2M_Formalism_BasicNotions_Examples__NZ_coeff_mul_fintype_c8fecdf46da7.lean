-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_coeff_mul_fintype_c8fecdf46da7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:22.051027+00:00
-- url     : https://prove2.me/submissions/544fb660-77fa-4c27-aedf-7e1482ea2ea7

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
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {Γ : Type} [Group Γ] [Fintype Γ] (x y : MonoidAlgebra k Γ) (g : Γ) :
    (x * y).coeff g = ∑ h, x.coeff h * y.coeff (h⁻¹ * g) := by
  rw [coeff_mul_apply_left, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
end Formalism.BasicNotions.Examples₂.NZ
