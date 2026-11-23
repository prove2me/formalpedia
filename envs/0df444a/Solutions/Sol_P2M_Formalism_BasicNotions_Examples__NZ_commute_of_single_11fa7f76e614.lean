-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_commute_of_single_11fa7f76e614
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:22.739392+00:00
-- url     : https://prove2.me/submissions/fe2b4867-2bc7-45cc-a270-967f1e026418

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
theorem _root_.solution {Γ : Type} [Group Γ] (z : MonoidAlgebra k Γ)
    (h : ∀ g : Γ, z * single g 1 = single g 1 * z) (a : MonoidAlgebra k Γ) : z * a = a * z := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]
  | single g r =>
    have e : (single g r : MonoidAlgebra k Γ) = r • single g 1 := by rw [smul_single', mul_one]
    rw [e, mul_smul_comm, smul_mul_assoc, h]
end Formalism.BasicNotions.Examples₂.NZ
