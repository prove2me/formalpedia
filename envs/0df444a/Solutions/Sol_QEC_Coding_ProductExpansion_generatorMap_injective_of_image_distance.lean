-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.generatorMap_injective_of_image_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:02:02.149053+00:00
-- url     : https://prove2.me/submissions/453ba895-bdc2-4632-965e-f46cb85002fb

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype F] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (g : Matrix R W F) (d : Nat) (hPositive : 0 < d)
    (hImage : ∀ a : Word F R, a ≠ 0 →
      d ≤ HammingWeight (g.transpose.mulVec a)) :
    Function.Injective (fun a : Word F R => g.transpose.mulVec a) := by
  intro a b hab
  change g.transpose.mulVec a = g.transpose.mulVec b at hab
  apply sub_eq_zero.mp
  by_contra hne
  have hzero : g.transpose.mulVec (a - b) = 0 := by
    rw [Matrix.mulVec_sub, hab, sub_self]
  have hWeight := hImage (a - b) hne
  rw [hzero, HammingWeight_zero] at hWeight
  omega
end QEC.Coding.ProductExpansion
