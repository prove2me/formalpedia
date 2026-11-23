-- Prove2me | solution 1 for SumProduct.idealCount_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:59:51.217682+00:00
-- url     : https://prove2.me/submissions/04980b0f-f9ed-4607-bec3-06c6a8c67262

import Mathlib
import Definitions.Def_SumProduct_EulerBound

set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]
namespace SumProduct
theorem _root_.solution : idealCount K 1 = 1 := by
  rw [idealCount, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun I J => ?_⟩, ⟨⟨⊤, Ideal.absNorm_top⟩⟩⟩
  obtain ⟨I, hI⟩ := I
  obtain ⟨J, hJ⟩ := J
  simp only [Subtype.mk_eq_mk]
  rw [Ideal.absNorm_eq_one_iff.mp hI, Ideal.absNorm_eq_one_iff.mp hJ]
end SumProduct
