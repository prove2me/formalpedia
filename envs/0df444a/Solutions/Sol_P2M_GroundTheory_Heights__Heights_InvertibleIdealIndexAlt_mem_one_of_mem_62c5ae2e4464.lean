-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mem_one_of_mem_62c5ae2e4464
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T05:44:43.012849+00:00
-- url     : https://prove2.me/submissions/306adea4-0eb1-4280-9123-77ed639d19dc

import Mathlib
open NumberField
variable {L : Type} [Field L]


theorem solution [NumberField L] {B : Subring L} [Module.Finite ℤ B] {b : L} (hb : b ∈ B) :
    b ∈ (1 : Submodule (𝓞 L) L) := by
  have hi : IsIntegral ℤ (⟨b,hb⟩ : B) := Algebra.IsIntegral.isIntegral _
  have hbint : IsIntegral ℤ b := hi.algebraMap (B := L)
  exact Submodule.mem_one.mpr ⟨⟨b,hbint⟩,rfl⟩
