-- Prove2me | solution 1 for SNumbers.Multiplicative.idealLike
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:17:47.636006+00:00
-- url     : https://prove2.me/submissions/dfaaa58f-369c-4edd-b535-0eb89210f202

module
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Definitions.Def_SNumbers_Basic

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
namespace SNumbers
namespace Multiplicative
theorem _root_.solution {s : Family 𝕜} (h : Multiplicative s) (h0 : NormAtZero s) :
    IdealLike s := by
  intro W X Y Z _ _ _ _ _ _ _ _ A S B n
  have hSA : s (S.comp A) n ≤ s S n * ‖A‖ := by
    have h' := h S A n 0
    rwa [Nat.add_zero, h0 A] at h'
  have hB : s (B.comp (S.comp A)) n ≤ ‖B‖ * s (S.comp A) n := by
    have h' := h B (S.comp A) 0 n
    rwa [Nat.zero_add, h0 B] at h'
  calc s (B.comp (S.comp A)) n
      ≤ ‖B‖ * s (S.comp A) n := hB
    _ ≤ ‖B‖ * (s S n * ‖A‖) := mul_le_mul_of_nonneg_left hSA (norm_nonneg B)
    _ = ‖B‖ * s S n * ‖A‖ := (mul_assoc _ _ _).symm
end Multiplicative
end SNumbers
