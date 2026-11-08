-- Prove2me | solution 1 for QEC.Coding.OriginalNormalizationComparison.ChartLocalization.tensorRingHom_ext_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:19:56.931439+00:00
-- url     : https://prove2.me/submissions/0f26e9bf-ce05-4d17-8510-d7a6c6e08190

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNormalizationComparison
import Mathlib.RingTheory.Localization.BaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLaurentNormalizationComparison

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.OriginalNormalizationComparison QEC.Coding.OriginalNormalizationComparison.ChartLocalization
open scoped TensorProduct
noncomputable section
variable {R S A D : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing D]
  [Algebra R S] [Algebra R A] [Algebra S D]
variable {P U V : Type*} [CommRing P] [CommRing U] [CommRing V]
  [Algebra U V] [Algebra D P]
variable [Algebra S U] [Algebra S V] [Algebra S P]
  [IsScalarTower S U V] [hDP : IsScalarTower S D P]
namespace QEC.Coding.OriginalNormalizationComparison.ChartLocalization
theorem _root_.solution {T : Type*} [CommRing T]
    (f h : S ⊗[R] A →+* T) (heq : ∀ c a, f (c ⊗ₜ[R] a) = h (c ⊗ₜ[R] a)) : f = h := by
  apply RingHom.ext
  intro x
  induction x with
  | zero => exact f.map_zero.trans h.map_zero.symm
  | add x y hx hy =>
    exact (f.map_add x y).trans
      ((congrArg₂ (· + ·) hx hy).trans (h.map_add x y).symm)
  | tmul c a => exact heq c a
end QEC.Coding.OriginalNormalizationComparison.ChartLocalization
