-- Prove2me | solution 1 for ReciprocityTheory.PGsh.IsPtDer.map_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:04.071475+00:00
-- url     : https://prove2.me/submissions/4dc76fc8-ca96-4089-aafb-c08bea18fa59

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
namespace ReciprocityTheory.PGsh
namespace IsPtDer
theorem _root_.solution {δ : A →ₗ[R] R} (hδ : IsPtDer δ) : δ 1 = 0 := by
  have h := hδ 1 1
  simp only [mul_one, Bialgebra.counit_one, one_mul] at h
  linear_combination -h
end IsPtDer
end ReciprocityTheory.PGsh
