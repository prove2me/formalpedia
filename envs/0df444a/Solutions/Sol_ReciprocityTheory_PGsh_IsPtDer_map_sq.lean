-- Prove2me | solution 1 for ReciprocityTheory.PGsh.IsPtDer.map_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:31:19.162403+00:00
-- url     : https://prove2.me/submissions/03f51985-a6f5-4bee-8578-3bd9c10e8dfa

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
theorem _root_.solution {δ : A →ₗ[R] R} (hδ : IsPtDer δ) {f : A}
    (hf : f ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2) : δ f = 0 := by
  rw [pow_two] at hf
  refine Submodule.mul_induction_on hf ?_ ?_
  · intro a ha b hb
    rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at ha hb
    rw [hδ, ha, hb]; ring
  · intro a b ha hb; rw [map_add, ha, hb, add_zero]
end IsPtDer
end ReciprocityTheory.PGsh
