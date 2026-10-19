-- Prove2me | solution 1 for PermanentRollout.homogeneousMapGradedQuotientMulLinearMap_finrank_quotient_add_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/466593be-0177-4309-b311-6e20cf1fde2b

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Finite ι] (I : Ideal (MvPolynomial ι ℂ))
    (f : MvPolynomial ι ℂ) {e : ℕ} (hf : f.IsHomogeneous e) (n : ℕ) :
    Module.finrank ℂ
        (homogeneousMapGradedQuotientPiece I (e + n) ⧸
          LinearMap.range
            (homogeneousMapGradedQuotientMulLinearMap I f hf n)) +
      Module.finrank ℂ (homogeneousMapGradedQuotientPiece I n) =
        Module.finrank ℂ (homogeneousMapGradedQuotientPiece I (e + n)) +
          Module.finrank ℂ
            (LinearMap.ker
              (homogeneousMapGradedQuotientMulLinearMap I f hf n)) := by
  letI : Module.Finite ℂ (MvPolynomial.homogeneousSubmodule ι ℂ n) :=
    (Submodule.fg_iff_finiteDimensional _).mp
      (MvPolynomial.homogeneousSubmodule_fg ι ℂ n)
  letI : Module.Finite ℂ (MvPolynomial.homogeneousSubmodule ι ℂ (e + n)) :=
    (Submodule.fg_iff_finiteDimensional _).mp
      (MvPolynomial.homogeneousSubmodule_fg ι ℂ (e + n))
  let m := homogeneousMapGradedQuotientMulLinearMap I f hf n
  have hrange :=
    Submodule.finrank_quotient_add_finrank (LinearMap.range m)
  have hkernel := LinearMap.finrank_range_add_finrank_ker m
  dsimp [m] at hrange hkernel
  omega
end PermanentRollout
