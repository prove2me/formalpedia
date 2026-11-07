-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeRightIndex_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:45:03.007867+00:00
-- url     : https://prove2.me/submissions/cf5092b9-887e-4926-a1b2-65acc162f90f

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) (i : Option (Fin p)) :
    ∃ δ : SL(2,ℤ), δ∈CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperMatrix p i*(γ:Matrix (Fin 2) (Fin 2) ℤ)=
        (δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p (lpsHeckeRightIndex N p hNp γ hγ i) :=
  (lpsHeckeRightFactor N p hNp γ hγ i).choose_spec
end QEC.Coding.TannerLiftedProduct
