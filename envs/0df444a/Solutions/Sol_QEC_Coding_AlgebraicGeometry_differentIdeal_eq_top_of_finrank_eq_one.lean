-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.differentIdeal_eq_top_of_finrank_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:51:54.214197+00:00
-- url     : https://prove2.me/submissions/1b896bc4-7714-4ded-a270-75301bdaccbc

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Mathlib.RingTheory.DedekindDomain.Different
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (B C K L : Type*) [CommRing B] [CommRing C] [Field K] [Field L]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra B C] [Algebra C L] [IsFractionRing C L] [IsScalarTower B C L]
    [Module.IsTorsionFree B C] [Module.Finite B C]
    [Algebra.IsSeparable K L]
include K L
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (hdegree : Module.finrank K L = 1) : differentIdeal B C = ⊤ := by
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; norm_num)
  have hgen : Algebra.adjoin K ({algebraMap C L (0 : C)} : Set L) = ⊤ := by
    simpa using (Subalgebra.bot_eq_top_of_finrank_eq_one hdegree)
  have hmem := aeval_derivative_mem_differentIdeal B K L (0 : C) hgen
  have hminpoly : minpoly B (0 : C) = Polynomial.X := by
    simpa using minpoly.eq_X_sub_C_of_algebraMap_inj (0 : B)
      (FaithfulSMul.algebraMap_injective B C)
  apply (differentIdeal B C).eq_top_iff_one.mpr
  simpa only [hminpoly, Polynomial.derivative_X, map_one] using hmem
end QEC.Coding.AlgebraicGeometry
