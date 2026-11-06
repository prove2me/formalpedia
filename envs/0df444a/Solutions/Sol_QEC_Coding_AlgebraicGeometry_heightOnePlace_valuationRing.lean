-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.heightOnePlace_valuationRing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:49:23.064062+00:00
-- url     : https://prove2.me/submissions/ed7437f4-fbeb-4c08-b003-98eea8b859a8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra k K] [Algebra R K] [IsFractionRing R K]
    (H : IsDedekindDomain.HeightOneSpectrum R) :
    H.valuationSubringAtPrime K = (heightOnePlace (k := k) (K := K) H).valuationRing :=
  H.valuationSubringAtPrime_eq_valuationSubring
end QEC.Coding.AlgebraicGeometry
