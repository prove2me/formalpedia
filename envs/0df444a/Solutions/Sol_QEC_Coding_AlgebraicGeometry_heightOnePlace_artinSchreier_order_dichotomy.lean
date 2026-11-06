-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.heightOnePlace_artinSchreier_order_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:30:49.479495+00:00
-- url     : https://prove2.me/submissions/86eb326d-214e-4dea-8484-393d566edb98

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_artinSchreier_order_dichotomy_of_finrank_le_two

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra k K] [Algebra k L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra R S] [FaithfulSMul R S] [Module.Finite R S]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    (H : IsDedekindDomain.HeightOneSpectrum R)
    (J : IsDedekindDomain.HeightOneSpectrum S) [J.asIdeal.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2)
    (ha : (heightOnePlace (k := k) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := k) (K := K) H).order a) :
    (heightOnePlace (k := k) (K := L) J).order y = -1 ∨
      0 ≤ (heightOnePlace (k := k) (K := L) J).order y := by
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; norm_num)
  exact heightOnePlace_artinSchreier_order_dichotomy_of_finrank_le_two
    H J a y hy hdegree.le ha
end QEC.Coding.AlgebraicGeometry
