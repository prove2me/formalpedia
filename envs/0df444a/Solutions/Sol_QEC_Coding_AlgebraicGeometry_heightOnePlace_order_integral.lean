-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.heightOnePlace_order_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:31:26.04591+00:00
-- url     : https://prove2.me/submissions/23716a86-893e-4e6e-b758-8e1a1e61d5c2

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
    (H : IsDedekindDomain.HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    (heightOnePlace (k := k) (K := K) H).order (algebraMap R K r) =
      (multiplicity H.asIdeal (Ideal.span {r}) : ℤ) := by
  unfold heightOnePlace GlobalPlace.order
  rw [H.valuation_of_algebraMap, H.intValuation_eq_exp_neg_multiplicity hr,
    WithZero.log_exp]
  ring
end QEC.Coding.AlgebraicGeometry
