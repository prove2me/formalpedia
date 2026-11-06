-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.scalarRingEquiv_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:23.757947+00:00
-- url     : https://prove2.me/submissions/853cb31e-a6ff-4b14-8c3f-f80769d38f90

import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Scheme
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_StalkScalars

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (R B : CommRingCat) (T : Type*) (A : T → CommRingCat)
    (s : ∀ t, R →+* A t) {t t' : T} (h : t = t') (e : A t' ≃+* B) (r : R) :
    (Eq.mpr (congrArg (fun z => A z ≃+* B) h) e) (s t r) = e (s t' r) := by
  cases h
  rfl
end QEC.Coding.AlgebraicGeometry
