-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ArtinSchreier_ker_finrank
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:33:20.324963+00:00
-- url     : https://prove2.me/submissions/5e651d21-b55b-43bb-a19f-5965eb440048

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Field
import Mathlib.FieldTheory.Finite.Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
section
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
private theorem f256ArtinSchreier_ker_eq_trace_ker :
    LinearMap.ker f256ArtinSchreier = LinearMap.ker (Algebra.trace F16 F256) := by
  ext x
  simp only [LinearMap.mem_ker]
  rw [← algebraMap_trace_eq_f256ArtinSchreier]
  simp
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution :
    Module.finrank F16 (LinearMap.ker f256ArtinSchreier) = 1 := by
  rw [f256ArtinSchreier_ker_eq_trace_ker]
  have hrange : LinearMap.range (Algebra.trace F16 F256) = ⊤ :=
    LinearMap.range_eq_top.mpr (Algebra.trace_surjective F16 F256)
  have h := LinearMap.finrank_range_add_finrank_ker (Algebra.trace F16 F256)
  rw [hrange] at h
  simp only [finrank_top, Module.finrank_self, f256_finrank_over_f16] at h
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
