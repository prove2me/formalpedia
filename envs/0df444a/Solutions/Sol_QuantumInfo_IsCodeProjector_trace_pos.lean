-- Prove2me | solution 1 for QuantumInfo.IsCodeProjector.trace_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:49:56.788191+00:00
-- url     : https://prove2.me/submissions/db2cc2fc-a9c2-43ac-b345-8e32bb93769f

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_IsCodeProjector_posSemidef

set_option autoImplicit false
@[expose] public section
public section
open Matrix Unitary
open scoped ComplexOrder ComplexConjugate
open QuantumInfo
variable {n : Type*} [Fintype n]
open QuantumInfo.IsCodeProjector
variable {P : Matrix n n ℂ} (hP : IsCodeProjector P)
include hP
namespace QuantumInfo.IsCodeProjector
theorem _root_.solution (hP0 : P ≠ 0) : 0 < P.trace :=
  lt_of_le_of_ne hP.posSemidef.trace_nonneg
    fun h => hP0 (hP.posSemidef.trace_eq_zero_iff.mp h.symm)
end QuantumInfo.IsCodeProjector
