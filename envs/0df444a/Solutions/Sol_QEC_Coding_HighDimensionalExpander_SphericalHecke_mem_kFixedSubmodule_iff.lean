-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.mem_kFixedSubmodule_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:53:56.472485+00:00
-- url     : https://prove2.me/submissions/6077021d-d6f3-4b31-8564-f0acafab2452

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalRepresentation

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open MeasureTheory
open scoped ComplexConjugate MatrixGroups LocalTopology
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) (v : V) :
    v ∈ kFixedSubmodule rho ↔
      ∀ h : maximalCompact k d, rho h v = v :=
  Iff.rfl
end QEC.Coding.HighDimensionalExpander.SphericalHecke
