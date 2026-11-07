-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.FiniteGeometry.map_generalLinear_eq_map_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:20:53.122925+00:00
-- url     : https://prove2.me/submissions/1e0d1417-073e-47aa-92ed-4599c0b1cf2d

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module
namespace QEC.Coding.HighDimensionalExpander.FiniteGeometry
theorem _root_.solution
    (k : Type*) [Field k] (d : ℕ)
    (P : Submodule k (Fin d → k)) (a b : GL (Fin d) k) :
    P.map (Matrix.GeneralLinearGroup.toLin a).val =
        P.map (Matrix.GeneralLinearGroup.toLin b).val ↔
      P.map (Matrix.GeneralLinearGroup.toLin (a⁻¹ * b)).val = P := by
  have hcomp (x y : GL (Fin d) k) :
      (Matrix.GeneralLinearGroup.toLin x).val.comp
          (Matrix.GeneralLinearGroup.toLin y).val =
        (Matrix.GeneralLinearGroup.toLin (x * y)).val := by
    ext v i
    simp
  have hone : (Matrix.GeneralLinearGroup.toLin (1 : GL (Fin d) k)).val =
      LinearMap.id := by
    ext v i
    simp
  constructor
  · intro h
    have hc := congrArg
      (fun Q : Submodule k (Fin d → k) =>
        Q.map (Matrix.GeneralLinearGroup.toLin a⁻¹).val) h
    rw [← Submodule.map_comp, hcomp, ← Submodule.map_comp, hcomp] at hc
    have hia : a⁻¹ * a = 1 := by group
    rw [hia] at hc
    rw [hone, Submodule.map_id] at hc
    exact hc.symm
  · intro h
    have hc := congrArg
      (fun Q : Submodule k (Fin d → k) =>
        Q.map (Matrix.GeneralLinearGroup.toLin a).val) h
    rw [← Submodule.map_comp, hcomp] at hc
    have hab : a * (a⁻¹ * b) = b := by group
    rw [hab] at hc
    simpa using hc.symm
end QEC.Coding.HighDimensionalExpander.FiniteGeometry
