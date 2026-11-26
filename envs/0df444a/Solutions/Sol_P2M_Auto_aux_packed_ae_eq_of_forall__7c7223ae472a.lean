-- Prove2me | solution 1 for P2M_Auto_aux_packed_ae_eq_of_forall__7c7223ae472a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:08:00.018574+00:00
-- url     : https://prove2.me/submissions/ca3e752d-0008-4c3d-ac26-7f8000940cc2

module
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Definitions.Def_LeanNct_Auto_MultilinearInterpolation

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto
namespace Auto
theorem _root_.solution {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f g : Fin J → X → ℂ}
    (hfg : ∀ j, f j =ᵐ[μ] g j) :
    (fun z : Fin J × X ↦ f z.1 z.2) =ᵐ[(Measure.count : Measure (Fin J)).prod μ]
      fun z ↦ g z.1 z.2 := by
  change ∀ᵐ z : Fin J × X ∂((Measure.count : Measure (Fin J)).prod μ), f z.1 z.2 = g z.1 z.2
  rw [ae_iff]
  let N : Fin J → Set X := fun j ↦ {x | f j x ≠ g j x}
  have hN (j : Fin J) : μ (N j) = 0 := by
    simpa only [N, ne_eq, not_not] using (ae_iff.mp (hfg j))
  have hrect (j : Fin J) :
      ((Measure.count : Measure (Fin J)).prod μ) ({j} ×ˢ N j) = 0 := by
    apply le_zero_iff.mp
    calc
      ((Measure.count : Measure (Fin J)).prod μ) ({j} ×ˢ N j) ≤
          Measure.count {j} * μ (N j) := MeasureTheory.Measure.prod_prod_le _ _
      _ = 0 := by rw [hN, mul_zero]
  have hsubset : {z : Fin J × X | f z.1 z.2 ≠ g z.1 z.2} ⊆ ⋃ j, {j} ×ˢ N j := by
    intro z hz
    refine Set.mem_iUnion.2 ⟨z.1, ?_⟩
    exact ⟨rfl, hz⟩
  exact nonpos_iff_eq_zero.mp
    ((measure_mono hsubset).trans_eq (MeasureTheory.measure_iUnion_null hrect))
end Auto
