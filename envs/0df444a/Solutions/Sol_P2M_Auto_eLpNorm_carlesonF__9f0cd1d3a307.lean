-- Prove2me | solution 1 for P2M_Auto_eLpNorm_carlesonF__9f0cd1d3a307
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:48:32.441003+00:00
-- url     : https://prove2.me/submissions/203f46ae-c278-48bb-8d5d-81d6436329fd

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution {a ν : ℝ → ℝ} (ha : Measurable a) (hν : Measurable ν) (σ : ℝ) :
    eLpNorm (carlesonF₂ a ν σ) 3 volume = eLpNorm (carlesonF₂ a ν 1) 3 volume := by
  have hb := carlesonBump₁.continuous.measurable
  exact eLpNorm_congr_norm_ae
    (ae_of_all _ fun p => by simp only [carlesonF₂, norm_mul, Complex.norm_exp_ofReal_mul_I])
end Auto
