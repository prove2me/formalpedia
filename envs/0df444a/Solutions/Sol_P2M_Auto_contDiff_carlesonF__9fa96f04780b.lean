-- Prove2me | solution 1 for P2M_Auto_contDiff_carlesonF__9fa96f04780b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:01:31.991023+00:00
-- url     : https://prove2.me/submissions/36c954f2-a309-43a3-951b-5eecf2f54e36

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_contDiff_ofReal_comp
public import Theorems.Thm_Auto_contDiff_exp_comp

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution {a ν : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hν : ContDiff ℝ ∞ ν) (σ : ℝ) :
    ContDiff ℝ ∞ (carlesonF₂ a ν σ) := by
  have hb : ContDiff ℝ ∞ (carlesonBump₁ : ℝ → ℝ) := carlesonBump₁.contDiff (n := ⊤)
  unfold carlesonF₂
  refine ((contDiff_ofReal_comp ?_).mul (contDiff_exp_comp ?_)).mul (contDiff_ofReal_comp ?_)
    <;> fun_prop
end Auto
