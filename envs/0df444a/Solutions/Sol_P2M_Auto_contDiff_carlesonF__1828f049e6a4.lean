-- Prove2me | solution 1 for P2M_Auto_contDiff_carlesonF__1828f049e6a4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:45:13.341518+00:00
-- url     : https://prove2.me/submissions/d4920c34-1aa5-47e4-879a-b3325752fd56

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
    ContDiff ℝ ∞ (carlesonF₀ a ν σ) := by
  have hb : ContDiff ℝ ∞ (carlesonBump₀ : ℝ → ℝ) := carlesonBump₀.contDiff (n := ⊤)
  unfold carlesonF₀
  refine ((contDiff_ofReal_comp ?_).mul (contDiff_exp_comp ?_)).mul (contDiff_ofReal_comp ?_)
    <;> fun_prop
end Auto
