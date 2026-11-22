-- Prove2me | solution 1 for P2M_Auto_contDiff_carlesonF__cb1ce9767a4b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:45:15.472617+00:00
-- url     : https://prove2.me/submissions/6406b2ea-ebb0-4711-89a6-969e62e9fab2

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_contDiff_ofReal_comp

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (carlesonF₁ g) := by
  have hb : ContDiff ℝ ∞ (carlesonBump₁ : ℝ → ℝ) := carlesonBump₁.contDiff (n := ⊤)
  unfold carlesonF₁
  refine (hg.comp (by fun_prop)).mul (contDiff_ofReal_comp ?_)
  fun_prop
end Auto
