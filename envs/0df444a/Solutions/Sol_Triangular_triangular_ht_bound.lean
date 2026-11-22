-- Prove2me | solution 1 for Triangular.triangular_ht_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:11:07.585822+00:00
-- url     : https://prove2.me/submissions/fa25715d-7e6f-4a82-ba8e-7d47bb3bb997

module
public import Definitions.Def_Triangular_Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Definitions.Def_Triangular_Auto_Carleson
public import Definitions.Def_Triangular_Theorems
public import Theorems.Thm_Auto_triangular_ht_bound


set_option autoImplicit true
@[expose] public section
public section
open Triangular
open MeasureTheory SchwartzMap Topology Filter Function
namespace Triangular
theorem _root_.solution :
    ∃ C : ℝ, ∀ F₀ F₁ F₂ : 𝓢(ℝ × ℝ, ℂ),
      ‖T F₀ F₁ F₂‖ₑ ≤ ENNReal.ofReal C * eLpNorm F₀ 3 * eLpNorm F₁ 3 * eLpNorm F₂ 3 :=
  Auto.triangular_ht_bound
end Triangular
