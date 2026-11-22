-- Prove2me | solution 1 for Triangular.classical_carleson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:29:30.193807+00:00
-- url     : https://prove2.me/submissions/3e73a1fc-ec3f-48e5-9a00-5ffb69fbc6d6

module
public import Definitions.Def_Triangular_Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Definitions.Def_Triangular_Auto_Carleson
public import Definitions.Def_Triangular_Theorems
public import Theorems.Thm_Auto_classical_carleson


set_option autoImplicit true
@[expose] public section
public section
open Triangular
open MeasureTheory SchwartzMap Topology Filter Function
namespace Triangular
theorem _root_.solution (f : ℝ → ℂ) (hf : Continuous f) (hper : Periodic f 1) :
    ∀ᵐ x, Tendsto (fun N ↦ fourierPartialSum f N x) atTop (𝓝 (f x)) :=
  Auto.classical_carleson f hf hper
end Triangular
