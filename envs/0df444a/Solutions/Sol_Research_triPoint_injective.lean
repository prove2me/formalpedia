-- Prove2me | solution 1 for Research.triPoint_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:17:13.774031+00:00
-- url     : https://prove2.me/submissions/ea9e459d-261b-45fb-b74e-a948c4ec7574

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells

set_option autoImplicit true
@[expose] public section
public section
open Research
namespace Research
theorem _root_.solution : Function.Injective triPoint := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have hy := congrArg Prod.snd h
  simp only [triPoint] at hy
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hbdR : (b : ℝ) = (d : ℝ) := by nlinarith
  have hbd : b = d := by exact_mod_cast hbdR
  subst d
  have hx := congrArg Prod.fst h
  simp only [triPoint] at hx
  have hacR : (a : ℝ) = (c : ℝ) := by nlinarith
  have hac : a = c := by exact_mod_cast hacR
  subst c
  rfl
end Research
