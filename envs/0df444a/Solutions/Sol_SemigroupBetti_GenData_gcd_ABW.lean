-- Prove2me | solution 1 for SemigroupBetti.GenData.gcd_ABW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:33:25.40203+00:00
-- url     : https://prove2.me/submissions/9ed8fed8-5ff5-4771-a1d0-8c524e32ae7b

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_GenData_g_dvd_a
public import Theorems.Thm_SemigroupBetti_GenData_g_dvd_b
public import Theorems.Thm_SemigroupBetti_GenData_g_dvd_w
public import Theorems.Thm_SemigroupBetti_GenData_g_pos

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : Nat.gcd G.A (Nat.gcd G.B G.W) = 1 := by
  have hbw : G.g ∣ Nat.gcd G.b G.w := Nat.dvd_gcd G.g_dvd_b G.g_dvd_w
  have h1 : Nat.gcd G.B G.W = Nat.gcd G.b G.w / G.g := Nat.gcd_div G.g_dvd_b G.g_dvd_w
  rw [A, h1, Nat.gcd_div G.g_dvd_a hbw]
  exact Nat.div_self G.g_pos
end SemigroupBetti.GenData
