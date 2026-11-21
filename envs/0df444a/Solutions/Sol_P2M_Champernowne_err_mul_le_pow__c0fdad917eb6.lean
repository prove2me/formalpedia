-- Prove2me | solution 1 for P2M_Champernowne_err_mul_le_pow__c0fdad917eb6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:54.231707+00:00
-- url     : https://prove2.me/submissions/09ce90ba-3690-4741-963b-b1f8d47bf77f

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
public import Theorems.Thm_Champernowne_err_mul_le_pow

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
open Filter Asymptotics Topology
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (n : ℕ) (w : List ℕ) (h2 : 2 ≤ champM b n) :
    7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n * ((b - 1) * champM b n)
      ≤ 2 * (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ 2) * n := by
  have hF := err_mul_le_pow hb n w
  have h9 : (b - 1) * champM b n ≤ 2 * ((b - 1) * (champM b n - 1)) := by
    calc (b - 1) * champM b n ≤ (b - 1) * (2 * (champM b n - 1)) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = 2 * ((b - 1) * (champM b n - 1)) := by ring
  calc 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n * ((b - 1) * champM b n)
      ≤ 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n
        * (2 * ((b - 1) * (champM b n - 1))) := Nat.mul_le_mul_left _ h9
  _ = 2 * (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n
        * ((b - 1) * (champM b n - 1))) := by ring
  _ ≤ 2 * ((7 * (w.length + 1) * b ^ (2 * w.length) * b ^ 2) * n) :=
      Nat.mul_le_mul_left _ hF
  _ = 2 * (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ 2) * n := by ring
end Champernowne
