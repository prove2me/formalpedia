-- Prove2me | solution 1 for PhosphorylationSharpness.sharp_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:34:36.644719+00:00
-- url     : https://prove2.me/submissions/bad516bb-a974-48d5-ac7e-560473afd166

import Definitions.Def_proofs_PhosphorylationSharpness_Assembly
import Definitions.Def_proofs_PhosphorylationSharpness_Resolution
import Theorems.Thm_PhosphorylationSharpness_attainment_succ

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology
namespace PhosphorylationSharpness
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) : Attains n (2*n-1) := by
  cases n with
  | zero => omega
  | succ m =>
    have h : 2*(m+1)-1=2*m+1 := by omega
    simpa only [Nat.succ_eq_add_one, h] using attainment_succ m
end PhosphorylationSharpness
