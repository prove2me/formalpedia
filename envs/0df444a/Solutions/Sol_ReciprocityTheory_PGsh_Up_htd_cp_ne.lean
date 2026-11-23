-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.htd_cp_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:32.215114+00:00
-- url     : https://prove2.me/submissions/9f43634b-f170-4c2c-9adb-5244f0a1147e

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hS : HodgeTateSetting p v R O σ cp) : cp ≠ 0 := by
  intro h
  have h1 := hS.cp_val
  rw [h, map_zero, map_zero, zero_pow] at h1
  · exact hS.p_ne h1.symm
  · have := (Fact.out : p.Prime).two_le
    omega
end ReciprocityTheory.PGsh.Up
