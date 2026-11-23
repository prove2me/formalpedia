-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.vp_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:59.803852+00:00
-- url     : https://prove2.me/submissions/52375bd8-8987-43b1-9901-ef6fa0611fa0

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
theorem _root_.solution (hS : HodgeTateSetting p v R O σ cp) (d : ℕ) :
    (v (algebraMap R C (p : R)) : ℝ) ^ ((d : ℝ) / (p - 1)) =
      ((v (algebraMap R C cp) ^ d : NNReal) : ℝ) := by
  have hp := (Fact.out : p.Prime).two_le
  have h1 : ((v (algebraMap R C (p : R)) : NNReal) : ℝ) =
      ((v (algebraMap R C cp) : ℝ)) ^ ((p : ℝ) - 1) := by
    rw [← hS.cp_val]
    push_cast
    rw [← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub (by omega)]
    simp
  have hne : ((p : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have h2 : ((p : ℝ) - 1) * ((d : ℝ) / ((p : ℝ) - 1)) = d := by
    field_simp
  rw [h1, ← Real.rpow_mul (by positivity), h2]
  push_cast
  rw [Real.rpow_natCast]
end ReciprocityTheory.PGsh.Up
