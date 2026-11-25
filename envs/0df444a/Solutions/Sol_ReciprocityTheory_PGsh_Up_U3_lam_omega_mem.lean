-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.lam_omega_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:45:11.49195+00:00
-- url     : https://prove2.me/submissions/f54dfd34-36cf-4efa-b022-e8ff1698d07c

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_wt_int
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_lam_scale
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_cmul_mem
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_scale_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
variable (hv : v.Integers R)
include hv
variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution (AA : HopfOrder (C := C) R (ZMod p)) {f : ZMod p → C}
    (hf : f ∈ AA.carrier) : (fun t => lam ω f * ω t) ∈ AA.carrier := by
  have hS : v (sS ω) ≤ 1 := by
    unfold sS
    exact v.map_sum_le fun b _ => hω.wt_int b
  have hu : ∀ a, v (u0 ω a) ≤ 1 := fun a => by
    unfold u0
    split_ifs
    · exact (v.map_sub _ _).trans (max_le (hω.wt_int a) hS)
    · rw [sub_zero]
      exact hω.wt_int a
  have key : (fun t => lam ω f * ω t) = ∑ a, (fun t => u0 ω a * f (a * t)) := by
    funext t
    simp only [Finset.sum_apply, lam]
    rw [mul_comm (∑ a, u0 ω a * f a) (ω t), ← hω.lam_scale f t]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm t a]
  rw [key]
  exact Submodule.sum_mem _ fun a _ => cmul_mem hv AA.carrier (hu a) (scale_mem AA hf a)
end ReciprocityTheory.PGsh.Up.U3
