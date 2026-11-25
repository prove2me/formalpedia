-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplReducePosDef_proof_0a31a9219869
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:08.633824+00:00
-- url     : https://prove2.me/submissions/b5b7af39-ebe0-4811-9aef-1dac0ef61330

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplReducePosDef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReducePosDef_sum_mul_symplCons_68553baf88f1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open PSymplReducePosDef
namespace GroundTheory.Heights₂.Heights
namespace SymplReducePosDef
theorem _root_.solution : SymplReducePosDef.Statement := by
  intro n H hH
  have hsymm : ∀ i j, H j i = H i j := fun i j => by
    simpa using hH.isHermitian.apply i j
  have hpos : 0 < H (Sum.inl 0) (Sum.inl 0) := hH.diag_pos
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · refine Matrix.IsHermitian.ext fun a b => ?_
    simp only [symplReduce, star_trivial]
    rw [hsymm (Sum.map Fin.succ Fin.succ a), hsymm (Sum.map Fin.succ Fin.succ a) (Sum.inl 0),
      hsymm (Sum.inl 0) (Sum.map Fin.succ Fin.succ b)]
    ring
  · intro x hx
    simp only [star_trivial]
    set h := H (Sum.inl 0) (Sum.inl 0) with hh
    set S := ∑ b, H (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) * x b with hS
    set Q := ∑ a, (∑ b, H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) * x b) * x a
      with hQ
    have hT : ∑ a, x a * H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) = S := by
      rw [hS]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hsymm]; ring
    have hy : symplCons (-(S / h)) 0 x ≠ 0 := by
      intro hz
      apply hx
      funext q
      have := congrFun hz (Sum.map Fin.succ Fin.succ q)
      cases q <;> simpa [symplCons] using this
    have h1 := hH.dotProduct_mulVec_pos hy
    simp only [star_trivial] at h1
    have hL : symplCons (-(S / h)) 0 x ⬝ᵥ (H *ᵥ symplCons (-(S / h)) 0 x) =
        (h * (-(S / h)) + S) * (-(S / h)) + (-(S / h)) * S + Q := by
      rw [dotProduct_comm]
      simp only [dotProduct, mulVec, sum_mul_symplCons]
      rw [← hh, ← hS]
      simp only [add_mul, Finset.sum_add_distrib]
      rw [← hQ]
      have hc : ∑ q, H (Sum.map Fin.succ Fin.succ q) (Sum.inl 0) * (-(S / h)) * x q =
          (-(S / h)) * S := by
        rw [← hT, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
      rw [hc]
      ring
    have hRa : ∀ a, ∑ b, (H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) -
        H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) * H (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) /
          h) * x b =
        ∑ b, H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) * x b -
          H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) / h * S := by
      intro a
      rw [hS, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    have hR : x ⬝ᵥ (symplReduce H *ᵥ x) = Q - S / h * S := by
      simp only [dotProduct, mulVec, symplReduce]
      rw [← hh]
      simp only [hRa, mul_sub, Finset.sum_sub_distrib]
      rw [hQ, ← hT, Finset.sum_div, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun a _ => ?_
        ring
      · refine Finset.sum_congr rfl fun a _ => ?_
        ring
    have hne : h ≠ 0 := hpos.ne'
    have key : symplCons (-(S / h)) 0 x ⬝ᵥ (H *ᵥ symplCons (-(S / h)) 0 x) =
        x ⬝ᵥ (symplReduce H *ᵥ x) := by
      rw [hL, hR]
      field_simp
      ring
    rw [← key]
    exact h1
end SymplReducePosDef
end GroundTheory.Heights₂.Heights
