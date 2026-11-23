-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.residue_eq_zero_iff_norm_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:07.653798+00:00
-- url     : https://prove2.me/submissions/fb5c3474-379e-49bc-99c5-a9d051316408

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsTorusPointOneLeNormSum
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_mem_unitBallRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type*} [NormedField K] [IsUltrametricDist K]
    (x : unitBallRing K) :
    IsLocalRing.residue (unitBallRing K) x = 0 ↔ ‖(x : K)‖ < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hx1 : ‖(x : K)‖ ≤ 1 := (mem_unitBallRing (x : K)).1 x.2
  constructor
  · intro hnu
    refine lt_of_le_of_ne hx1 fun h1 => hnu ?_
    have hx0 : (x : K) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    have hinv : (x : K)⁻¹ ∈ unitBallRing K := by
      rw [mem_unitBallRing, norm_inv, h1, inv_one]
    have hm : x * ⟨(x : K)⁻¹, hinv⟩ = 1 := Subtype.ext (by simp [hx0])
    exact ⟨⟨x, ⟨(x : K)⁻¹, hinv⟩, hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  · intro hlt hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have h := congrArg (fun t : unitBallRing K => ‖(t : K)‖) hy
    first
    | simp only [MulMemClass.coe_mul, OneMemClass.coe_one, norm_mul, norm_one] at h
    | simp at h
    have hy1 : ‖(y : K)‖ ≤ 1 := (mem_unitBallRing (y : K)).1 y.2
    nlinarith [norm_nonneg (x : K), norm_nonneg (y : K)]
end ReciprocityTheory.MultiplicativeHeights
