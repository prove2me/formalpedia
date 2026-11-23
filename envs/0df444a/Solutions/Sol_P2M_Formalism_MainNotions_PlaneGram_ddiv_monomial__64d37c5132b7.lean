-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_ddiv_monomial__64d37c5132b7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:52:52.746997+00:00
-- url     : https://prove2.me/submissions/eff41b72-9b83-4cdb-b2fd-1cdce71e2b18

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
section Gen
variable {σ : Type} [Fintype σ]
private theorem finsupp_prod_choose_eq_bin_of_le (M α : σ →₀ ℕ) (h : M ≤ α) :
    (α.prod fun x k => (k.choose (M x) : K)) = bin M α := by
  unfold bin Finsupp.prod
  refine Finset.prod_subset (Finset.subset_univ _) fun x _ hx => ?_
  have h0 : α x = 0 := by simpa using hx
  have hle : M x ≤ α x := by
    exact Finsupp.le_def.1 h x
  have h1 : M x = 0 := by omega
  simp [h0, h1]
end Gen
section Letter
variable {L : Type} [DecidableEq L] {r : ℕ}
end Letter
section Der
variable [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ)
end Der
section App
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}
variable {I : Type} [Fintype I]
end App
section AppL
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} {I : Type} [Fintype I]
end AppL
namespace TwistData
variable (D : TwistData K) (p : ℕ)
variable (t : D.Tau)
end TwistData
end Formalism.MainNotions.PlaneGram
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable {σ : Type} [Fintype σ]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (M α : σ →₀ ℕ) (c : K) :
    ddiv M (monomial α c) = monomial (α - M) (c * bin M α) := by
  rw [ddiv_monomial]
  by_cases h : M ≤ α
  · rw [if_pos h, finsupp_prod_choose_eq_bin_of_le M α h]
  · rw [if_neg h]
    obtain ⟨x, hx⟩ : ∃ x, α x < M x := by
      by_contra hc
      push_neg at hc
      apply h
      exact Finsupp.le_def.2 hc
    have h0 : (bin M α : K) = 0 := by
      unfold bin
      exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [Nat.choose_eq_zero_of_lt hx])
    rw [h0, mul_zero, map_zero]
end Formalism.MainNotions.PlaneGram
