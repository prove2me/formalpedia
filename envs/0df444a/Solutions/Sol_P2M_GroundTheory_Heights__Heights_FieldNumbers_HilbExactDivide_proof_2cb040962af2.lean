-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_proof_2cb040962af2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:13:41.428969+00:00
-- url     : https://prove2.me/submissions/64953736-2a68-4560-bf96-4557e216325d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_finrank_eq_beef6e4ea699

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
theorem _root_.solution (h1 : GradedFinite.Statement.{u}) : HilbExactDivide.Statement.{u} := by
  intro F _ K _ _ ι _ I hI c s hs m
  by_cases hm : ∀ k, 0 ≤ m k
  · obtain ⟨n, rfl⟩ : ∃ n : K → ℕ, m = fun k => (n k : ℤ) :=
      ⟨fun k => (m k).toNat, funext fun k => (Int.toNat_of_nonneg (hm k)).symm⟩
    have key := finrank_eq h1 hI hs n
    rw [(h1 F K ι I n).2, (h1 F K ι (I ⊔ Ideal.span {s}) n).2, key]
    by_cases hc : c ≤ n
    · rw [if_pos hc]
      have hnc : ((fun k => (n k : ℤ)) - fun k => (c k : ℤ)) = fun k => ((n - c) k : ℤ) :=
        funext fun k => by
          have : c k ≤ n k := hc k
          simp only [Pi.sub_apply]
          omega
      rw [hnc, (h1 F K ι _ (n - c)).2]
      push_cast
      ring
    · rw [if_neg hc]
      have hneg : hilbFn (I.colon (Ideal.span {s}))
          ((fun k => (n k : ℤ)) - fun k => (c k : ℤ)) = 0 := by
        rw [hilbFn, if_neg]
        intro hall
        apply hc
        intro k
        show c k ≤ n k
        have := hall k
        simp only [Pi.sub_apply] at this
        omega
      rw [hneg]
      push_cast
      ring
  · have hm' : ¬ ∀ k, 0 ≤ (m - fun k => (c k : ℤ)) k := by
      intro hall
      apply hm
      intro k
      have := hall k
      simp only [Pi.sub_apply] at this
      omega
    simp only [hilbFn, if_neg hm, if_neg hm', sub_zero]
end GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
