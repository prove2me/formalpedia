-- Prove2me | solution 1 for PI.FJMS.neg_iff_nN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:23.99602+00:00
-- url     : https://prove2.me/submissions/61d6178c-373b-4e70-8600-4121013d403d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Lemmata_B1959r_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMS
open PI.FJM PI.FJMP
namespace PI.FJMS
theorem _root_.solution {n : ℕ} (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0)
    (i : Fin n) : f i < 0 ↔ n ≤ i.val + nN f := by
  constructor
  · intro hi
    have hsub : Finset.Ici i ⊆ Finset.univ.filter (fun x => f x < 0) := by
      intro x hx
      rw [Finset.mem_Ici] at hx
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hx.lt_or_eq with h | h
      · exact hseg i x h hi
      · rw [← h]; exact hi
    have h2 := Finset.card_le_card hsub
    rw [Fin.card_Ici] at h2
    show n ≤ i.val + (Finset.univ.filter fun x => f x < 0).card
    have := i.isLt
    omega
  · intro hi
    by_contra hn
    have hsub : Finset.univ.filter (fun x => f x < 0) ⊆ Finset.Ioi i := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_Ioi]
      by_contra hle
      push_neg at hle
      rcases hle.lt_or_eq with h | h
      · exact hn (hseg x i h hx.2)
      · rw [← h] at hn; exact hn hx.2
    have h2 := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at h2
    have h3 : n ≤ i.val + (Finset.univ.filter fun x => f x < 0).card := hi
    have := i.isLt
    omega
end PI.FJMS
