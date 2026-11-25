-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_locAtIntPrime_eq_locPrimeTo_4bb9be37f9c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:34:58.180656+00:00
-- url     : https://prove2.me/submissions/0527b34f-b528-4708-893c-8164ade89f38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (p : ℕ) (A : Subalgebra ℤ Ω) :
    locAtIntPrime p A.toSubring = (IndefiniteRowSideFullHecke.Antisym.locPrimeTo A p).toSubring := by
  rw [IndefiniteRowSideFullHecke.Antisym.locPrimeTo, Algebra.adjoin_int]
  show locAtIntPrime p A.toSubring = Subring.closure _
  apply le_antisymm
  · refine Subring.closure_le.2 (Set.union_subset (fun a ha => Subring.subset_closure (Or.inl ha)) ?_)
    rintro u ⟨s, hs, rfl⟩
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg s
    · exact Subring.subset_closure
        (Or.inr ⟨n, fun h => hs (Int.natCast_dvd_natCast.2 h), by simp⟩)
    · have hmem : ((n : ℕ) : Ω)⁻¹ ∈ Subring.closure ((A : Set Ω) ∪
          {u | ∃ s : ℕ, ¬ p ∣ s ∧ u = (s : Ω)⁻¹}) :=
        Subring.subset_closure (Or.inr ⟨n, fun h => hs (by
          rw [Int.dvd_neg]; exact Int.natCast_dvd_natCast.2 h), rfl⟩)
      simpa [inv_neg] using neg_mem hmem
  · refine Subring.closure_le.2 (Set.union_subset (fun a ha => Subring.subset_closure (Or.inl ha)) ?_)
    rintro u ⟨s, hs, rfl⟩
    exact Subring.subset_closure (Or.inr ⟨s, fun h => hs (Int.natCast_dvd_natCast.1 h), by simp⟩)
end GroundTheory.Heights₂.Heights
