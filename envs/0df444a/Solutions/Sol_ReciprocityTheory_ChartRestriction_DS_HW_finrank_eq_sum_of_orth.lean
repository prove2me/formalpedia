-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.finrank_eq_sum_of_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:09.440377+00:00
-- url     : https://prove2.me/submissions/ab6ad828-8224-4da8-a7cf-cb70403455b9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {m : ℕ} (A : Fin m → Submodule ℂ V)
    (horth : ∀ i i', i ≠ i' → ∀ y ∈ A i, ∀ z ∈ A i', ⟪y, z⟫_ℂ = 0) (htop : (⨆ i, A i) = ⊤) :
    Module.finrank ℂ V = ∑ i, Module.finrank ℂ (A i) := by
  classical
  have hOF : OrthogonalFamily ℂ (fun i => A i) fun i => (A i).subtypeₗᵢ :=
    fun i j hij v w => horth i j hij _ v.2 _ w.2
  have hind : iSupIndep A := by
    first
      | exact hOF.independent
      | exact hOF.iSupIndep
  have hint : DirectSum.IsInternal A := by
    first
      | exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top A).mpr ⟨hind, htop⟩
      | exact (DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top A).mpr ⟨hind, htop⟩
  rw [Module.finrank_eq_card_basis (hint.collectedBasis fun i => Module.finBasis ℂ (A i)),
    Fintype.card_sigma]
  simp
end ReciprocityTheory.ChartRestriction.DS.HW
