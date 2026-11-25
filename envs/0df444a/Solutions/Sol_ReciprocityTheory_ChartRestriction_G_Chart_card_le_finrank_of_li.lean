-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.card_le_finrank_of_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:51.064792+00:00
-- url     : https://prove2.me/submissions/9cf496e9-55d0-490d-9acf-557127c82011

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open Module
variable {V k : Type} [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field k] [Algebra V k] [FaithfulSMul V k]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {ι' ι : Type} [Fintype ι'] [Fintype ι] (v : ι → ι' → V) (hv : LinearIndependent V v)
    (W : Submodule k (ι' → k)) (hW : ∀ i, (algebraMap V k ∘ v i) ∈ W) : Fintype.card ι ≤ finrank k W := by
  have hk : LinearIndependent k (fun i => algebraMap V k ∘ v i) :=
    linearIndependent_algebraMap_comp_iff.mpr hv
  have hw : LinearIndependent k (fun i => (⟨algebraMap V k ∘ v i, hW i⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hk
  exact hw.fintype_card_le_finrank
end ReciprocityTheory.ChartRestriction.G.Chart
