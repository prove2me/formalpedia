-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.fap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:08.256717+00:00
-- url     : https://prove2.me/submissions/9e5084bd-81dc-42f8-a895-963b49e346fd

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TensInduction
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TrivSymmApply
import Theorems.Thm_PositivityTheory_PfBern_Frob_triv_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_triv_symm_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_intB_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_rtr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.PfBern.Frob.intB_apply
attribute [local simp] PositivityTheory.PfBern.Frob.rtr_apply


attribute [local simp] PositivityTheory.PfBern.Frob.triv_apply
attribute [local simp] PositivityTheory.PfBern.Frob.triv_symm_apply

set_option autoImplicit false
noncomputable section
open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Frob
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {H : Subgroup G} [LocallyCompactSpace H]
  {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] [MulAction G X] [ContinuousSMul G X]
  {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (σ : Sec H)
  (hpc : Continuous p) (μH : Measure H) [μH.IsHaarMeasure]
namespace PositivityTheory.PfBern.Frob
theorem _root_.solution [LocallyCompactSpace (Fib p)] (α : SB G) (φ : SB (Fib p)) (x : X) :
    ((fap hp σ hpc μH α φ : SB X) : X → ℂ) x = ∫ h, (α : G → ℂ) (σ.s (p x) * (h : G)) *
      (φ : Fib p → ℂ) (fibSmul hp h⁻¹ (zpart hp σ x)) ∂μH := by
  simp [fap, avg]
end PositivityTheory.PfBern.Frob
