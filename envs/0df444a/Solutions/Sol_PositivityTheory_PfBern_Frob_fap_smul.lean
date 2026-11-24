-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.fap_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:45:48.139927+00:00
-- url     : https://prove2.me/submissions/4a8d881b-ecb3-45be-a8db-8d39743a8e92

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TensInduction
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TrivSymmApply
import Theorems.Thm_PositivityTheory_PfBern_Frob_triv_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_triv_symm_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_fap_apply
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
theorem _root_.solution [LocallyCompactSpace (Fib p)] (α : SB G) (φ : SB (Fib p)) (g : G) (z : Fib p) :
    ((fap hp σ hpc μH α φ : SB X) : X → ℂ) (g • z.1) =
      ∫ h, (α : G → ℂ) (g * (h : G)) * (φ : Fib p → ℂ) (fibSmul hp h⁻¹ z) ∂μH := by
  rw [fap_apply, p_smul_fib hp g z]
  set s0 := σ.s (g : G ⧸ H)
  set k : H := ⟨s0⁻¹ * g, σ.inv_mul_mem g⟩
  conv_lhs => rw [← integral_mul_left_eq_self _ k]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  have e1 : s0 * ((k * h : H) : G) = g * h := by
    simp [k, mul_assoc]
  have e2 : fibSmul hp (k * h)⁻¹ (zpart hp σ (g • z.1)) = fibSmul hp h⁻¹ z := by
    apply Subtype.ext
    simp [k, s0, smul_smul, mul_assoc, p_smul_fib hp g z]
  simp only [e1, e2]
end PositivityTheory.PfBern.Frob
