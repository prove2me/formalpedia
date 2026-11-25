-- Prove2me | solution 1 for P2M_UpperTheory_Comparison__level_family_500f33f210e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:43.585352+00:00
-- url     : https://prove2.me/submissions/7d600397-bb39-40bb-befe-6156fc034950

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_GChiEq
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_GzEq
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_LevelFamily
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_P2M_UpperTheory_Comparison__Gz_eq_090925bcd8e1
import Theorems.Thm_P2M_UpperTheory_Comparison__gChi_eq_7c3956c33f79
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost
private theorem UpperTheory.Comparison₂.level_family_wt_pos (Λ : Level) (ψ : PChar) : 0 < UpperTheory.Comparison₂.level_family_wt Λ ψ := by
  unfold UpperTheory.Comparison₂.level_family_wt Level.wt
  split_ifs
  · exact one_pos
  · exact one_pos
  · positivity
private theorem UpperTheory.Comparison₂.level_family_adm (ψ : PChar) : ψ.N = 1 ∨ ψ.χ ≠ 1 := by
  by_cases h : ψ.χ = 1
  · left
    have hp := ψ.prim
    rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hp
    exact hp.symm
  · exact Or.inr h
private theorem UpperTheory.Comparison₂.level_family_sum (Λ : Level) (y : ℝ) :
    ∑ ψ ∈ Λ.KEPT, UpperTheory.Comparison₂.level_family_wt Λ ψ * (Deduction.Gchi ψ.χ y).re = Λ.Gm y := by
  classical
  rw [← Finset.add_sum_erase _ _ Λ.one_mem, Level.Gm, Level.Nt]
  congr 1
  · have h1 : UpperTheory.Comparison₂.level_family_wt Λ PChar.one = 1 := by
      simp [UpperTheory.Comparison₂.level_family_wt]
    rw [h1, one_mul, ← gChi_eq, (Gz_eq y).1]
    simp only [An.gChi, PChar.one]
    exact (congrArg Complex.re (if_pos rfl)).trans (Complex.ofReal_re _)
  · refine Finset.sum_congr (by congr) fun ψ hψ => ?_
    have hne : ψ ≠ PChar.one := Finset.ne_of_mem_erase hψ
    simp only [UpperTheory.Comparison₂.level_family_wt, if_neg hne, gChi_eq]
end

set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost
namespace UpperTheory.Comparison₂
theorem _root_.solution :
    ∀ Λ : Level, ∃ F : Deduction.CharFamily, (∀ y, Deduction.Gm F y = Λ.Gm y) ∧ ∀ θ, Deduction.ZeroFree F θ ↔ Λ.ZeroFreeAbove θ := by
  intro Λ
  refine ⟨@Deduction.CharFamily.mk Λ.KEPT _ (fun i => i.1.N) (fun i => i.1.ne) (fun i => i.1.χ) (fun i => UpperTheory.Comparison₂.level_family_wt Λ i.1) (fun i => UpperTheory.Comparison₂.level_family_wt_pos Λ i.1) (fun i => UpperTheory.Comparison₂.level_family_adm i.1), fun y => ?_, fun θ => ?_⟩
  · rw [← UpperTheory.Comparison₂.level_family_sum Λ y, Deduction.Gm]
    exact Finset.sum_coe_sort Λ.KEPT (fun ψ => UpperTheory.Comparison₂.level_family_wt Λ ψ * (Deduction.Gchi ψ.χ y).re)
  · simp only [Deduction.ZeroFree, Level.ZeroFreeAbove, PChar.ZeroFreeAbove]
    constructor
    · intro h ψ hψ s hs
      exact h ⟨ψ, hψ⟩ s hs
    · intro h i s hs
      exact h i.1 i.2 s hs
end UpperTheory.Comparison₂
