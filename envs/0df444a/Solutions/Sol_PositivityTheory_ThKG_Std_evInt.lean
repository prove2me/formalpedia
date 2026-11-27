-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.evInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:32:55.436475+00:00
-- url     : https://prove2.me/submissions/12e0a5c3-f4c0-4d56-894e-b14f015ac9bd

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Theorems.Thm_PositivityTheory_ThKG_Std_one_mem_SB
import Theorems.Thm_PositivityTheory_ThKG_Std_cut_mem
import Theorems.Thm_PositivityTheory_ThKG_Std_integrable_SB
import Theorems.Thm_PositivityTheory_ThKG_Std_int_ind_one
import Theorems.Thm_PositivityTheory_ThKG_Std_IsPsi_ex
import Theorems.Thm_PositivityTheory_ThKG_Std_IsPsi_ne
import Theorems.Thm_PositivityTheory_ThKG_Std_one_add
import Theorems.Thm_PositivityTheory_ThKG_Std_one_mul_psi
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_PositivityTheory_ThKH_Evl_core
import Theorems.Thm_PositivityTheory_ThKH_Evl_schr_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Pointwise
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {κ : Type} [Fintype κ] [DecidableEq κ]
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThKG.Std
theorem _root_.solution [Invertible (2 : k)] {m : Measure k} (hm : IsVol m) {ψ : AddChar k ℂ} (hψ : IsPsi ψ) (P : Finset κ)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ Z : κ → k, (∀ p ∉ P, Z p = 0) → ∀ Φ ∈ GlobalTheory.WeilM.SB (κ → k), l (fun Y => Φ (Y + Z)) = l Φ)
    (hM : ∀ Z : κ → k, (∀ p ∈ P, Z p = 0) → ∀ Φ ∈ GlobalTheory.WeilM.SB (κ → k), l (fun Y => ψ (Y ⬝ᵥ Z) * Φ Y) = l Φ)
    (h1 : l (one κ) = 1) : ∀ Φ ∈ GlobalTheory.WeilM.SB (κ → k), l Φ = ∫ Z, Φ (cut P Z) * wt P Z ∂(Measure.pi fun _ : κ => m) := by
  haveI := hm.haar
  let l₀ : GlobalTheory.WeilM.SB (κ → k) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => ∫ Z, Φ.1 (cut P Z) * wt P Z ∂(Measure.pi fun _ : κ => m)
      map_add' := fun a b => by
        rw [← integral_add (integrable_SB hm (cut_mem a.2)) (integrable_SB hm (cut_mem b.2))]
        simp [add_mul]
      map_smul' := fun c a => by simp [← integral_const_mul, mul_assoc] }
  obtain ⟨l', hl'⟩ := l₀.exists_extend
  have e : ∀ Φ ∈ GlobalTheory.WeilM.SB (κ → k), l' Φ = ∫ Z, Φ (cut P Z) * wt P Z ∂(Measure.pi fun _ : κ => m) := fun Φ h =>
    LinearMap.congr_fun hl' ⟨Φ, h⟩
  have dot0 : ∀ Z Z' : κ → k, (∀ p ∉ P, Z p = 0) → (∀ p ∈ P, Z' p = 0) → Z ⬝ᵥ Z' = 0 := fun Z Z' a b =>
    Finset.sum_eq_zero fun p _ => by
      by_cases hp : p ∈ P
      · rw [b p hp, mul_zero]
      · rw [a p hp, zero_mul]
  have key := PositivityTheory.ThKH.Evl.core hψ.cont hψ.norm hψ.ne (one_mem_SB (κ := κ) (k := k))
    (fun h => by have := congrFun h 0; simp [one, ind] at this)
    {w | (∀ p ∉ P, w.1 p = 0) ∧ ∀ p ∈ P, w.2 p = 0} (l - l') ?_ ?_ ?_
  · intro Φ hΦ
    rw [← e Φ hΦ, ← sub_eq_zero]; exact key Φ hΦ
  · rintro ⟨Z, Z'⟩ ⟨a, b⟩ φ hφ
    have hs := PositivityTheory.ThKH.Evl.schr_mem hψ.cont (Z, Z') hφ
    have hs0 := PositivityTheory.ThKH.Evl.schr_mem hψ.cont (Z, 0) hφ
    have e0 : GlobalTheory.WeilM.schr ψ (Z, (0 : κ → k)) φ = fun Y => φ (Y + Z) := by funext x; simp [GlobalTheory.WeilM.schr]
    have e1 : GlobalTheory.WeilM.schr ψ (Z, Z') φ = fun Y => ψ (Y ⬝ᵥ Z') * φ (Y + Z) := by
      funext x; simp [GlobalTheory.WeilM.schr, dot0 Z Z' a b]
    rw [e0] at hs0
    simp only [LinearMap.sub_apply]
    rw [e _ hs, e φ hφ, e1, hM Z' b _ hs0, hT Z a φ hφ]
    congr 1
    rw [← integral_add_right_eq_self (fun Y => φ (cut P Y) * wt P Y) Z]
    congr 1
    funext Y
    beta_reduce
    rw [dot0 (cut P Y) Z' (fun p hp => if_neg hp) b, AddChar.map_zero_eq_one, one_mul]
    congr 1
    · congr 1
      funext p
      by_cases hp : p ∈ P
      · simp [cut, hp]
      · simp [cut, hp, show Z p = 0 from a p hp]
    · refine Finset.prod_congr rfl fun p _ => ?_
      by_cases hp : p ∈ P
      · simp [hp]
      · simp [hp, show Z p = 0 from a p hp]
  · intro w
    let b1 : κ → k := fun p => if p ∈ P then 0 else w.1 p
    let b2 : κ → k := cut P w.2
    refine ⟨(cut P w.1, fun p => if p ∈ P then 0 else w.2 p), ⟨fun p hp => if_neg hp, fun p hp => if_pos hp⟩, (b1, b2), ?_, ?_⟩
    · refine Prod.ext (funext fun p => ?_) (funext fun p => ?_) <;> by_cases hp : p ∈ P <;> simp [cut, b1, b2, hp]
    have d12 : b1 ⬝ᵥ b2 = 0 := by rw [dotProduct_comm]; exact dot0 _ _ (fun p hp => if_neg hp) fun p hp => if_pos hp
    by_cases c1 : ∀ p, valuation k (b1 p) ≤ 1
    · by_cases c2 : ∀ p, valuation k (b2 p) ≤ 1
      · refine Or.inl ⟨1, funext fun x => ?_⟩
        simp only [GlobalTheory.WeilM.schr, d12, mul_zero, add_zero, one_add c1, one_mul_psi hψ c2, one_smul]
      · push Not at c2
        obtain ⟨p, hp⟩ := c2
        obtain ⟨y, hy, hy'⟩ := hψ.ex (not_le.2 hp)
        have hP : p ∈ P := by by_contra h; simp [b2, cut, h] at hp
        refine Or.inr ⟨(Pi.single p y, 0), ⟨fun q hq => Pi.single_eq_of_ne (fun h : q = p => hq (h ▸ hP)) _, fun _ _ => rfl⟩,
          funext fun x => ?_, by simpa [mul_comm] using hy'⟩
        have : ∀ q, valuation k ((Pi.single p y : κ → k) q) ≤ 1 := fun q => by
          by_cases h : q = p
          · subst h; simpa using hy
          · simp [Pi.single_eq_of_ne h]
        simp [GlobalTheory.WeilM.schr, one_add this]
    · push Not at c1
      obtain ⟨p, hp⟩ := c1
      obtain ⟨y, hy, hy'⟩ := hψ.ex (not_le.2 hp)
      have hP : p ∉ P := by intro h; simp [b1, h] at hp
      refine Or.inr ⟨(0, Pi.single p (-y)), ⟨fun _ _ => rfl, fun q hq => Pi.single_eq_of_ne (fun h : q = p => hP (h ▸ hq)) _⟩,
        funext fun x => ?_, by simpa using hy'⟩
      have : ∀ q, valuation k ((Pi.single p (-y) : κ → k) q) ≤ 1 := fun q => by
        by_cases h : q = p
        · subst h; simpa using hy
        · simp [Pi.single_eq_of_ne h]
      simp only [GlobalTheory.WeilM.schr, zero_dotProduct, mul_zero, add_zero, one_mul_psi hψ this]
  · rw [LinearMap.sub_apply, h1, e _ one_mem_SB]
    have : (fun Z : κ → k => one κ (cut P Z) * wt P Z) = fun Z => ∏ p, ind 1 (Z p) := by
      funext Z
      rw [one, wt, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ => ?_
      by_cases hp : p ∈ P <;> simp [cut, hp, ind]
    rw [this, integral_fintype_prod_eq_prod (fun _ : κ => ind (1 : k))]
    simp [int_ind_one hm]
end PositivityTheory.ThKG.Std
