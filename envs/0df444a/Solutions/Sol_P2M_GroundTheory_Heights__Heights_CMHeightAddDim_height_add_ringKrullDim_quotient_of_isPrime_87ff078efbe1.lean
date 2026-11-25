-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CMHeightAddDim_height_add_ringKrullDim_quotient_of_isPrime_87ff078efbe1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:40:36.297154+00:00
-- url     : https://prove2.me/submissions/f94650c8-6e31-4b7c-b847-ca3bcb932e45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMHeightAddDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CMDepthAssoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_HeightCoheightQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMHeightAddDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_add_ringKrullDim_quotient_le_42493816d064
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_map_add_one_le_of_mem_nonZeroDivisors_57a541d5cf05
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_eq_of_mem_minimalPrimes_8298c56cb1b7


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing
universe u
namespace GroundTheory.Heights₂.Heights
namespace CMHeightAddDim
theorem _root_.solution (hreg : CMRegularElement.Statement.{u}) :
    ∀ (n : ℕ) (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B], ringKrullDim B = n →
      ∀ (P : Ideal B) [P.IsPrime], (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) = ringKrullDim B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B _ _ hn P hP
  refine le_antisymm (height_add_ringKrullDim_quotient_le P) ?_
  by_cases hmin : P ∈ minimalPrimes B
  · rw [Ideal.height_eq_zero_iff.mpr hmin, ringKrullDim_quotient_eq_of_mem_minimalPrimes hmin]
    simp

  have hfin := minimalPrimes.finite_of_isNoetherianRing (R := B)
  obtain ⟨y, hyP, hyq⟩ : ∃ y ∈ P, ∀ q ∈ minimalPrimes B, y ∉ q := by
    by_contra! h
    have hsub : (P : Set B) ⊆ ⋃ i ∈ (↑hfin.toFinset : Set (Ideal B)), (id i : Set B) := by
      intro z hz
      obtain ⟨q, hq, hzq⟩ := h z hz
      exact Set.mem_biUnion (by simpa using hq) hzq
    obtain ⟨q, hq, hPq⟩ := (Ideal.subset_union_prime (s := hfin.toFinset) (f := id) ⊥ ⊥
      (fun i hi _ _ => ((Set.Finite.mem_toFinset hfin).mp hi).1.1)).mp hsub
    have hq' : q ∈ minimalPrimes B := (Set.Finite.mem_toFinset hfin).mp hq
    have hqP : q ≤ P := hq'.2 ⟨hP, bot_le⟩ hPq
    exact hmin (le_antisymm hPq hqP ▸ hq')
  have hym : y ∈ maximalIdeal B := le_maximalIdeal hP.ne_top hyP
  obtain ⟨hynzd, hCM⟩ := hreg B y hym hyq
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hynzd hym
  obtain ⟨rs', -, -, hd'⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B ⧸ Ideal.span {y})
  have hlt : rs'.length < n := by
    have h1 : ((rs'.length + 1 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
      rw [← hn, ← hdim, hd']
      push_cast
      rfl
    have h2 : rs'.length + 1 = n := by exact_mod_cast h1
    omega
  have hle : Ideal.span {y} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hyP
  have hP' : (P.map (Ideal.Quotient.mk (Ideal.span {y}))).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hle
  have hIH := ih rs'.length hlt (B ⧸ Ideal.span {y}) hd' (P.map (Ideal.Quotient.mk (Ideal.span {y})))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hIH
  have hc := height_map_add_one_le_of_mem_nonZeroDivisors hynzd P hyP
  calc ringKrullDim B = ringKrullDim (B ⧸ Ideal.span {y}) + 1 := hdim.symm
    _ = ((P.map (Ideal.Quotient.mk (Ideal.span {y}))).height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) + 1 := by
        rw [hIH]
    _ = (((P.map (Ideal.Quotient.mk (Ideal.span {y}))).height + 1 : ℕ∞) : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by
        rw [WithBot.coe_add, WithBot.coe_one, add_right_comm]
    _ ≤ (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by
        gcongr
        exact_mod_cast hc
end CMHeightAddDim
end GroundTheory.Heights₂.Heights
