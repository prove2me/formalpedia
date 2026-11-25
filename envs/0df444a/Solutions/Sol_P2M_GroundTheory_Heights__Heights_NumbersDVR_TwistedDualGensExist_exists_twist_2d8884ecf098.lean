-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_exists_twist_2d8884ecf098
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:15:45.538853+00:00
-- url     : https://prove2.me/submissions/efe62803-6cc4-4a05-bafd-2611b1eab8e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensExist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_latSub_fg_ea0656f0f852
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_pow_mul_mem_mono_b099b0e3fb7e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω] {τ : Type*}
  {r : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace TwistedDualGensExist
theorem _root_.solution [Fintype τ] {x : τ → Ω} (B : ChartBundle O x r E) {c : τ}
    (hc : x c ≠ 0) {ψ : Module.Dual Ω E} (hψ : ∀ v ∈ B.lat c, ψ v ∈ chartRing O x c) :
    ∃ n : ℕ, ∀ c', x c' ≠ 0 → ∀ v ∈ B.lat c', (x c / x c') ^ n * ψ v ∈ chartRing O x c' := by
  have hone : ∀ c', ∃ n : ℕ, x c' ≠ 0 → ∀ v ∈ B.lat c',
      (x c / x c') ^ n * ψ v ∈ chartRing O x c' := by
    intro c'
    by_cases hc' : x c' = 0
    · exact ⟨0, fun h => (h hc').elim⟩
    obtain ⟨S, hS⟩ := TwistedDualGensExist.latSub_fg B hc'
    have hgen : ∀ v ∈ S, ∃ m : ℕ, (x c / x c') ^ m * ψ v ∈ chartRing O x c' := by
      intro v hv
      have hv' : v ∈ B.lat c' := by
        have : v ∈ TwistedDualGensExist.latSub B c' := hS ▸ Submodule.subset_span hv
        exact this
      obtain ⟨m, hm⟩ := B.overlap c' c hc' hc v hv'
      have hw := hψ _ hm
      rw [map_smul, smul_eq_mul] at hw
      obtain ⟨m', hm'⟩ := exists_pow_mul_mem_chartRing x c c' hc hw
      refine ⟨m', ?_⟩
      have hu : (x c / x c') ^ m * (x c' / x c) ^ m = 1 := by
        rw [← mul_pow, div_mul_div_comm, mul_comm (x c), div_self (mul_ne_zero hc' hc), one_pow]
      have : (x c / x c') ^ m' * ψ v =
          (x c / x c') ^ m * ((x c / x c') ^ m' * ((x c' / x c) ^ m * ψ v)) := by
        linear_combination (-(x c / x c') ^ m' * ψ v) * hu
      rw [this]
      exact mul_mem (pow_mem (div_mem_chartRing x c' c) _) hm'
    choose! m hm using hgen
    refine ⟨∑ v ∈ S, m v, fun _ v hv => ?_⟩
    have hv' : v ∈ Submodule.span (chartRing O x c') (S : Set E) := by
      rw [hS]
      exact hv
    clear hv
    induction hv' using Submodule.span_induction with
    | mem w hw =>
      exact TwistedDualGensExist.pow_mul_mem_mono (hm w hw)
        (Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) hw)
    | zero => simp
    | add w z _ _ hw hz =>
      rw [map_add, mul_add]
      exact add_mem hw hz
    | smul a w _ hw =>
      show (x c / x c') ^ _ * ψ ((a : Ω) • w) ∈ _
      rw [map_smul, smul_eq_mul, mul_left_comm]
      exact mul_mem a.2 hw
  choose n hn using hone
  refine ⟨∑ c', n c', fun c' hc' v hv => TwistedDualGensExist.pow_mul_mem_mono (hn c' hc' v hv) ?_⟩
  exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c')
end TwistedDualGensExist
end GroundTheory.Heights₂.Heights.NumbersDVR
