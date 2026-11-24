-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CoinvIdealRepresentation_proof_04cfae8b11db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:12.361172+00:00
-- url     : https://prove2.me/submissions/f1845f85-aa27-4d5b-84e8-0d34cd582ba2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvIdealRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open Coinv
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CoinvIdealRepresentation
theorem _root_.solution : CoinvIdealRepresentation.Statement := by
  intro K _ f n J hJ
  induction hJ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m₀, b₀, h1, h2, rfl⟩ := hx
    refine ⟨fun m b => if m = m₀ ∧ b = b₀ then 1 else 0, ?_⟩
    have hm₀ : m₀ ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨h1, h2⟩
    symm
    rw [Finset.sum_eq_single m₀]
    · rw [Finset.sum_eq_single b₀]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd (Finset.mem_univ b₀) h
    · intro m _ hm
      apply Finset.sum_eq_zero
      intro b _
      simp [hm]
    · intro h
      exact absurd hm₀ h
  | zero =>
    exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨a', rfl⟩ := hy
    refine ⟨a + a', ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  | smul r x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    refine ⟨fun m b => r * a m b, ?_⟩
    simp only [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun b _ => ?_
    ring
end CoinvIdealRepresentation
end GroundTheory.Heights₂.Heights.RestTerms
