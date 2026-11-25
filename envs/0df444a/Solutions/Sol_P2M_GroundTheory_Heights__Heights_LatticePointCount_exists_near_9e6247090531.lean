-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticePointCount_exists_near_9e6247090531
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:02:25.250318+00:00
-- url     : https://prove2.me/submissions/3d33c44a-3a30-445d-be2b-7d06079b1f62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VolumeFundamentalDomainEq

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
open MeasureTheory Metric Module Submodule
open scoped ENNReal Pointwise
open GroundTheory.Heights₂.Heights.LatticePointCount
namespace GroundTheory.Heights₂.Heights.LatticePointCount
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {r : ℕ} (b : Fin r → V)
    (hb : LinearIndependent ℝ b) (S : Set V) (C : ℝ) (hS : ∀ s ∈ S, ‖s‖ ≤ C)
    (hspan : span ℤ S = span ℤ (Set.range b)) (v : V) (hv : v ∈ span ℝ (Set.range b)) :
    ∃ l ∈ span ℤ (Set.range b), ‖v - l‖ ≤ r * C := by
  classical
  have hSℤ : ∀ s ∈ S, s ∈ span ℤ (Set.range b) := fun s hs => hspan ▸ subset_span hs
  have hle : span ℝ (Set.range b) ≤ span ℝ S := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : b i ∈ span ℤ S := hspan ▸ subset_span ⟨i, rfl⟩
    exact Submodule.span_le_restrictScalars ℤ ℝ S this
  have hge : span ℝ S ≤ span ℝ (Set.range b) := by
    rw [Submodule.span_le]
    intro s hs
    exact Submodule.span_le_restrictScalars ℤ ℝ _ (hSℤ s hs)
  obtain ⟨T, hTS, hTspan, hTli⟩ := exists_linearIndependent ℝ S
  have hTW : span ℝ T = span ℝ (Set.range b) := hTspan.trans (le_antisymm hge hle)
  have hWfin : FiniteDimensional ℝ (span ℝ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  have : FiniteDimensional ℝ (span ℝ (Set.range ((↑) : T → V))) := by
    rw [Subtype.range_coe, hTW]
    exact hWfin
  have : Finite T := Module.Finite.finite_basis (Basis.span hTli)
  set T' : Finset V := (Set.toFinite T).toFinset with hT'
  have hT'coe : (T' : Set V) = T := Set.Finite.coe_toFinset _
  have hcard : T'.card = r := by
    have h1 := finrank_span_finset_eq_card (R := ℝ) (s := T') (by rw [hT'coe]; exact hTli)
    rw [hT'coe, hTW, finrank_span_eq_card hb, Fintype.card_fin] at h1
    exact h1.symm
  rw [← hTW, ← hT'coe] at hv
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hv
  have hT'S : ∀ t ∈ T', t ∈ S := fun t ht => hTS (hT'coe ▸ ht)
  refine ⟨∑ t ∈ T', (⌊f t⌋ : ℤ) • t, ?_, ?_⟩
  · exact sum_mem fun t ht => zsmul_mem (hSℤ t (hT'S t ht)) _
  · rw [← hf, ← Finset.sum_sub_distrib]
    calc ‖∑ t ∈ T', (f t • t - (⌊f t⌋ : ℤ) • t)‖ ≤ ∑ t ∈ T', ‖f t • t - (⌊f t⌋ : ℤ) • t‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _t ∈ T', C := by
          refine Finset.sum_le_sum fun t ht => ?_
          rw [← Int.cast_smul_eq_zsmul ℝ, ← sub_smul, norm_smul, Real.norm_eq_abs]
          have h0 : 0 ≤ f t - ⌊f t⌋ := Int.fract_nonneg (f t)
          have h1 : f t - ⌊f t⌋ < 1 := Int.fract_lt_one (f t)
          rw [abs_of_nonneg h0]
          calc (f t - ⌊f t⌋) * ‖t‖ ≤ 1 * ‖t‖ := by gcongr
            _ ≤ C := by rw [one_mul]; exact hS t (hT'S t ht)
      _ = r * C := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
end GroundTheory.Heights₂.Heights.LatticePointCount
