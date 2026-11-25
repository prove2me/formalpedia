-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SmallSections_exists_mul_pow_eq_mkF_840b0bae13e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:16:55.438654+00:00
-- url     : https://prove2.me/submissions/e328b4dd-9513-40b0-a3fc-549a22e0e4b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_mkF_X_ne_zero_5ca902d68882

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SmallSections
theorem _root_.solution {P : ArithVariety n} {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {u : P.FunField} (hu : u ∈ P.chartRing c) :
    ∃ (N : ℕ) (E : MvPolynomial (Coord n) ℤ), u * P.mkF (chartMonomial c 1) ^ N = P.mkF E := by
  unfold ArithVariety.chartRing at hu
  induction hu using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    refine ⟨1, X v * ∏ k ∈ Finset.univ.erase v.1, X ⟨k, c k⟩, ?_⟩
    have h1 : P.mkF (chartMonomial c 1) =
        P.mkF (X ⟨v.1, c v.1⟩) * ∏ k ∈ Finset.univ.erase v.1, P.mkF (X ⟨k, c k⟩) := by
      rw [chartMonomial, map_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v.1)]
      simp
    have hne := mkF_X_ne_zero hc v.1
    rw [pow_one, h1, map_mul, map_prod, ArithVariety.chartCoord]
    field_simp
  | zero => exact ⟨0, 0, by simp⟩
  | one => exact ⟨0, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, E, hE⟩ := hx
    obtain ⟨N', E', hE'⟩ := hy
    refine ⟨N + N', E * chartMonomial c 1 ^ N' + E' * chartMonomial c 1 ^ N, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hE, ← hE', pow_add]
    ring
  | neg x _ hx =>
    obtain ⟨N, E, hE⟩ := hx
    exact ⟨N, -E, by rw [map_neg, ← hE]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨N, E, hE⟩ := hx
    obtain ⟨N', E', hE'⟩ := hy
    exact ⟨N + N', E * E', by rw [map_mul, ← hE, ← hE', pow_add]; ring⟩
end GroundTheory.Heights₂.Heights.SmallSections
