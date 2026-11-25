-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_clear_denom_4864fe822f9f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:50:56.128915+00:00
-- url     : https://prove2.me/submissions/afceebd4-5ce6-4219-b651-504cb55eb3a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroTer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_mkF_X_ne_zero_f0798c5f09f9

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
open GroundTheory.Heights₂.Heights.ChartVanishing
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.ChartVanishing
theorem _root_.solution (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {u : P.FunField} (hu : u ∈ P.chartRing c) :
    ∃ (e : ℕ) (f : MvPolynomial (Coord n) ℤ), u * P.mkF (chartMonomial c 1) ^ e = P.mkF f := by
  induction hu using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    refine ⟨1, X v * ∏ k ∈ Finset.univ.erase v.1, X ⟨k, c k⟩, ?_⟩
    have hne := mkF_X_ne_zero P hc v.1
    simp only [ArithVariety.chartCoord, chartMonomial, Pi.one_apply, pow_one, map_prod, map_mul]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v.1)]
    field_simp
  | zero => exact ⟨0, 0, by simp⟩
  | one => exact ⟨0, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨e, f, hf⟩ := hx
    obtain ⟨e', f', hf'⟩ := hy
    refine ⟨e + e', f * chartMonomial c 1 ^ e' + f' * chartMonomial c 1 ^ e, ?_⟩
    simp only [map_add, map_mul, map_pow, ← hf, ← hf']
    ring
  | neg x _ hx =>
    obtain ⟨e, f, hf⟩ := hx
    refine ⟨e, -f, ?_⟩
    rw [map_neg, ← hf]
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨e, f, hf⟩ := hx
    obtain ⟨e', f', hf'⟩ := hy
    refine ⟨e + e', f * f', ?_⟩
    rw [map_mul, ← hf, ← hf']
    ring
end GroundTheory.Heights₂.Heights.ChartVanishing
