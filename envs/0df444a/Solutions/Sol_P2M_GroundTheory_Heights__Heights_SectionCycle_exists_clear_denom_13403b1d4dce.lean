-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_exists_clear_denom_13403b1d4dce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:15:19.222995+00:00
-- url     : https://prove2.me/submissions/f0c46c0e-73bd-46fb-924c-713b8f52286a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_mkF_X_ne_zero_6e1224960199

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
open GroundTheory.Heights₂.Heights.SectionCycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n} (D : AddBlockData P)
variable {d : ι → ℕ} {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {u : P.FunField} (hu : u ∈ P.chartRing c) :
    ∃ (e : ℕ) (f : MvPolynomial (Coord n) ℤ), u * P.mkF (chartMonomial c 1) ^ e = P.mkF f := by
  induction hu using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    refine ⟨1, X v * ∏ k ∈ Finset.univ.erase v.1, X ⟨k, c k⟩, ?_⟩
    have hne := mkF_X_ne_zero hc v.1
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
end GroundTheory.Heights₂.Heights.SectionCycle
