-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_exists_int_smul_mem_latticeDual_603c1b9810fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:23:09.669904+00:00
-- url     : https://prove2.me/submissions/2235ec6c-61fe-45f5-9609-a2fe56a4c72b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_exists_int_mul_integral_bc558ebbcceb

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution {m : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} (hL : L.FG)
    (u : Fin m → K) : ∃ n : ℤ, n ≠ 0 ∧ (n : K) • u ∈ latticeDual L := by
  classical
  obtain ⟨s, rfl⟩ := hL
  choose n hn a ha using fun g : Fin m → K ↦ exists_int_mul_integral (u ⬝ᵥ g)
  refine ⟨∏ g ∈ s, n g, Finset.prod_ne_zero_iff.mpr fun g _ ↦ hn g, ?_⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨((∏ g ∈ s.erase x, n g : ℤ) : 𝓞 K) * a x, ?_⟩
    rw [map_mul, map_intCast, ha x, smul_dotProduct, smul_eq_mul, ← Finset.mul_prod_erase s n hx]
    push_cast
    ring
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨b + c, by rw [map_add, hb, hc, dotProduct_add]⟩
  | smul c x _ hx =>
    obtain ⟨b, hb⟩ := hx
    exact ⟨c * b, by rw [map_mul, hb, dotProduct_smul, Algebra.smul_def c]⟩
end GroundTheory.Heights₂.Heights.LatticeModel
