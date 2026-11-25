-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_standard_coord_integral_2758d376c410
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:41:11.61464+00:00
-- url     : https://prove2.me/submissions/3f9ad2b2-c87b-4ba3-8100-e29da596b9bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockStandard

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
open MvPolynomial NumberField Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m : ℕ} {v : Fin m → K}
    (hv : v ∈ (HermLattice.standard K m).lattice) (i : Fin m) :
    ∃ b : 𝓞 K, v i = algebraMap (𝓞 K) K b := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨if i = j then 1 else 0, ?_⟩
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ← ha, ← hb, Pi.add_apply]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [map_mul, ← ha, Pi.smul_apply, Algebra.smul_def]⟩
end GroundTheory.Heights₂.Heights
