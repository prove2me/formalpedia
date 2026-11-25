-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_exists_linear_of_mem_6d2dc9a00622
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:21.285249+00:00
-- url     : https://prove2.me/submissions/390fec4c-9aad-4375-8423-757413c4103b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_linear_b60498b1849d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_mem_dual_iff_40d47eed4618


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
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}
variable {φ : Fin (N + 1) → Fin m → K}
variable {r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)} {φ : Fin (N + 1) → Fin (r + 1) → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution {m : ℕ} {L' : Submodule (𝓞 K) (Fin m → K)} {φ' : Fin (N + 1) → Fin m → K}
    (hφ : IsDualBasis L' φ') {u : Fin m → K} (hu : u ∈ latticeDual L') :
    ∃ g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ, g.IsHomogeneous 1 ∧ latticeMap φ' g = latticeForm u := by
  obtain ⟨c, hc⟩ := (mem_dual_iff hφ u).mp hu
  exact ⟨∑ b, C (c b) * X ⟨(), b⟩, IsHomogeneous.sum _ _ _ fun b _ ↦ isHomogeneous_C_mul_X _ _,
    by rw [latticeMap_linear, hc]⟩
end GroundTheory.Heights₂.Heights.LatticeModel
