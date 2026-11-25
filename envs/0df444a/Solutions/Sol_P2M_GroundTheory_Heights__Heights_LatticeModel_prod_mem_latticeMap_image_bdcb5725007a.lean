-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_prod_mem_latticeMap_image_bdcb5725007a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:25.266021+00:00
-- url     : https://prove2.me/submissions/399060f8-c0a6-4c34-a961-af3843367eeb

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
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (hφ : IsDualBasis L φ) {d : ℕ} (u : Fin d → Fin m → K)
    (hu : ∀ i, u i ∈ latticeDual L) :
    ∃ f : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ, f.IsHomogeneous d ∧ latticeMap φ f = ∏ i, latticeForm (u i) := by
  choose c hc using fun i ↦ (mem_dual_iff hφ (u i)).mp (hu i)
  refine ⟨∏ i, ∑ b, C (c i b) * X ⟨(), b⟩, ?_, ?_⟩
  · have h := IsHomogeneous.prod Finset.univ (fun i ↦ ∑ b, C (c i b) * X (⟨(), b⟩ : Coord fun _ : Unit ↦ N))
      (fun _ ↦ 1) fun i _ ↦ IsHomogeneous.sum _ _ _ fun b _ ↦ isHomogeneous_C_mul_X _ _
    simpa using h
  · rw [map_prod]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [latticeMap_linear, hc i]
end GroundTheory.Heights₂.Heights.LatticeModel
