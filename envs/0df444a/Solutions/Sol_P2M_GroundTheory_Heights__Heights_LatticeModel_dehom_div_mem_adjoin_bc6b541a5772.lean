-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_div_mem_adjoin_bc6b541a5772
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:18.630896+00:00
-- url     : https://prove2.me/submissions/5a855de7-0ec4-488b-97a2-afd65ad067fe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_sum_41169ea91792
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_intSmul_1c54165cdeb0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_exists_int_smul_mem_latticeDual_603c1b9810fa
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
variable {K : Type} [Field K] [NumberField K] {N r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)}
  {φ : Fin (N + 1) → Fin (r + 1) → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (hL : L.FG) (hφ : IsDualBasis L φ) (u : Fin (r + 1) → K) :
    dehom K r (latticeForm u) / latticeCoord φ ⟨(), 0⟩ ∈
      IntermediateField.adjoin ℚ (coneRatios (latticeCoord φ) fun _ : Unit ↦ (0 : Fin (N + 1))) := by
  set E := IntermediateField.adjoin ℚ (coneRatios (latticeCoord φ) fun _ : Unit ↦ (0 : Fin (N + 1)))
  have hb : ∀ b, latticeCoord φ ⟨(), b⟩ / latticeCoord φ ⟨(), 0⟩ ∈ E := fun b ↦
    IntermediateField.subset_adjoin _ _ ⟨⟨(), b⟩, rfl⟩
  obtain ⟨n, hn, hnu⟩ := exists_int_smul_mem_latticeDual hL u
  obtain ⟨c, hc⟩ := (mem_dual_iff hφ _).mp hnu
  have h1 : (n : LatticeField K r) * dehom K r (latticeForm u) / latticeCoord φ ⟨(), 0⟩ ∈ E := by
    rw [← dehom_latticeForm_intSmul, ← hc, dehom_latticeForm_sum, Finset.sum_div]
    refine sum_mem fun b _ ↦ ?_
    rw [mul_div_assoc]
    exact mul_mem (intCast_mem _ _) (hb b)
  have h2 : (n : LatticeField K r) ≠ 0 := Int.cast_ne_zero.mpr hn
  have h3 := div_mem h1 (intCast_mem E n)
  have e : (n : LatticeField K r) * dehom K r (latticeForm u) / latticeCoord φ ⟨(), 0⟩ / n =
      dehom K r (latticeForm u) / latticeCoord φ ⟨(), 0⟩ := by
    field_simp
  rwa [e] at h3
end GroundTheory.Heights₂.Heights.LatticeModel
