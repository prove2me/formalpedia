-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_int_comb_33dd5c235172
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:44:06.133344+00:00
-- url     : https://prove2.me/submissions/19af5da7-4c20-491a-96f6-87fca54ecd67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_int_smul_mem_4c8901af79bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_dualLatticeCoord_eq_ca49334a53b1


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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField DualArithmeticVariety
noncomputable section
open GroundTheory.Heights₂.Heights.StandardModelDualRank
variable {K : Type} [Field K] {i : ℕ}
variable [NumberField K]
variable {T : Type}
namespace GroundTheory.Heights₂.Heights.StandardModelDualRank
theorem _root_.solution [Fintype T] (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (c : T) (a : K) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ n : T → ℤ, ∑ t, (n t : dualStdModelField K i) * w b t = (N : _) * embK K i a * w b c := by
  obtain ⟨N, hN, hmem⟩ := exists_int_smul_mem (HermLattice.standard K i) (a • (b c : Fin i → K))
  obtain ⟨φ, hφ⟩ : ∃ φ : dualLattice (HermLattice.standard K i),
      (φ : Fin i → K) = (N : K) • a • (b c : Fin i → K) := ⟨⟨_, hmem⟩, rfl⟩
  refine ⟨N, hN, fun t => b.repr φ t, ?_⟩
  have hrepr := congrArg (fun ψ : dualLattice (HermLattice.standard K i) => evalForm i (ψ : Fin i → K))
    (b.sum_repr φ)
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_zsmul, hφ, map_smul] at hrepr
  simp only [← dualLatticeCoord_eq b, zsmul_eq_mul, Algebra.smul_def, map_intCast] at hrepr
  have h2 := congrArg (fun y => dualStdModelEmb K i y * dualStdModelS K i * dualStdModelT K i) hrepr
  simp only [map_sum, map_mul, map_intCast, Finset.sum_mul] at h2
  simp only [w, embK, RingHom.comp_apply, mul_assoc] at h2 ⊢
  rw [h2]
end GroundTheory.Heights₂.Heights.StandardModelDualRank
