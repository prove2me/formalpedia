-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_int_comb_c953859cc094
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:44.639066+00:00
-- url     : https://prove2.me/submissions/45b560c2-b1d0-44b7-ba1c-34b4ace7ccee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_int_smul_mem_latticeDual_7ca10bc0ad16

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
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) (v : Fin (r + 1) → K) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ c : Fin (N + 1) → ℤ, ∑ b, c b • φ b = D • v := by
  obtain ⟨D, hD, hmem⟩ := exists_int_smul_mem_latticeDual F.lattice F.fg v
  have h : D • v ∈ Submodule.span ℤ (Set.range φ) := by rw [hφ.span_eq]; exact hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h
  exact ⟨D, hD, c, hc⟩
end GroundTheory.Heights₂.Heights
