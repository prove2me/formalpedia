-- Prove2me | solution 1 for PI.InvTopW.entries_integral_of_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:36:16.850356+00:00
-- url     : https://prove2.me/submissions/826e4466-ca03-4677-906d-06a3a067e3d5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LatticeOfEntriesIntegral
import Theorems.Thm_PI_InvTopW_lat_data
import Theorems.Thm_PI_InvTopW_matrix_entries_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.InvTopW
theorem _root_.solution : EntriesLat := by
  intro I g hg
  obtain ⟨c, hc, h1, h2⟩ := lat_data I
  refine ⟨g * c * c, Nat.mul_pos (Nat.mul_pos hg hc) hc, ?_⟩
  intro M M' hMM' hM hM'
  have hsm : ∀ z ∈ I.Lf, ((g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • z) ∈ I.Lf := fun z hz =>
    I.Lf.smul_mem (⟨(g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), natCast_mem _ g⟩ : Formalism.MainNotions.S.IntAf I.F I.E) hz
  have hM'M : M' * M = 1 := by
    first
    | exact mul_eq_one_comm.1 hMM'
    | exact Matrix.mul_eq_one_comm.1 hMM'
    | (letI := Matrix.invertibleOfRightInverse M M' hMM'
       exact invOf_mul_self M)
  refine ⟨fun y => ⟨fun hy => ?_, fun hy => ?_⟩, fun y hy => matrix_entries_integral I c g h1 h2 (M - 1) hM y hy⟩
  · obtain ⟨z, hz, e⟩ := matrix_entries_integral I c g h1 h2 (M - 1) hM y hy
    have h3 : M *ᵥ y = y + (M - 1) *ᵥ y := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [h3, e]
    exact add_mem hy (hsm z hz)
  · obtain ⟨z, hz, e⟩ := matrix_entries_integral I c g h1 h2 (M' - 1) hM' (M *ᵥ y) hy
    have h3 : y = M *ᵥ y + (M' - 1) *ᵥ (M *ᵥ y) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, hM'M, Matrix.one_mulVec]
      abel
    rw [h3, e]
    exact add_mem hy (hsm z hz)
end PI.InvTopW
