-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_exists_mul_mem_of_le_sup_sq_eb111fd8b2cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:42.585988+00:00
-- url     : https://prove2.me/submissions/ef499ebd-d761-4d8a-80e9-85197b70c539

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsExpansion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTransverseSliceGeneral

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
open MvPolynomial Matrix ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.TransverseSliceGeneral
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.TransverseSliceGeneral
theorem _root_.solution (q : Fin n → ℂ) (I : Ideal (MvPolynomial (Fin n) ℂ))
    (h : RingHom.ker (eval q) ≤ I ⊔ RingHom.ker (eval q) ^ 2) (g : MvPolynomial (Fin n) ℂ)
    (hg : eval q g = 0) : ∃ s, eval q s ≠ 0 ∧ s * g ∈ I := by
  set m := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hle : Submodule.map I.mkQ m ≤ m • Submodule.map I.mkQ m := by
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    obtain ⟨i, hi, y, hy, rfl⟩ := Submodule.mem_sup.1 (h hx)
    rw [Submodule.mem_comap, map_add, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero I).2 hi, zero_add, ← Submodule.map_smul'']
    rw [sq, ← Ideal.smul_eq_mul] at hy
    exact Submodule.mem_map_of_mem hy
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m _
    ((IsNoetherian.noetherian m).map I.mkQ) hle
  refine ⟨r, ?_, ?_⟩
  · have h1 : eval q (r - 1) = 0 := hr1
    rw [map_sub, map_one, sub_eq_zero] at h1
    rw [h1]
    exact one_ne_zero
  · have h2 := hr _ (Submodule.mem_map_of_mem (f := I.mkQ) (show g ∈ m from hg))
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul] at h2
    exact h2
end GroundTheory.Heights₂.Heights.TransverseSliceGeneral
