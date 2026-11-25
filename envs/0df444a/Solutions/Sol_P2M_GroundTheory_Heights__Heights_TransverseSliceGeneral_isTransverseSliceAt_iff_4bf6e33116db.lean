-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_isTransverseSliceAt_iff_4bf6e33116db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:37:41.049728+00:00
-- url     : https://prove2.me/submissions/b25e9662-cace-49dc-8730-11e025a4ddb9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsExpansion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTransverseSliceGeneral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_mul_of_eval_eq_zero_7e4ca727f22d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_X_sub_C_65f9f86f6e98
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_exists_expansion_8e7a532e1b86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_mem_sq_of_gradAt_eq_zero_ba2ac002f700
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_exists_mul_mem_of_le_sup_sq_eb111fd8b2cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradSpace_sliceIdeal_d192009989c4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_zeroSet_sliceIdeal_81bd9c1d3ddc
import Theorems.Thm_UpperTheory_Reformulated_B_Qn12_exists_expansion


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
theorem _root_.solution (W : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ)
    (q : Fin n → ℂ) (hq : q ∈ zeroSet W) :
    IsTransverseSliceAt W L q ↔ gradSpace W q ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤ := by
  rw [← gradSpace_sliceIdeal W L q]
  have hq' : q ∈ zeroSet (sliceIdeal W L q) := by
    rw [zeroSet_sliceIdeal]
    exact ⟨hq, rfl⟩
  set I := sliceIdeal W L q
  constructor
  · intro hT
    rw [eq_top_iff, ← (Pi.basisFun ℂ (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨s, hs, hsI⟩ := hT (X j - C (q j)) (by simp)
    refine ⟨C (eval q s)⁻¹ * (s * (X j - C (q j))), I.mul_mem_left _ hsI, ?_⟩
    rw [gradAt_mul_of_eval_eq_zero q _ _ (by simp), gradAt_mul_of_eval_eq_zero q _ _ (by simp),
      gradAt_X_sub_C, smul_smul, eval_C, inv_mul_cancel₀ hs, one_smul, Pi.basisFun_apply]
  · intro hG g hg
    refine exists_mul_mem_of_le_sup_sq q I (fun x hx => ?_) g hg
    obtain ⟨c, hc⟩ := exists_expansion q x
    rw [RingHom.mem_ker.1 hx, map_zero, zero_add] at hc
    rw [hc]
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_
    obtain ⟨h, hh, hgh⟩ : (Pi.single i 1 : Fin n → ℂ) ∈ gradSpace I q := hG ▸ Submodule.mem_top
    have hmem : X i - C (q i) - h ∈ RingHom.ker (eval q) ^ 2 :=
      mem_sq_of_gradAt_eq_zero q _ (by rw [map_sub, hq' h hh]; simp)
        (by rw [map_sub, hgh, gradAt_X_sub_C, sub_self])
    have hsplit : X i - C (q i) = h + (X i - C (q i) - h) := by ring
    rw [hsplit]
    exact Submodule.add_mem_sup hh hmem
end GroundTheory.Heights₂.Heights.TransverseSliceGeneral
