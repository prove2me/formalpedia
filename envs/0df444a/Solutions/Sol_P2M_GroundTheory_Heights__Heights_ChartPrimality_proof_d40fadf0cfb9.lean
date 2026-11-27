-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartPrimality_proof_d40fadf0cfb9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:55:47.948371+00:00
-- url     : https://prove2.me/submissions/6441ed9b-4b1e-493c-b783-996a101b0c00

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_WeightEqMapDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_component_ef6c391bfafd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e


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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
namespace ChartPrimality
theorem _root_.solution : ChartPrimality.Statement := by
  intro ι _ _ n P D
  refine ⟨{ ideal := D.extIdeal, isPrime := ?_, homogeneous := ?_, relevant := ?_, horizontal := ?_ }, rfl⟩
  · exact RingHom.ker_isPrime _
  · intro f hf m
    rw [AddBlockData.extIdeal, RingHom.mem_ker] at hf ⊢
    rw [D.extMap_component, hf, coeff_zero, monomial_zero]
  · rintro (_ | k)
    · obtain ⟨c, hc⟩ := P.exists_chart
      obtain ⟨u, -, hu⟩ := D.generating c hc
      have hj : ∃ j, D.elt j ≠ 0 := by
        by_contra h
        push Not at h
        simp [h] at hu
      obtain ⟨j, hj⟩ := hj
      refine ⟨j, fun hmem ↦ hj ?_⟩
      rw [AddBlockData.extIdeal, RingHom.mem_ker, AddBlockData.extMap, eval₂Hom_X'] at hmem
      exact (mul_eq_zero.mp hmem).resolve_right (X_ne_zero _) |> C_eq_zero.mp
    · obtain ⟨i, hi⟩ := P.relevant k
      refine ⟨i, fun hmem ↦ hi ?_⟩
      rw [AddBlockData.extIdeal, RingHom.mem_ker, AddBlockData.extMap, eval₂Hom_X'] at hmem
      rw [← P.mkF_eq_zero_iff]
      exact (mul_eq_zero.mp hmem).resolve_right (X_ne_zero _) |> C_eq_zero.mp
  · intro a ha
    rw [AddBlockData.extIdeal, RingHom.mem_ker, AddBlockData.extMap, eval₂Hom_C, eq_intCast] at ha
    have h2 : (a : P.FunField) = 0 := by rw [← C_eq_zero, map_intCast]; exact ha
    have h3 : algebraMap P.CoordRing P.FunField (a : P.CoordRing) = 0 := by rw [map_intCast]; exact h2
    rw [(IsFractionRing.injective P.CoordRing P.FunField).eq_iff' (map_zero _)] at h3
    exact_mod_cast h3
end ChartPrimality
end GroundTheory.Heights₂.Heights
