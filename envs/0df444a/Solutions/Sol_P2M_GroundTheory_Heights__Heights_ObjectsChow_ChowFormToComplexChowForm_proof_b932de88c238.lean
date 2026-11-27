-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_ChowFormToComplexChowForm_proof_b932de88c238
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:05:58.341231+00:00
-- url     : https://prove2.me/submissions/edf0edd8-005e-4bd3-9cd7-4202fa845a03

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsHomogeneousOfIsMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_squarefree_of_isChowForm_e1bcf340834c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isHomogIdeal_genericIdeal_0eabf1506c24
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormBaseChange_proof_7d9525206e4b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_isChowForm_map_27b2fdc9a1f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_proof_14040d77a0cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_iff_0f52654b96e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultihomog_map_iff_cd1cd76dd983
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RadicalBaseChange_proof_fda9669ff964
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomog_iff_4e11cc8773b5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)
namespace GroundTheory.Heights₂.Heights.ObjectsChow
namespace ChowFormToComplexChowForm
theorem _root_.solution (hZ : IncidenceZeroLocus.Statement) : ChowFormToComplexChowForm.Statement := by
  intro n e δ P f hP hf hδ
  have hcast : Rat.castHom ℂ = algebraMap ℚ ℂ := RingHom.ext_rat _ _
  have hC := ChowFormExtend.isChowForm_map (L := ℂ) RadicalBaseChange.proof (genericIdeal P) f hf
  rw [← hcast] at hC
  refine ⟨(isMultihomog_map_iff (Rat.castHom ℂ).injective f).mpr ((isMultiHomog_iff f).mp hδ),
    squarefree_of_isChowForm hC, fun u => ⟨fun hu => ?_, fun ⟨z, hz, hzu⟩ => ?_⟩⟩
  ·
    have hv : ∀ g ∈ incIdeal (genericIdeal P) (e + 1), aeval (fun p => u p.1 p.2) g = 0 := by
      intro g hg
      simp only [incIdeal, Ideal.mem_iInf, RingHom.mem_ker] at hg
      obtain ⟨h, rfl⟩ := (hf.2 g).1 fun w hw => hg w hw
      rw [map_mul, aeval_def, ← hcast, ← eval_map, hu, zero_mul]
    obtain ⟨y, hy0, hyQ, hyu⟩ := hZ ℚ n (e + 1) (genericIdeal P) (isHomogIdeal_genericIdeal hP) ℂ
      (fun p => u p.1 p.2) hv
    refine ⟨y, ⟨hy0, fun q hq => ?_⟩, fun j => hyu j⟩
    rw [eval_map, RingHom.ext_int (Int.castRingHom ℂ) ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)),
      ← eval₂_map, ← aeval_def]
    exact hyQ _ (Ideal.mem_map_of_mem _ hq)
  ·
    set ι := algebraMap ℂ (AlgebraicClosure ℂ)
    have hle : (genericIdeal P).map (map (Rat.castHom ℂ)) ≤
        RingHom.ker (aeval (ι ∘ z) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] AlgebraicClosure ℂ) := by
      rw [genericIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro q hq
      rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, map_map,
        RingHom.ext_int ((Rat.castHom ℂ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℂ),
        aeval_algebraMap_apply]
      exact (congrArg ι (hz.2 q hq)).trans (map_zero ι)
    have h1 := (hC.2 (map (Rat.castHom ℂ) f)).2 dvd_rfl (ι ∘ fun p => u p.1 p.2)
      ⟨ι ∘ z, fun h0 => hz.1 (funext fun i => ι.injective (by simpa using congrFun h0 i)),
        fun g hg => hle hg, fun j => by simpa [map_sum, map_mul] using congrArg ι (hzu j)⟩
    rw [aeval_algebraMap_apply] at h1
    exact ι.injective (h1.trans (map_zero ι).symm)
end ChowFormToComplexChowForm
end GroundTheory.Heights₂.Heights.ObjectsChow
