-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockDimension_ker_oldMap_e83711f0f9ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:33:56.37436+00:00
-- url     : https://prove2.me/submissions/f3f11b25-54be-48d1-8021-cacce7126d3a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicNew
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_plusMap_X_old_c1a40a519d86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_oldMap_X_e33851c6039e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_oldMap_of_homog_2ffd1e4573b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


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
open GroundTheory.Heights₂.Heights.AddBlockDimension
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}
  (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.AddBlockDimension
theorem _root_.solution : RingHom.ker (oldMap D) = P.ideal := by
  ext f
  rw [RingHom.mem_ker]
  constructor
  · intro hf

    let ev : MvPolynomial (Option ι) P.FunField →+* P.FunField :=
      (aeval (R := P.FunField) fun _ : Option ι ↦ (1 : P.FunField)).toRingHom
    have hev : ev.comp (oldMap D) = P.mkF :=
      MvPolynomial.ringHom_ext (fun m ↦ by simp) (fun v ↦ by
        simp [ev, oldMap_X, plusMap_X_old])
    have := congrArg (fun φ : MvPolynomial (Coord n) ℤ →+* P.FunField ↦ φ f) hev
    simp only [RingHom.comp_apply, hf, map_zero] at this
    exact (P.mkF_eq_zero_iff f).mp this.symm
  · intro hf
    rw [← sum_weightedHomogeneousComponent (coordDeg n) f,
      map_finsum _ (weightedHomogeneousComponent_finsupp f)]
    refine finsum_eq_zero_of_forall_eq_zero fun m ↦ ?_
    rw [oldMap_of_homog D (weightedHomogeneousComponent_isWeightedHomogeneous m f),
      (P.mkF_eq_zero_iff _).mpr (P.homogeneous f hf m), map_zero, mul_zero]
end GroundTheory.Heights₂.Heights.AddBlockDimension
