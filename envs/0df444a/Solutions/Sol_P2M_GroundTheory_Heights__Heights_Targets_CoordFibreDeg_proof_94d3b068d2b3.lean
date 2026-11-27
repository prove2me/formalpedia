-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CoordFibreDeg_proof_94d3b068d2b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:08:58.864621+00:00
-- url     : https://prove2.me/submissions/0a26e0eb-1d49-48c9-8102-526766acfecf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CoordFibreDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_FibreMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CoordRatioDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GenFibreChartDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCoordFibreDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeTrdeg_proof_69ca55d428ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordConeArithVar_proof_c88814975c4f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_proof_6c9e7d5dfa01
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_GenericPointExists_proof_ea6d93ea06df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_proof_19b16af12153
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Targets
namespace CoordFibreDeg
theorem _root_.solution (hM : FibreMultiHomog.Statement) (hD : GenFibreChartDeg.Statement)
    (hR : CoordRatioDeg.Statement) : CoordFibreDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ _ y d G i hb hZ' hZ hi
  have : CharZero G.Φ' := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hmem : (C (n : ℤ) : MRing ι') ∈ mCoordIdeal y := by
      rw [← G.genericFibre_ker_target, RingHom.mem_ker]
      simpa using hn
    simp only [mCoordIdeal, RingHom.mem_ker, mConeMap] at hmem
    simpa using hmem
  have hMH : IsMultiHomogIdeal (mCoordIdeal y) := hZ'.2.1.2.1
  choose c hc using hZ.2.1.2.2
  have hx : ∀ k, G.x ⟨k, c k⟩ ≠ 0 := fun k h => hc k (by
    rw [← G.ker_x, RingHom.mem_ker, aeval_X]
    exact h)
  have hi' : ∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0 := fun k h => hi k (by
    rw [fibreIdeal, RingHom.mem_ker, aeval_X]
    exact h)
  have h1 := Inter.ChartRankAdjoin.proof (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ'
    (fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k => G.x' ⟨q.1.1, q.2⟩) i hi'
    (hM K ι K' ι' κ v (mCoordIdeal y) G hb hMH)
  exact h1.trans ((hD K ι K' ι' κ v (mCoordIdeal y) G c i hb hMH hx hi').trans
    (hR K ι K' ι' κ v Ω y G.Φ' G.x' hb G.genericFibre_ker_target))
end CoordFibreDeg
end GroundTheory.Heights₂.Heights.Targets
