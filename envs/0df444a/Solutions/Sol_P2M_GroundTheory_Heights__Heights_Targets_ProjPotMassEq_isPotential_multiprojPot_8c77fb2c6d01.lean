-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_isPotential_multiprojPot_8c77fb2c6d01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:29:29.551864+00:00
-- url     : https://prove2.me/submissions/4743ca1f-6214-4f44-ba4b-32af10075ea7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEqGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_blockSum_pos_f3a6ed830dc6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_isPotential_congr_7067f4d9748e
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotentialPullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isPotential_potOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSmoothHerm_sqMetric


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open scoped ContDiff
open GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)}
namespace GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
theorem _root_.solution {V : Set R.X} {BV : FinHolAtlas n V}
    (hH : HoloMap BV R.A Subtype.val) : IsPotential BV (multiprojPot R V) := by
  refine isPotential_congr BV (P := (potOf R (HermLine.sqMetric (fun _ => 2))).pullback
    Subtype.val hH.1) (fun _ => rfl) (fun x z hz => ?_)
    (isPotentialPullback R.A BV Subtype.val hH _
      (isPotential_potOf R (isSmoothHerm_sqMetric _)))
  have hm := (R.mem x.1 z.1 hz).1
  show Real.log (∏ k, Real.sqrt (∑ i, ‖R.lift x.1 z.1 ⟨k, i⟩‖ ^ 2) ^ 2) =
    ∑ k, Real.log (∑ i, ‖R.lift x.1 z.1 ⟨k, i⟩‖ ^ 2)
  rw [Finset.prod_congr rfl fun k _ => Real.sq_sqrt (by positivity),
    Real.log_prod fun k _ => (blockSum_pos hm k).ne']
end GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
