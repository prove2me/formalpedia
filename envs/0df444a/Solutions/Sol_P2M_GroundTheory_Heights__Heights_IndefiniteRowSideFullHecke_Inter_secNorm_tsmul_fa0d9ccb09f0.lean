-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_secNorm_tsmul_fa0d9ccb09f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:29:28.996262+00:00
-- url     : https://prove2.me/submissions/09cdbc5d-4a8e-419b-9714-31d0462d304b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_eval_tsmul_of_isMultiHomog_ed52743cf4a4

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial MeasureTheory Topology Filter Set
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential MIntegrable locDens)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {P : Ideal (MRing ι ℂ)} {A : HLine ι} {s : MRing ι ℂ} (hs : IsFormSec P A s)
    {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : MCone ι) :
    secNorm A s (tsmul c z) = secNorm A s z := by
  obtain ⟨a, ha, hsa, -⟩ := hs
  unfold secNorm
  rw [eval_tsmul_of_isMultiHomog hsa c z]
  have hh : A.h (tsmul c z) = (∏ k, ‖c k‖ ^ A.a k) * A.h z := A.smul c z hc
  have hpos : 0 < ∏ k, ‖c k‖ ^ A.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  have hn : ‖∏ k, c k ^ a k‖ = ∏ k, ‖c k‖ ^ A.a k := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow, ha k, zpow_natCast]
  rw [hh, norm_mul, hn, mul_div_mul_left _ _ hpos.ne']
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
