-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.locDens_cons_rsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:03.784488+00:00
-- url     : https://prove2.me/submissions/7bc23434-22a6-4376-95c0-1144c8bd35c7

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_cons
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_hessC_const_mul__03a5d330ff52
import Theorems.Thm_ReciprocityTheory_AnForm_M_mdisc_cons_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff ComplexOrder
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas (e + 1) X) (c : ℝ) (P : LocPot X)
    (Φ : Fin e → LocPot X) (j : Fin A.n) (y : Fin (e + 1) → ℂ) :
    locDens A (Fin.cons (P.rsmul c) Φ) j y = c * locDens A (Fin.cons P Φ) j y := by
  rw [locDens_cons, locDens_cons]
  have : (fun y' => (P.rsmul c).φ ((A.chart j).symm y) ((A.chart j).symm y')) =
      fun y' => c * P.φ ((A.chart j).symm y) ((A.chart j).symm y') := rfl
  rw [this, hessC_const_mul', mdisc_cons_smul, Complex.re_ofReal_mul]
  ring
end ReciprocityTheory.AnForm.M
