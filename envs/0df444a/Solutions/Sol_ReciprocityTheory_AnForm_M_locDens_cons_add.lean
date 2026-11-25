-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.locDens_cons_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:25.510799+00:00
-- url     : https://prove2.me/submissions/23047d80-4154-48f2-b32a-882b705ee44d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Theorems.Thm_ReciprocityTheory_AnForm_M_potential_contDiffAt
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_cons
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_add__d2d06fbdee79
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_hessC_add__c2c0858c9e7b
import Theorems.Thm_ReciprocityTheory_AnForm_M_mdisc_cons_add


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
theorem _root_.solution (A : FinHolAtlas (e + 1) X) (P Q : LocPot X) (Φ : Fin e → LocPot X)
    (hP : IsPotential A P) (hQ : IsPotential A Q) (j : Fin A.n) {y : Fin (e + 1) → ℂ}
    (hy : y ∈ (A.chart j).target) :
    locDens A (Fin.cons (P + Q) Φ) j y =
      locDens A (Fin.cons P Φ) j y + locDens A (Fin.cons Q Φ) j y := by
  rw [locDens_cons, locDens_cons, locDens_cons]
  have : (fun y' => (P + Q).φ ((A.chart j).symm y) ((A.chart j).symm y')) =
      fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y') +
        Q.φ ((A.chart j).symm y) ((A.chart j).symm y') := rfl
  rw [this, hessC_add' _ _ _ (potential_contDiffAt A P hP j hy) (potential_contDiffAt A Q hQ j hy),
    mdisc_cons_add, Complex.add_re]
  ring
end ReciprocityTheory.AnForm.M
