-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.dI_target_of_mIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:16:09.736102+00:00
-- url     : https://prove2.me/submissions/ea42c34f-79ba-468d-a975-78bd5ca1d956

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_chartDens_locDens
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_target_of_weights
import Theorems.Thm_ReciprocityTheory_AnForm_M_existsPartition
import Theorems.Thm_ReciprocityTheory_AnForm_M_integrableOn_weight


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
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (g : X → ℝ) (hg : MIntegrable A Φ g)
    (k : Fin A.n) :
    IntegrableOn (fun y => g ((A.chart k).symm y) * locDens A Φ k y) (A.chart k).target := by
  obtain ⟨P⟩ := existsPartition A
  exact dI_target_of_weights A P (dI_chartDens_locDens A Φ hΦ) g
    (fun j => integrableOn_weight A P Φ g hg j) k
end ReciprocityTheory.AnForm.M
