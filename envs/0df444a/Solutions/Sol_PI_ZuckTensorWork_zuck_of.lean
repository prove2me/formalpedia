-- Prove2me | solution 1 for PI.ZuckTensorWork.zuck_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:18:23.42864+00:00
-- url     : https://prove2.me/submissions/55c5626f-85d2-42f6-a233-c07f43c2b6bd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_DSExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ZuckDualOf
import Theorems.Thm_PI_ZuckTensorWork_fam_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
attribute [instance] Fam.nH Fam.iH Fam.cH
namespace PI.ZuckTensorWork
theorem _root_.solution (hE : PI.DSExist) (hI : Ineq) (hN : NormNe) (hT : ToSum) (hO : OfSum) : Zuck := by
  classical
  intro n ε μ H _ _ _ σ hμ hσ hg
  obtain ⟨F, hF⟩ := fam_of hE ε (fun s => μ + Pi.single s 1)
  refine ⟨{ Sm := Finset.univ.filter fun s => IsHCParam (μ + Pi.single s 1)
            Hs := F.Hs, σs := F.σs
            ds := fun s hs => ⟨(Finset.mem_filter.1 hs).2, hF s (Finset.mem_filter.1 hs).2⟩
            inequiv := fun s hs s' hs' hne =>
              hI n ε (μ + Pi.single s 1) (μ + Pi.single s' 1) (hN n ε μ hμ s s' hne).1 (F.Hs s) (F.σs s) (hF s (Finset.mem_filter.1 hs).2) (F.Hs s') (F.σs s')
                (hF s' (Finset.mem_filter.1 hs').2)
            toSum := fun v w x y hv hw => by
              obtain ⟨ι, i1, sI, vI, wI, h1, h2⟩ := hT n ε μ H σ hμ hσ hg F hF v w x y hv hw
              exact ⟨ι, i1, sI, vI, wI, fun i => ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, (h1 i).1⟩, (h1 i).2⟩, h2⟩
            ofSum := fun s hs v w hv hw =>
              hO n ε μ H σ hμ hσ hg s (Finset.mem_filter.1 hs).2 (F.Hs s) (F.σs s) (hF s (Finset.mem_filter.1 hs).2) v w hv hw }, fun s => ?_⟩
  simp
end PI.ZuckTensorWork
