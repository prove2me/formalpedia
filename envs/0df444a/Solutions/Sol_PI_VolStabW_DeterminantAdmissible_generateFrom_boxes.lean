-- Prove2me | solution 1 for PI.VolStabW.DeterminantAdmissible.generateFrom_boxes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:47:45.232993+00:00
-- url     : https://prove2.me/submissions/88a4f186-c215-45ae-bfec-26b42f2a80d0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_isCompact_boxS
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_pre_mem
import Theorems.Thm_PI_VolStabW_TopoPolish_polish_of_lcsc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DeterminantAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
namespace PI.VolStabW.DeterminantAdmissible
theorem _root_.solution : generateFrom (boxes F ι) = (MeasurableSpace.pi : MeasurableSpace (ι → Af F)) := by
  classical
  refine le_antisymm (generateFrom_le ?_) ?_
  · rintro _ ⟨D, hD, rfl⟩
    exact (isCompact_boxS hD).isClosed.measurableSet
  · intro s hs
    let Ev : (ι → Af F) → (ι → ∀ v : HeightOneSpectrum (𝓞 F), Fv F v) := fun y c v => y c v
    have hcont : Continuous Ev := continuous_pi fun c => continuous_pi fun v =>
      (RestrictedProduct.continuous_eval v).comp (continuous_apply c)
    have hinj : Function.Injective Ev := fun y y' h =>
      funext fun c => Subtype.ext (funext fun v => congrFun (congrFun h c) v)
    haveI : PolishSpace (ι → Af F) := TopoPolish.polish_of_lcsc _
    have hE := hcont.measurableEmbedding hinj
    have hc : ∀ c v, (borel (Fv F v)).comap (fun y : ι → Af F => y c v) ≤ generateFrom (boxes F ι) := by
      intro c v
      rw [borel, MeasurableSpace.comap_generateFrom]
      refine generateFrom_le ?_
      rintro _ ⟨W, hW, rfl⟩
      exact pre_mem c v W hW
    have hEv : (MeasurableSpace.pi : MeasurableSpace (ι → ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)).comap Ev
        ≤ generateFrom (boxes F ι) := by
      simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
      exact iSup_le fun c => iSup_le fun v => hc c v
    rw [← hinj.preimage_image s]
    exact hEv _ ⟨_, hE.measurableSet_image.2 hs, rfl⟩
end PI.VolStabW.DeterminantAdmissible
