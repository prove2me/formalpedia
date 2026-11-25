-- Prove2me | solution 1 for PI.VolStabW.RPA.tl_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:57.263059+00:00
-- url     : https://prove2.me/submissions/0cb094d5-5d49-4d86-a6ca-88d3e51c1514

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ESSymmApply
import Theorems.Thm_PI_VolStabW_RPA_hasProd_ind

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RPA
open MeasureTheory Filter Finset
open scoped NNReal ENNReal
variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable (m : ∀ i, Measure (W i)) (L : ∀ i, Set (W i))
variable {m L}
namespace PI.VolStabW.RPA
theorem _root_.solution [DecidableEq ι] (hT : TailH m L) {S T : Finset ι} (h : S ⊆ T) :
    tl m L S = (∏ i ∈ T \ S, am m L i) * tl m L T := by
  classical
  have h1 := hasProd_ind hT S
  have h2 := hasProd_ind hT T
  have h3 : HasProd (((T \ S : Finset ι) : Set ι).mulIndicator (am m L)) (∏ i ∈ T \ S, am m L i) := by
    have h5 : HasProd (((T \ S : Finset ι) : Set ι).mulIndicator (am m L))
        (∏ b ∈ T \ S, ((T \ S : Finset ι) : Set ι).mulIndicator (am m L) b) := hasProd_prod_of_ne_finset_one (fun b hb => Set.mulIndicator_apply_eq_one.mpr (fun hb' => absurd (Finset.mem_coe.mp hb') hb))
    convert h5 using 1
    exact Finset.prod_congr rfl (fun i hi => (Set.mulIndicator_of_mem (Finset.mem_coe.mpr hi) _).symm)
  have h4 := h3.mul h2
  refine h1.unique ?_
  convert h4 using 1
  funext i
  by_cases hiS : i ∈ S
  · have hiT := h hiS
    simp [Set.mulIndicator_apply, hiT, hiS]
  · by_cases hiT : i ∈ T <;> simp [Set.mulIndicator_apply, hiT, hiS]
end PI.VolStabW.RPA
