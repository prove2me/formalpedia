-- Prove2me | solution 1 for PI.VolStabW.DeterminantAdmissible.pre_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:37:58.552099+00:00
-- url     : https://prove2.me/submissions/e60df508-a6c5-486f-896a-16e97157db2b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_boxes_seq
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_mem_upd
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_isBoxD_upd
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_open_eq_sUnion


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
open Classical
namespace PI.VolStabW.DeterminantAdmissible
theorem _root_.solution (c : ι) (v : HeightOneSpectrum (𝓞 F)) (W : Set (Fv F v)) (hW : IsOpen W) :
    MeasurableSet[generateFrom (boxes F ι)] ((fun y : ι → Af F => y c v) ⁻¹' W) := by
  classical
  let m' : MeasurableSpace (ι → Af F) := generateFrom (boxes F ι)
  obtain ⟨T, hT, hTc, rfl⟩ := open_eq_sUnion v hW
  obtain ⟨bs, hbs, hbU⟩ := boxes_seq (F := F) (ι := ι)
  choose Db hDb hbe using hbs
  have e : (fun y : ι → Af F => y c v) ⁻¹' ⋃₀ T = ⋃ C ∈ T, ⋃ n, boxS (upd (Db n) c v C) := by
    ext y
    simp only [mem_preimage, mem_sUnion, mem_iUnion, mem_upd, exists_prop]
    constructor
    · rintro ⟨C, hC, hy⟩
      have hy' : y ∈ ⋃ n, bs n := by
        rw [hbU]
        trivial
      obtain ⟨n, hn⟩ := mem_iUnion.1 hy'
      exact ⟨C, hC, n, by rw [← hbe n]; exact hn, hy⟩
    · rintro ⟨C, hC, n, -, hy⟩
      exact ⟨C, hC, hy⟩
  rw [e]
  exact MeasurableSet.biUnion hT fun C hC => MeasurableSet.iUnion fun n =>
    measurableSet_generateFrom ⟨_, isBoxD_upd (hDb n) c v (hTc C hC), rfl⟩
end PI.VolStabW.DeterminantAdmissible
