-- Prove2me | solution 1 for PI.VolStabW.RPA.kap_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:57:14.615923+00:00
-- url     : https://prove2.me/submissions/197aaec9-17cf-42a6-af3f-af247cee39a7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ESSymmApply
import Theorems.Thm_PI_VolStabW_RPA_kap_eval_null

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
variable (m L)
variable [∀ i, SigmaFinite (m i)]
variable {m L}
namespace PI.VolStabW.RPA
theorem _root_.solution [Countable ι] (hLm : ∀ i, MeasurableSet (L i)) (S : Finset ι) :
    ∀ᵐ x ∂kap m L S, ∀ i, (i ∈ S → x i ∉ L i) ∧ (i ∉ S → x i ∈ L i) := by
  classical
  rw [ae_all_iff]
  intro i
  by_cases hi : i ∈ S
  · have h0 : kap m L S {x | x i ∈ L i} = 0 :=
      kap_eval_null (hLm i) (by simp [mu, hi, Measure.restrict_apply (hLm i)])
    refine measure_mono_null (fun x hx => ?_) h0
    simp only [Set.mem_setOf_eq] at hx ⊢
    by_contra hxi
    exact hx ⟨fun _ => hxi, fun h => absurd hi h⟩
  · have h0 : kap m L S {x | x i ∈ (L i)ᶜ} = 0 :=
      kap_eval_null (hLm i).compl (by simp [mu, hi, Measure.restrict_apply (hLm i).compl])
    refine measure_mono_null (fun x hx => ?_) h0
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff] at hx ⊢
    by_contra hxi
    exact hx ⟨fun h => absurd h hi, fun _ => hxi⟩
end PI.VolStabW.RPA
