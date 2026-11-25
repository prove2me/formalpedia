-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_regMax_of_injective_e20efb725643
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:32:05.722419+00:00
-- url     : https://prove2.me/submissions/81c54af2-b84a-4b33-8131-70e83cae6587

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_regMax_comp_equiv_0d69f3f85194
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_regMax_subtype_16df40b114c4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory
open ReciprocityTheory.AnForm.A (regMax tmax kθ)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {κ ι : Type} [Fintype κ] [Nonempty κ] [Fintype ι] [Nonempty ι]
    (f : κ → ι) (hf : Function.Injective f) {η : ℝ} (hη : 0 ≤ η) (t : ι → ℝ)
    (hdom : ∀ i, (∀ k, f k ≠ i) → ∃ k, t i + η ≤ t (f k)) :
    regMax η t = regMax η (t ∘ f) := by
  classical
  have : Nonempty {i // i ∈ Set.range f} :=
    ⟨⟨f (Classical.arbitrary κ), Set.mem_range_self _⟩⟩
  rw [regMax_subtype (fun i => i ∈ Set.range f) hη t ?_]
  · convert (regMax_comp_equiv (Equiv.ofInjective f hf) η
      (fun k : {i // i ∈ Set.range f} => t k)).symm using 2
    funext k
    simp
  · intro i hi
    obtain ⟨k, hk⟩ := hdom i fun k hk => hi ⟨k, hk⟩
    exact ⟨f k, Set.mem_range_self _, hk⟩
end GroundTheory.Heights₂.Heights.Regular
