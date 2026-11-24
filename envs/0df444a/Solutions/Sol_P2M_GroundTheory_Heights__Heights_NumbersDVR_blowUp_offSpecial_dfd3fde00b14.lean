-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUp_offSpecial_dfd3fde00b14
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:35.095542+00:00
-- url     : https://prove2.me/submissions/24c69a7b-ff27-4ba9-9417-e6ef8d36bc59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_liftForm_facts_3c10203679d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_powMonomial_not_mem_390e62bd3aa2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpCof_relation_be2eb66028dd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
variable {J : Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {P : Ideal (MRing ι R)} (hP : P.IsPrime) {s g f m : MRing ι R} (e : K → ℕ)
    (hg : g ∉ P) {W : Ideal (MRing (extIdx ι (BlowUpIdx ι)) R)} (hW : W.IsPrime)
    (hQW : blowUpOf P (blowUpGens s g f m e) ≤ W) (hrel : IsRelevant W) {u₀ v₀ : MRing ι R}
    (hv : liftForm v₀ ∉ W) (h : u₀ * f - v₀ * g ∈ P) :
    ∃ i : ∀ k, ι k, liftForm (powMonomial e i) ∉ W ∧ newVar (some (some i)) ∉ W ∧
      (liftForm m ∉ W → newVar (some none) ∉ W) := by
  have mnm : ∀ {x y}, x ∉ W → y ∉ W → x * y ∉ W := fun hx hy hxy => (hW.mem_or_mem hxy).elim hx hy
  obtain ⟨hW₀, -, hrel₀, j, hj⟩ := comap_liftForm_facts hW hQW hrel
  obtain ⟨i, hi⟩ := powMonomial_not_mem hW₀ hrel₀ e
  have hi' : liftForm (powMonomial e i) ∉ W := hi
  have key : ∀ j', liftForm (blowUpCof s m e u₀ v₀ j') ∉ W → newVar j' ∉ W := by
    intro j' ha hj'
    have hr := hQW (blowUpCof_relation hP e hg h j j')
    have h3 : newVar j * liftForm (blowUpCof s m e u₀ v₀ j') ∈ W := by
      have h4 := W.add_mem hr (W.mul_mem_right (liftForm (blowUpCof s m e u₀ v₀ j)) hj')
      rwa [sub_add_cancel] at h4
    exact mnm hj ha h3
  refine ⟨i, hi', key _ ?_, fun hm => key _ ?_⟩
  · show liftForm (v₀ * powMonomial e i) ∉ W
    rw [map_mul]; exact mnm hv hi'
  · show liftForm (v₀ * m) ∉ W
    rw [map_mul]; exact mnm hv hm
end GroundTheory.Heights₂.Heights.NumbersDVR
