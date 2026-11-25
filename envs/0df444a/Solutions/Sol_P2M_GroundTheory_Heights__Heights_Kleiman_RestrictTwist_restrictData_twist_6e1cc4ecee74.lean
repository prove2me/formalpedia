-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_restrictData_twist_6e1cc4ecee74
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:19.011234+00:00
-- url     : https://prove2.me/submissions/7aa961b7-4030-4a11-8fcb-e80d7adaf087

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twist_sub_eq_203111ec3d6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_mul_mem__7be37290911c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_dual_bbc8f1838554
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_mul_mem_of_mem_mul_89319747f3eb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_add_db6472489522
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_mul_063c6593364d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_eq_of_subset_43355d35aad8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']
variable {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
theorem _root_.solution {Q₁ Q₂ : LineBundle S x} {Q₁' Q₂' : LineBundle S y} {r₁ r₂ : Ω → K'}
    (h₁ : RestrictData Q₁.toSubSystem hxy Q₁'.toSubSystem r₁)
    (h₂ : RestrictData Q₂.toSubSystem hxy Q₂'.toSubSystem r₂) :
    ∃ r : Ω → K', RestrictData (Q₁.toSubSystem.twist Q₂.toSubSystem) hxy
      (Q₁'.toSubSystem.twist Q₂'.toSubSystem) r := by
  classical
  choose L hL hL1 using fun I : Chart y => exists_dual Q₁ (liftChart hxy I)
  let r : Ω → K' := fun z =>
    if h : ∃ I : Chart y, z ∈ Q₂.sub (liftChart hxy I) * Q₁.sub (liftChart hxy I) then
      prodRes r₁ r₂ (L (Classical.choose h)) z else 0
  have hr : ∀ (I : Chart y) (z : Ω), z ∈ Q₂.sub (liftChart hxy I) * Q₁.sub (liftChart hxy I) →
      r z = prodRes r₁ r₂ (L I) z := by
    intro I z hz
    have hex : ∃ I : Chart y, z ∈ Q₂.sub (liftChart hxy I) * Q₁.sub (liftChart hxy I) := ⟨I, hz⟩
    simp only [r, dif_pos hex]
    have hJ := Classical.choose_spec hex
    let K : Chart y := ⟨(Classical.choose hex).1 ∪ I.1,
      (Classical.choose hex).2.1.mono Finset.subset_union_left,
      Finset.union_subset (Classical.choose hex).2.2 I.2.2⟩
    rw [prodRes_eq_of_subset h₁ h₂ (K := K) Finset.subset_union_left (hL _) (hL1 _) (hL K) (hL1 K) hJ,
      prodRes_eq_of_subset h₁ h₂ (K := K) Finset.subset_union_right (hL I) (hL1 I) (hL K) (hL1 K) hz]
  have hmem : ∀ (I : Chart y) (z : Ω), z ∈ (Q₁.toSubSystem.twist Q₂.toSubSystem).sub (liftChart hxy I) →
      z ∈ Q₂.sub (liftChart hxy I) * Q₁.sub (liftChart hxy I) := fun I z hz => by
    rwa [twist_sub_eq] at hz
  have hv : ∀ (I : Chart y) (z : Ω), z ∈ Q₂.sub (liftChart hxy I) * Q₁.sub (liftChart hxy I) →
      ∀ p ∈ L I, p.2 * z ∈ Q₂.sub (liftChart hxy I) := fun I z hz p hp =>
    mul_mem_of_mem_mul (hL I p hp).2 hz
  have hrmem : ∀ (I : Chart y), ∀ q ∈ (Q₁.toSubSystem.twist Q₂.toSubSystem).sub (liftChart hxy I),
      r q ∈ (Q₁'.toSubSystem.twist Q₂'.toSubSystem).sub I := by
    intro I q hq
    rw [twist_sub_eq, hr I q (hmem I q hq), prodRes]
    refine list_sum_mem fun w hw => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    rw [mul_comm (r₁ p.1)]
    exact Submodule.mul_mem_mul (h₂.mem I _ (hv I q (hmem I q hq) p hp)) (h₁.mem I _ (hL I p hp).1)
  refine ⟨r, hrmem, ?_, ?_, ?_⟩
  · intro I q hq q' hq'
    have hq₁ := hmem I q hq
    have hq₁' := hmem I q' hq'
    rw [hr I _ (add_mem hq₁ hq₁'), hr I _ hq₁, hr I _ hq₁']
    exact prodRes_add h₂ I (hv I q hq₁) (hv I q' hq₁')
  · intro I q hq f s e hs hf hse
    have hq₁ := hmem I q hq
    have hc : aeval x f / aeval x s ∈ chartRing S x (liftChart hxy I) := ⟨f, s, e, hs, hf, hse, rfl⟩
    rw [hr I _ (mul_mem' hc hq₁), hr I _ hq₁, prodRes, prodRes, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
    rw [show p.2 * (aeval x f / aeval x s * q) = aeval x f / aeval x s * (p.2 * q) by ring,
      h₂.smul I _ (hv I q hq₁ p hp) f s e hs hf hse]
    ring
  · intro I
    apply le_antisymm
    · exact Submodule.span_le.mpr fun _ ⟨q, hq, hrq⟩ => hrq ▸ hrmem I q hq
    · rw [twist_sub_eq Q₁'.toSubSystem Q₂'.toSubSystem I, ← h₁.span I, ← h₂.span I,
        Submodule.span_mul_span]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨_, ⟨b, hb, rfl⟩, _, ⟨a, ha, rfl⟩, rfl⟩
      have hba : b * a ∈ Q₂.sub (liftChart hxy I) * Q₁.sub (liftChart hxy I) :=
        Submodule.mul_mem_mul hb ha
      refine Submodule.subset_span ⟨b * a, ?_, ?_⟩
      · rw [twist_sub_eq]; exact hba
      · rw [hr I _ hba, prodRes_mul h₁ h₂ I (hL I) (hL1 I) ha hb, mul_comm]
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
