-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_CutPieces_proof_0d2ae38a67a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:14.5021+00:00
-- url     : https://prove2.me/submissions/adb46d8b-06ab-4c99-88f2-17144c9ff975

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutPieces
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_CutPieces_component_mul_68293a88f0c6

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
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace CutPieces
theorem _root_.solution : CutPieces.Statement := by
  intro F _ K _ _ ι _ I x e m hI hx hnzd
  set S := weightedHomogeneousSubmodule F (blockWeight ι) with hS
  by_cases hx0 : x = 0
  · have hI1 : I = ⊤ := (Ideal.eq_top_iff_one I).2 (hnzd 1 (by simp [hx0]))
    subst hI1
    have e1 : S m ⊓ ((⊤ : Ideal (MRing ι F)) ⊔ Ideal.span {x}).restrictScalars F = S m := by
      rw [top_sup_eq, Submodule.restrictScalars_top, inf_top_eq]
    have e2 : ∀ n, S n ⊓ (⊤ : Ideal (MRing ι F)).restrictScalars F = S n := fun n => by
      rw [Submodule.restrictScalars_top, inf_top_eq]
    rw [e1, e2, e2]
    split_ifs <;> simp

  set μ := LinearMap.mulLeft F x with hμ
  have hμinj : Function.Injective μ := fun a b h => mul_left_cancel₀ hx0 h
  have hx' : x ∈ S e := hx

  have hsplit : ∀ f ∈ S m, f ∈ I ⊔ Ideal.span {x} →
      ∃ i ∈ S m ⊓ I.restrictScalars F, ∃ y : MRing ι F,
        f = i + weightedHomogeneousComponent (blockWeight ι) m (x * y) := by
    intro f hf hfI
    obtain ⟨i, hi, z, hz, rfl⟩ := Submodule.mem_sup.mp hfI
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hz
    refine ⟨weightedHomogeneousComponent (blockWeight ι) m i,
      ⟨weightedHomogeneousComponent_mem _ _ _, hI i hi m⟩, y, ?_⟩
    classical
    have h1 := weightedHomogeneousComponent_of_mem (m := m) hf
    rw [if_pos rfl, map_add] at h1
    exact h1.symm
  by_cases hem : e ≤ m
  · rw [if_pos hem]
    set A := S m ⊓ I.restrictScalars F
    set B := (S (m - e)).map μ
    have hsup : S m ⊓ (I ⊔ Ideal.span {x}).restrictScalars F = A ⊔ B := by
      apply le_antisymm
      · rintro f ⟨hf, hfI⟩
        obtain ⟨i, hi, y, rfl⟩ := hsplit f hf hfI
        rw [CutPieces.component_mul hx, if_pos hem]
        exact Submodule.add_mem_sup hi
          ⟨_, weightedHomogeneousComponent_mem _ _ _, rfl⟩
      · refine sup_le (inf_le_inf_left _ (Submodule.restrictScalars_mono F le_sup_left)) ?_
        rintro _ ⟨s, hs, rfl⟩
        refine ⟨?_, Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr (dvd_mul_right x s))⟩
        have := IsWeightedHomogeneous.mul hx' hs
        rwa [add_tsub_cancel_of_le hem] at this
    have hinf : A ⊓ B = (S (m - e) ⊓ I.restrictScalars F).map μ := by
      apply le_antisymm
      · rintro _ ⟨⟨_, hI'⟩, ⟨s, hs, rfl⟩⟩
        exact ⟨s, ⟨hs, hnzd s hI'⟩, rfl⟩
      · rintro _ ⟨s, ⟨hs, hsI⟩, rfl⟩
        refine ⟨⟨?_, I.mul_mem_left x hsI⟩, ⟨s, hs, rfl⟩⟩
        have := IsWeightedHomogeneous.mul hx' hs
        rwa [add_tsub_cancel_of_le hem] at this
    have hA : FiniteDimensional F A := Submodule.finiteDimensional_of_le inf_le_left
    have key := Submodule.finrank_sup_add_finrank_inf_eq A B
    have h1 : Module.finrank F B = Module.finrank F (S (m - e)) :=
      (Submodule.equivMapOfInjective μ hμinj _).finrank_eq.symm
    have h2 : Module.finrank F ↥((S (m - e) ⊓ I.restrictScalars F).map μ) =
        Module.finrank F ↥(S (m - e) ⊓ I.restrictScalars F) :=
      (Submodule.equivMapOfInjective μ hμinj _).finrank_eq.symm
    rw [hinf, h1, h2] at key
    rw [hsup]
    omega
  · rw [if_neg hem, add_zero]
    have hsup : S m ⊓ (I ⊔ Ideal.span {x}).restrictScalars F = S m ⊓ I.restrictScalars F := by
      apply le_antisymm
      · rintro f ⟨hf, hfI⟩
        obtain ⟨i, hi, y, rfl⟩ := hsplit f hf hfI
        rw [CutPieces.component_mul hx, if_neg hem, add_zero]
        exact hi
      · exact inf_le_inf_left _ (Submodule.restrictScalars_mono F le_sup_left)
    rw [hsup]
end CutPieces
end GroundTheory.Heights₂.Heights.NumbersDVR
