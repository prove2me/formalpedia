-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_divCycle_eq_of_cross_e8d8a257b3c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:29.515436+00:00
-- url     : https://prove2.me/submissions/062cdba8-fc5b-4952-8f66-63030097a47b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_length_localized_eq_9df2ed0bc3a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_mem_minimalPrimes_iff_5f70c654c603

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {K : Type*} {κ : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution (I : Ideal (NumbersDVR.MRing κ R)) {f g f' g' : NumbersDVR.MRing κ R}
    {W : Ideal (NumbersDVR.MRing κ R)} [W.IsPrime] (hf' : f' ∉ W) (hg' : g' ∉ W)
    (hrel : f * g' - f' * g ∈ I) : NumbersDVR.divCycle I f W = NumbersDVR.divCycle I g W := by
  set J := I ⊔ Ideal.span {f * g'} with hJdef
  have hfg : f * g' ∈ J := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hIJ : I ≤ J := le_sup_left
  have hf'g : f' * g ∈ J := by
    have h := J.sub_mem hfg (hIJ hrel)
    rwa [sub_sub_cancel] at h
  have h1 : J ≤ I ⊔ Ideal.span {f} := sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
    (Ideal.mem_sup_right (Ideal.mul_mem_right g' _ (Ideal.mem_span_singleton_self f))))
  have h2 : J ≤ I ⊔ Ideal.span {g} := by
    refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    have h := Ideal.add_mem _ (Ideal.mem_sup_left hrel : _ ∈ I ⊔ Ideal.span {g})
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ f' (Ideal.mem_span_singleton_self g)) :
        _ ∈ I ⊔ Ideal.span {g})
    rwa [sub_add_cancel] at h
  have hm1 : ∀ x ∈ I ⊔ Ideal.span {f}, g' * x ∈ J := by
    intro x hx
    obtain ⟨i, hi, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [mul_add, show g' * (r * f) = r * (f * g') by ring]
    exact J.add_mem (hIJ (I.mul_mem_left _ hi)) (J.mul_mem_left _ hfg)
  have hm2 : ∀ x ∈ I ⊔ Ideal.span {g}, f' * x ∈ J := by
    intro x hx
    obtain ⟨i, hi, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [mul_add, show f' * (r * g) = r * (f' * g) by ring]
    exact J.add_mem (hIJ (I.mul_mem_left _ hi)) (J.mul_mem_left _ hf'g)
  have e1 := mem_minimalPrimes_iff h1 hg' hm1
  have e2 := mem_minimalPrimes_iff h2 hf' hm2
  have l1 := length_localized_eq h1 hg' hm1
  have l2 := length_localized_eq h2 hf' hm2
  unfold NumbersDVR.divCycle
  by_cases hc : W ∈ (I ⊔ Ideal.span {f}).minimalPrimes ∧ NumbersDVR.IsRelevant W
  · have hc' : W ∈ (I ⊔ Ideal.span {g}).minimalPrimes ∧ NumbersDVR.IsRelevant W :=
      ⟨e2.mp (e1.mpr hc.1), hc.2⟩
    rw [dif_pos hc, dif_pos hc']
    exact congrArg (fun m : ℕ∞ ↦ (m.toNat : ℤ)) (l1.symm.trans l2)
  · have hc' : ¬ (W ∈ (I ⊔ Ideal.span {g}).minimalPrimes ∧ NumbersDVR.IsRelevant W) :=
      fun h ↦ hc ⟨e1.mp (e2.mpr h.1), h.2⟩
    rw [dif_neg hc, dif_neg hc']
end GroundTheory.Heights₂.Heights.SectionCycle
