-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialCycleEval_proof_017382fa96cd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:21.803029+00:00
-- url     : https://prove2.me/submissions/b80e0a74-139c-460a-9dcc-da1ac5409b23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialCycleEval

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace SpecialCycleEval
theorem _root_.solution (h1 : SpecialIdealCorresp.Statement.{u})
    (h2 : SpecialIdealSurj.Statement.{u}) (h3 : SpecialMultAt.Statement.{u}) :
    SpecialCycleEval.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P n
  classical
  let s : Set (Ideal (MRing ι O)) :=
    {W | W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ∧ IsRelevant W}
  let t : Set (Ideal (MRing ι (IsLocalRing.ResidueField O))) :=
    {V | V ∈ (specialIdeal P).minimalPrimes ∧ IsRelevant V}
  have hsupp1 : Function.support (fun W => divCycle P (C ϖ) W * n (specialIdeal W)) ⊆ s := by
    intro W hW
    by_contra h
    apply hW
    show divCycle P (C ϖ) W * n (specialIdeal W) = 0
    have h' : ¬ (W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ∧ IsRelevant W) := h
    unfold divCycle
    rw [dif_neg h', zero_mul]
  have hsupp2 : Function.support (fun V => idealCycle (specialIdeal P) V * n V) ⊆ t := by
    intro V hV
    by_contra h
    apply hV
    show idealCycle (specialIdeal P) V * n V = 0
    have h' : ¬ (V ∈ (specialIdeal P).minimalPrimes ∧ IsRelevant V) := h
    unfold idealCycle
    rw [dif_neg h', zero_mul]
  have hmem : ∀ W ∈ s, W.IsPrime ∧ (C ϖ : MRing ι O) ∈ W := fun W hW =>
    ⟨hW.1.1.1, hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))⟩
  have hmaps : ∀ W ∈ s, specialIdeal W ∈ t := by
    intro W hW
    obtain ⟨hp, hc⟩ := hmem W hW
    obtain ⟨-, hmin, hrel, -⟩ := h1 O ϖ hϖ K ι P W hp hc
    exact ⟨hmin.mp hW.1, hrel.mp hW.2⟩
  have e1 : (∑ᶠ W, divCycle P (C ϖ) W * n (specialIdeal W)) =
      ∑ᶠ W ∈ s, divCycle P (C ϖ) W * n (specialIdeal W) := by
    rw [finsum_mem_def, Set.indicator_eq_self.mpr hsupp1]
  have e2 : (∑ᶠ V, idealCycle (specialIdeal P) V * n V) =
      ∑ᶠ V ∈ t, idealCycle (specialIdeal P) V * n V := by
    rw [finsum_mem_def, Set.indicator_eq_self.mpr hsupp2]
  show (∑ᶠ W, divCycle P (C ϖ) W * n (specialIdeal W)) =
    ∑ᶠ V, idealCycle (specialIdeal P) V * n V
  rw [e1, e2]
  refine finsum_mem_eq_of_bijOn specialIdeal ⟨hmaps, ?_, ?_⟩ ?_
  · intro W hW W' hW' heq
    obtain ⟨hp, hc⟩ := hmem W hW
    obtain ⟨hp', hc'⟩ := hmem W' hW'
    exact ((h1 O ϖ hϖ K ι P W hp hc).2.2.2 W' hp' hc' heq.symm).symm
  · intro V hV
    have hVp : V.IsPrime := hV.1.1.1
    obtain ⟨W, hWp, hc, rfl⟩ := h2 O ϖ hϖ K ι V hVp
    obtain ⟨-, hmin, hrel, -⟩ := h1 O ϖ hϖ K ι P W hWp hc
    exact ⟨W, ⟨hmin.mpr hV.1, hrel.mpr hV.2⟩, rfl⟩
  · intro W hW
    obtain ⟨hp, hc⟩ := hmem W hW
    have := hp
    have := (h1 O ϖ hϖ K ι P W hp hc).1
    have hm := h3 O ϖ hϖ K ι P W hc
    congr 1
    unfold divCycle idealCycle
    have hW' : W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ∧ IsRelevant W := hW
    have hV' : specialIdeal W ∈ (specialIdeal P).minimalPrimes ∧ IsRelevant (specialIdeal W) :=
      hmaps W hW
    rw [dif_pos hW', dif_pos hV']
    exact congrArg (fun x : ℕ∞ => ((x.toNat : ℕ) : ℤ)) hm
end SpecialCycleEval
end GroundTheory.Heights₂.Heights.NumbersDVR
