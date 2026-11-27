-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFibreRadical_proof_dcbf66814685
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:54:55.577971+00:00
-- url     : https://prove2.me/submissions/433ba7a5-4a08-4e7c-ab11-a821d76c1a90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreTor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFibreRadical
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_map_inf_eq_of_sup_inf_ker_le_7efd15ee598a

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
namespace GroundTheory.Heights₂.Heights
namespace GenericFibreRadical
theorem _root_.solution (hT : GenericFibreTor.Statement)
    (hP : GenericFibreRadicalPrime.Statement) : GenericFibreRadical.Statement := by
  intro σ _ ι _ K hK
  have hsurj : ∀ t : σ → ℂ, Function.Surjective
      (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) :=
    fun t => MvPolynomial.map_surjective _ (fun c => ⟨C c, eval_C c⟩)
  classical
  have key : ∀ s : Finset (Ideal (MvPolynomial ι (MvPolynomial σ ℂ))), (∀ p ∈ s, p.IsPrime) →
      ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
        ((s.inf id).map (MvPolynomial.map (eval t))).IsRadical := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨1, one_ne_zero, fun t _ => ?_⟩
      rw [Finset.inf_empty, Ideal.map_top]
      exact fun _ _ => Submodule.mem_top
    | insert p s hps ih =>
      intro hs
      obtain ⟨F₁, hF₁, h₁⟩ := ih (fun q hq => hs q (Finset.mem_insert_of_mem hq))
      obtain ⟨F₂, hF₂, h₂⟩ := hP σ ι p (hs p (Finset.mem_insert_self p s))
      obtain ⟨F₃, hF₃, h₃⟩ := hT σ ι (p ⊔ s.inf id)
      refine ⟨F₁ * F₂ * F₃, mul_ne_zero (mul_ne_zero hF₁ hF₂) hF₃, fun t ht => ?_⟩
      simp only [map_mul, ne_eq, mul_eq_zero, not_or] at ht
      obtain ⟨⟨ht₁, ht₂⟩, ht₃⟩ := ht
      rw [Finset.inf_insert, id, map_inf_eq_of_sup_inf_ker_le _ (hsurj t) _ _ (h₃ t ht₃)]
      exact (h₂ t ht₂).inf (h₁ t ht₁)
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing _ K
  obtain ⟨F, hF, hFt⟩ := key hfin.toFinset (fun p hp => ((hfin.mem_toFinset).1 hp).1.1)
  refine ⟨F, hF, fun t ht => ?_⟩
  have hK' : K = hfin.toFinset.inf id := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset, Ideal.sInf_minimalPrimes]
    exact le_antisymm Ideal.le_radical hK
  rw [hK']
  exact hFt t ht
end GenericFibreRadical
end GroundTheory.Heights₂.Heights
