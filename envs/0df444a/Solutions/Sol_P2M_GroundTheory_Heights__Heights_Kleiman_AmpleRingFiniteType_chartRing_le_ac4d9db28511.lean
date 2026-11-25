-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_chartRing_le_ac4d9db28511
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:20:26.092846+00:00
-- url     : https://prove2.me/submissions/5edc0e32-bdad-4781-a569-bc97956387a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingFiniteTypeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleRingFiniteType
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_aeval_div_pow_3ee1d0390a06
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_mem_chartGens_0a4e70cbfceb

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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
theorem _root_.solution (J : Chart x) :
    chartRing S x J ≤ Algebra.adjoin S (chartGens J : Set Ω) := by
  rintro _ ⟨f, s, e, hs, hf, hse, rfl⟩
  obtain ⟨l, hl⟩ := J.2.1
  have hxl : x l ≠ 0 := (mem_support x).mp (J.2.2 hl)
  have hmon : ∀ s ∈ monos (S := S) J.1, ∃ e, s.IsHomogeneous e ∧
      x l ^ e / aeval x s ∈ Algebra.adjoin S (chartGens J : Set Ω) := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨i, hi, rfl⟩ := hs
      refine ⟨1, isHomogeneous_X S i, ?_⟩
      rw [pow_one, aeval_X]
      exact Algebra.subset_adjoin (Finset.mem_coe.mpr (mem_chartGens l hi))
    | one => exact ⟨0, isHomogeneous_one _ _, by rw [pow_zero, map_one, div_one]; exact one_mem _⟩
    | mul s s' _ _ h h' =>
      obtain ⟨e, he, hW⟩ := h
      obtain ⟨e', he', hW'⟩ := h'
      refine ⟨e + e', he.mul he', ?_⟩
      rw [pow_add, map_mul, mul_div_mul_comm]
      exact mul_mem hW hW'
  obtain ⟨e', he', hW⟩ := hmon s hs
  have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos J hs
  have hee : e' = e := he'.inj_right hse (fun h => hs0 (by rw [h, map_zero]))
  subst hee
  have hf' : aeval x f / x l ^ e' ∈ Algebra.adjoin S (chartGens J : Set Ω) := by
    rw [← aeval_div_pow hf (x l)]
    have h1 : aeval (fun i => x i / x l) f ∈ Algebra.adjoin S (Set.range fun i => x i / x l) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨f, rfl⟩
    exact Algebra.adjoin_le (Set.range_subset_iff.mpr fun i =>
      Algebra.subset_adjoin (Finset.mem_coe.mpr (mem_chartGens i hl))) h1
  have e1 : aeval x f / aeval x s = (aeval x f / x l ^ e') * (x l ^ e' / aeval x s) := by
    rw [div_mul_div_cancel₀ (pow_ne_zero _ hxl)]
  rw [e1]
  exact mul_mem hf' hW
end GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
