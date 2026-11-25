-- Prove2me | solution 1 for ReciprocityTheory.Cheb.cyclotomic_irreducible_of_forall_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:06:09.507065+00:00
-- url     : https://prove2.me/submissions/d6126ffc-912a-45e5-b98c-fd5102cd9768

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CyclotomicIrreducibleOfForallIsUnramifiedAt
import Theorems.Thm_ReciprocityTheory_Cheb_cyclotomic_irreducible_of_isUnramifiedAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Cheb
open Polynomial NumberField
namespace ReciprocityTheory.Cheb
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    {l : ℕ} (hl : l.Prime)
    (h : ∀ (P : Ideal (𝓞 K)) [P.IsPrime], (l : 𝓞 K) ∈ P → Algebra.IsUnramifiedAt ℤ P) :
    Irreducible (cyclotomic l K) := by
  have hnu : ¬ IsUnit (l : 𝓞 K) := by
    intro hu
    have h1 := hu.map (Algebra.norm ℤ (S := 𝓞 K))
    rw [show (l : 𝓞 K) = algebraMap ℤ (𝓞 K) (l : ℤ) by simp, Algebra.norm_algebraMap,
      isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq] at h1
    simp at h1
    exact hl.one_lt.ne' h1
  obtain ⟨M, hM, hlM⟩ := Ideal.exists_le_maximal (Ideal.span {(l : 𝓞 K)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hlM' : (l : 𝓞 K) ∈ M := hlM (Ideal.mem_span_singleton_self _)
  haveI := h M hlM'
  exact cyclotomic_irreducible_of_isUnramifiedAt hl M hlM'
end ReciprocityTheory.Cheb
