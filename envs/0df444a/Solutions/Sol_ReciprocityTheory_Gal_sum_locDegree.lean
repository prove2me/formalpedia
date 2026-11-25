-- Prove2me | solution 1 for ReciprocityTheory.Gal.sum_locDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:01:02.178928+00:00
-- url     : https://prove2.me/submissions/93be6ed9-6fc3-425d-8b63-c3521ef8245b

import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_ReciprocityTheory_GaloisValuations_ArithOfA
import Theorems.Thm_ReciprocityTheory_Gal_isMaximal_span_prime
import Theorems.Thm_ReciprocityTheory_Gal_liesOver_span_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
variable {F : Type*} [Field F] [NumberField F]
namespace ReciprocityTheory.Gal
theorem _root_.solution (l : ℕ) [Fact l.Prime] (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ v, v ∈ T ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    ∑ v ∈ T, locDegree v = Module.finrank ℚ F := by
  haveI := isMaximal_span_prime l
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hp0 : Ideal.span {(l : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hl0
  have h := Ideal.sum_ramification_inertia (𝓞 F) ℚ F hp0
  rw [← h]
  refine Finset.sum_nbij (fun v => v.asIdeal) ?_ ?_ ?_ ?_
  · intro v hv
    rw [IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 F)]
    haveI : v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) :=
      (liesOver_span_iff l v.asIdeal).2 ((hT v).1 hv)
    exact ⟨v.isPrime, inferInstance⟩
  · intro v _ w _ hvw
    exact HeightOneSpectrum.ext hvw
  · intro P hP
    rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 F)] at hP
    obtain ⟨hPp, hPl⟩ := hP
    have hPne : P ≠ ⊥ := by
      intro hb
      have hm := (liesOver_span_iff l P).1 hPl
      rw [hb, Ideal.mem_bot] at hm
      exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast hm)
    refine ⟨⟨P, hPp, hPne⟩, ?_, rfl⟩
    rw [Finset.mem_coe, hT]
    exact (liesOver_span_iff l P).1 hPl
  · intro v hv
    haveI : v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) :=
      (liesOver_span_iff l v.asIdeal).2 ((hT v).1 hv)
    haveI := v.isMaximal
    unfold locDegree
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(l : ℤ)}) v.asIdeal hp0,
      Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(l : ℤ)}) v.asIdeal]
end ReciprocityTheory.Gal
