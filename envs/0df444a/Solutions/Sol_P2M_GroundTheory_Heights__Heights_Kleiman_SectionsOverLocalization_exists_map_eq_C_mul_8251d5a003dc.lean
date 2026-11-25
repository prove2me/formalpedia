-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_map_eq_C_mul_8251d5a003dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:18:33.002655+00:00
-- url     : https://prove2.me/submissions/5dc00007-6ae5-45d0-8677-0b47ea8c870d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulMemSecsTwistIdealSys

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial Kleiman
noncomputable section
variable {S : Type*} [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] {O : Type*} [CommRing O] [Algebra S O]
  [IsLocalization.AtPrime O 𝔪] {Ω : Type*} [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
  {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
theorem _root_.solution (f : Poly O N) :
    ∃ t : S, t ∉ 𝔪 ∧ ∃ g : Poly S N, map (algebraMap S O) g = C (algebraMap S O t) * f ∧
      ∀ d, g.coeff d ≠ 0 → f.coeff d ≠ 0 := by
  classical
  obtain ⟨⟨t, ht⟩, hb⟩ := IsLocalization.exist_integer_multiples 𝔪.primeCompl f.support (fun d => f.coeff d)
  have hb' : ∀ d ∈ f.support, ∃ r : S, algebraMap S O r = t • f.coeff d :=
    fun d hd => RingHom.mem_rangeS.mp (hb d hd)
  choose! c hc using hb'
  have hcoeff : ∀ d, (∑ d' ∈ f.support, monomial d' (c d') : Poly S N).coeff d =
      if d ∈ f.support then c d else 0 := by
    intro d
    rw [coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
  refine ⟨t, ht, ∑ d' ∈ f.support, monomial d' (c d'), ?_, ?_⟩
  · ext d
    rw [coeff_map, coeff_C_mul, hcoeff]
    split_ifs with hd
    · rw [hc d hd, Algebra.smul_def]
    · rw [mem_support_iff, not_not] at hd
      rw [hd, map_zero, mul_zero]
  · intro d hd
    rw [hcoeff] at hd
    split_ifs at hd with h
    · exact mem_support_iff.mp h
    · exact absurd rfl hd
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
