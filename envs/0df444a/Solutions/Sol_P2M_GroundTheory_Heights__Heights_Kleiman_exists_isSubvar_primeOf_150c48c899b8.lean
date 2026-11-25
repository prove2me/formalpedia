-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_isSubvar_primeOf_150c48c899b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:23:31.676265+00:00
-- url     : https://prove2.me/submissions/bf31e19a-0bbe-4e7b-9b96-a42f347bb6e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_mem_primeOf_077b7ab281b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hx : x ≠ 0) : ∃ d : ℕ, IsSubvar x (primeOf (S := k) x) d := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hXi : (X i : Poly k N) ∉ primeOf (S := k) x := by
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X]
    exact hi
  have hle : ringKrullDim (Poly k N ⧸ primeOf (S := k) x) ≤ ((N + 1 : ℕ) : WithBot ℕ∞) := by
    refine (ringKrullDim_quotient_le _).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
  have hpos : ¬ ringKrullDim (Poly k N ⧸ primeOf (S := k) x) ≤ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 (Poly k N ⧸ primeOf (S := k) x) := Ring.krullDimLE_iff.mpr (by simpa using h0)
    have hF : IsField (Poly k N ⧸ primeOf (S := k) x) := Ring.KrullDimLE.isField_of_isDomain
    have hne : Ideal.Quotient.mk (primeOf (S := k) x) (X i) ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hne
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hmem : X i * g - 1 ∈ primeOf (S := k) x := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hb, map_one, sub_self]
    have h0' := homogeneousComponent_mem_primeOf x hmem 0
    have hc : coeff 0 (X i * g - 1 : Poly k N) = -1 := by
      rw [← congrFun constantCoeff_eq]
      simp
    rw [homogeneousComponent_zero, hc] at h0'
    exact (Ideal.IsPrime.ne_top inferInstance)
      (Ideal.eq_top_of_isUnit_mem _ h0' ((isUnit_one.neg).map (C : k →+* Poly k N)))
  have hbot : ringKrullDim (Poly k N ⧸ primeOf (S := k) x) ≠ ⊥ := fun h => hpos (h ▸ bot_le)
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have htop : e ≠ ⊤ := by
    rintro rfl
    rw [← he] at hle
    have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((N + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := hle
    exact ENat.natCast_ne_top (N + 1) (top_le_iff.mp (WithBot.coe_le_coe.mp h'))
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp htop
  have hn1 : 1 ≤ n := by
    by_contra h
    push Not at h
    apply hpos
    rw [← he]
    interval_cases n
    simp
  refine ⟨n - 1, ⟨inferInstance, fun f hf d => homogeneousComponent_mem_primeOf x hf d, le_rfl,
    ⟨i, hXi⟩, ?_⟩⟩
  rw [← he, Nat.sub_add_cancel hn1]
  rfl
end GroundTheory.Heights₂.Heights.Kleiman
