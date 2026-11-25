-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_proof_9ab3fe5ffabf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:17:56.243577+00:00
-- url     : https://prove2.me/submissions/48c0c8e9-7159-4a30-90c9-ef14f3041782

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PComponentOfIncIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_ringKrullDim_quot_add_one_le_6d257a8d96e5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_one_le_ringKrullDim_quot_e6e3f847a053
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_exists_nat_of_bounds_a5ec014f4cda
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_height_add_ringKrullDim_quotient


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
open ComponentOfIncIdeal
namespace GroundTheory.Heights₂.Heights
namespace ComponentOfIncIdeal
theorem _root_.solution (h₁ : IncIdealDim.Statement) (h₂ : IncIdealPrime.Statement)
    (h₃ : ConeDimComponent.Statement) : ComponentOfIncIdeal.Statement := by
  intro F _ n e I W u q hI hdim hu hW hle hq hinc
  have hWp := hW.isPrime
  have := hI.isPrime

  have hIW : I ≤ W := le_sup_left.trans hle
  have huW : linForm u ∈ W := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hIneW : I ≠ W := fun h => hu (h ▸ huW)
  have hup := ringKrullDim_quot_add_one_le hIW hIneW
  rw [hdim] at hup
  obtain ⟨k, hk, hk1, hke⟩ := exists_nat_of_bounds (one_le_ringKrullDim_quot hW) hup

  have hdimInc := h₁ F n e (k - 1) W hW (by rw [hk]; congr 2; omega)
  have hincp : (incIdeal W e).IsPrime := h₂ F n e W hWp hW.isRelevant
  have hS : ringKrullDim (MvPolynomial (Fin e × Fin n) F) = ((e * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_isField (Field.toIsField F)]
    simp [Nat.card_eq_fintype_card]
  have hsum := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F (incIdeal W e)
  rw [hdimInc, hS] at hsum
  have hqle : (Ideal.span {q}).height ≤ 1 := Ideal.height_span_singleton_le_one hq.not_isUnit
  have hht : (incIdeal W e).height ≤ 1 := (Ideal.height_mono hinc).trans hqle
  obtain ⟨h, hh⟩ : ∃ h : ℕ, (incIdeal W e).height = h :=
    ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) hht) |>.imp fun _ h => h.symm
  rw [hh] at hsum hht
  have hh1 : h ≤ 1 := by exact_mod_cast hht
  have hnat : h + (e * n - e + min e (k - 1)) = e * n := by
    have h5 : (((h + (e * n - e + min e (k - 1)) : ℕ) : ℕ∞) : WithBot ℕ∞) = (((e * n : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [Nat.cast_add, WithBot.coe_add]
      exact hsum
    exact_mod_cast WithBot.coe_inj.mp h5
  have hn : 1 ≤ n := by
    obtain ⟨j, _⟩ := hW.isRelevant
    exact Nat.one_le_iff_ne_zero.mpr fun h0 => (h0 ▸ j).elim0
  have hen : e ≤ e * n := Nat.le_mul_of_pos_right e hn
  have hmin : min e (k - 1) = k - 1 := min_eq_right (by omega)
  rw [hmin] at hnat
  generalize e * n = N at hnat hen
  have hke' : k = e := by omega
  have hh' : h = 1 := by omega
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨W'', hmin'', hW''⟩ := Ideal.exists_minimalPrimes_le hle
    have hrel : IsRelevant W'' := by
      obtain ⟨j, hj⟩ := hW.isRelevant
      exact ⟨j, fun hj'' => hj (hW'' hj'')⟩
    have hdim'' := (h₃ F n e I W'' u hI hdim hu ⟨hmin'', hrel⟩).2
    by_cases heq : W'' = W
    · exact heq ▸ ⟨hmin'', hrel⟩
    · have := hmin''.1.1
      have hlt := ringKrullDim_quot_add_one_le hW'' heq
      rw [hdim'', hk, hke'] at hlt
      have : e + 1 ≤ e := by exact_mod_cast hlt
      omega
  ·
    by_contra hne
    have : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
    have : (Ideal.span {q}).FiniteHeight :=
      (Ideal.span {q}).finiteHeight_iff.mpr (Or.inr (ne_top_of_le_ne_top (by simp) hqle))
    have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hinc hne)
    rw [hh, hh'] at hlt
    exact absurd (hlt.trans_le hqle) (lt_irrefl _)
end ComponentOfIncIdeal
end GroundTheory.Heights₂.Heights
