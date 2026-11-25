-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_not_lt_lt_of_mem_minimalPrimes_sup_span_d06807dbb20f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:24:42.761579+00:00
-- url     : https://prove2.me/submissions/65e37ed2-8094-4b32-a548-b765d235d7ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PVertSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P Q W : Ideal A} [hP : P.IsPrime] [hQ : Q.IsPrime] [hW : W.IsPrime] {x : A}
    (hmin : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hPQ : P < Q) (hQW : Q < W) : False := by
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have hsurj : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk P) = P := Ideal.mk_ker
  have prime_map : ∀ J : Ideal A, J.IsPrime → P ≤ J → (J.map (Ideal.Quotient.mk P)).IsPrime :=
    fun J _ hPJ => Ideal.map_isPrime_of_surjective hsurj (hker.trans_le hPJ)
  have strict : ∀ J₁ J₂ : Ideal A, P ≤ J₁ → J₁ < J₂ →
      J₁.map (Ideal.Quotient.mk P) < J₂.map (Ideal.Quotient.mk P) := by
    intro J₁ J₂ h₁ h₁₂
    refine lt_of_le_of_ne (Ideal.map_mono h₁₂.le) fun h => h₁₂.ne ?_
    have := congrArg (Ideal.comap (Ideal.Quotient.mk P)) h
    rwa [Ideal.comap_map_of_surjective' _ hsurj, Ideal.comap_map_of_surjective' _ hsurj, hker,
      sup_eq_left.mpr h₁, sup_eq_left.mpr (h₁.trans h₁₂.le)] at this
  have := prime_map P hP le_rfl
  have := prime_map Q hQ hPQ.le
  have := prime_map W hW (hPQ.le.trans hQW.le)
  have a := Ideal.height_add_one_le_of_lt_of_isPrime (strict P Q le_rfl hPQ)
  have b := Ideal.height_add_one_le_of_lt_of_isPrime (strict Q W hPQ.le hQW)
  have : (2 : ℕ∞) ≤ 1 :=
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (P.map (Ideal.Quotient.mk P)).height + 1 + 1 := by gcongr; exact zero_le
      _ ≤ (Q.map (Ideal.Quotient.mk P)).height + 1 := by gcongr
      _ ≤ (W.map (Ideal.Quotient.mk P)).height := b
      _ ≤ 1 := h1
  exact absurd this (by norm_num)
end GroundTheory.Heights₂.Heights.Vertical
