-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_not_lt_of_mem_minimalPrimes_sup_span_cd90bad77275
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:24:46.703036+00:00
-- url     : https://prove2.me/submissions/d16e305c-5cff-43f0-abec-08ba327ec8a8

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PFibreCut

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
open MvPolynomial IsDedekindDomain
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {R : Type*} [CommRing R] [IsNoetherianRing R]
    {P W Q : Ideal R} {f : R} [P.IsPrime] [W.IsPrime] (hPW : P < W)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) : ¬ W < Q := by
  intro hWQ
  have : Q.IsPrime := hQ.isPrime
  have hPQ : P ≤ Q := le_sup_left.trans hQ.le
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hQ
  have hπ : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk P) = P := Ideal.mk_ker
  have hWm : (W.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective hπ (hker.le.trans hPW.le)
  have hQm : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective hπ (hker.le.trans hPQ)
  have hinj : ∀ {I J : Ideal R}, P ≤ I → P ≤ J →
      I.map (Ideal.Quotient.mk P) = J.map (Ideal.Quotient.mk P) → I = J := by
    intro I J hI hJ h
    have := congrArg (Ideal.comap (Ideal.Quotient.mk P)) h
    rwa [Ideal.comap_map_of_surjective' _ hπ, Ideal.comap_map_of_surjective' _ hπ, hker,
      sup_eq_left.mpr hI, sup_eq_left.mpr hJ] at this
  have hlt1 : (⊥ : Ideal (R ⧸ P)) < W.map (Ideal.Quotient.mk P) := by
    refine bot_lt_iff_ne_bot.mpr fun h => hPW.ne ?_
    exact hinj le_rfl hPW.le (by rw [h, Ideal.map_quotient_self])
  have hlt2 : W.map (Ideal.Quotient.mk P) < Q.map (Ideal.Quotient.mk P) :=
    lt_of_le_of_ne (Ideal.map_mono hWQ.le) fun h => hWQ.ne (hinj hPW.le hPQ h)
  have a := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt1
  have b := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt2
  rw [Ideal.height_bot] at a
  have c : (W.map (Ideal.Quotient.mk P)).height < 1 := lt_of_lt_of_le b h1
  rw [Order.lt_one_iff] at c
  rw [c] at a
  exact lt_irrefl _ a
end GroundTheory.Heights₂.Heights.Vertical
