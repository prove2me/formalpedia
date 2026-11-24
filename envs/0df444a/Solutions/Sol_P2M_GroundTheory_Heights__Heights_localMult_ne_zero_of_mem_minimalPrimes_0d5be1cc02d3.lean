-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_localMult_ne_zero_of_mem_minimalPrimes_0d5be1cc02d3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:39.132797+00:00
-- url     : https://prove2.me/submissions/f25e7801-e548-4871-9212-ac507cb2fcca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm

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
open MvPolynomial Ideal
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {A : Type*} [CommRing A] [IsNoetherianRing A]
    {J P : Ideal A} (hP : P ∈ J.minimalPrimes) : localMult J P ≠ 0 := by
  have hPp : P.IsPrime := hP.1.1
  unfold localMult
  rw [dif_pos hPp]
  let R := Localization.AtPrime P
  let I : Ideal R := J.map (algebraMap A R)
  have hmin : IsLocalRing.maximalIdeal R ∈ I.minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map P.primeCompl R J, Set.mem_preimage,
      Localization.AtPrime.under_maximalIdeal]
    exact hP
  have := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmin
  have : IsArtinian R (R ⧸ I) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  have : IsNoetherian R (R ⧸ I) := isNoetherian_quotient I
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hmin.1.2
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  rw [Ne, ENat.toNat_eq_zero, not_or]
  exact ⟨(Module.length_pos (R := R) (M := R ⧸ I)).ne', Module.length_ne_top⟩
end GroundTheory.Heights₂.Heights
