-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_proof_e312c9cf0b73
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:47:38.368021+00:00
-- url     : https://prove2.me/submissions/5cded3d9-1709-4932-a1ac-fcc162191fe9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_maximal_ord_eq_1711457ea247
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_curveLocalRing_eq_div_9ca7f60b5d9b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isReduced_curveLocalRing_913d64c72495


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
open MvPolynomial ComplexSets
noncomputable section
open MinimalPrimePlace
namespace GroundTheory.Heights₂.Heights
namespace MinimalPrimePlace
theorem _root_.solution : MinimalPrimePlace.Statement := by
  intro n I J q hI hJ hJq P'
  have hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) ≤
      J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) :=
    Ideal.map_mono hJ.1.2
  let π : curveLocalRing I q →+* curveLocalRing J q := Ideal.Quotient.factor hle
  have hπalg : ∀ f, π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f) =
      algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f := fun f ↦ Ideal.Quotient.factor_mk hle _
  have hJd : Disjoint ((RingHom.ker (eval q)).primeCompl : Set (MvPolynomial (Fin n) ℂ)) J :=
    Set.disjoint_left.2 fun x hx hxJ ↦ hx (hJq hxJ)
  have hJP : (J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ J hJ.1.1 hJd
  have hJc : (J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))).comap
      (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) = J :=
    IsLocalization.under_map_of_isPrime_disjoint _ _ hJ.1.1 hJd
  have _ : IsDomain (curveLocalRing J q) := Ideal.Quotient.isDomain _
  have _ : IsReduced (curveLocalRing I q) := isReduced_curveLocalRing I q hI
  have hkerJ : ∀ f, algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f = 0 ↔ f ∈ J := by
    intro f
    exact (Ideal.Quotient.eq_zero_iff_mem (I := J.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q))))) (a := algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q))) f)).trans (by rw [← Ideal.mem_comap, hJc])
  have hker : RingHom.ker π ∈ minimalPrimes (curveLocalRing I q) := by
    refine ⟨⟨RingHom.ker_isPrime π, bot_le⟩, fun Q hQ hQle ↦ ?_⟩
    have _ : Q.IsPrime := hQ.1
    have hIQ : I ≤ Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) := fun f hf ↦ by
      have h0 : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hf)
      show _ ∈ Q
      rw [h0]
      exact Q.zero_mem
    have hQJ : Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) ≤ J := fun f hf ↦
      (hkerJ f).1 (by rw [← hπalg]; exact RingHom.mem_ker.1 (hQle hf))
    have hJQ := hJ.2 ⟨Ideal.comap_isPrime _ Q, hIQ⟩ hQJ
    intro z hz
    obtain ⟨f, s, hs, hfs⟩ := curveLocalRing_eq_div I q z
    have hf : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ Q :=
      hJQ ((hkerJ f).1 (by rw [← hπalg, ← hfs, map_mul, RingHom.mem_ker.1 hz, zero_mul]))
    rw [← hfs] at hf
    exact (Ideal.mul_unit_mem_iff_mem Q hs).1 hf
  obtain ⟨P, hP⟩ := exists_maximal_ord_eq π (Ideal.Quotient.factor_surjective hle) hker P'
  refine ⟨P, fun f ↦ ?_⟩
  have h := hP (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f)
  rw [hπalg] at h
  exact h
end MinimalPrimePlace
end GroundTheory.Heights₂.Heights
