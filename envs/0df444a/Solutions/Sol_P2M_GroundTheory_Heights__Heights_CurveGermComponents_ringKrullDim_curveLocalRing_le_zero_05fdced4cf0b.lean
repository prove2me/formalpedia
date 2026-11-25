-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveGermComponents_ringKrullDim_curveLocalRing_le_zero_05fdced4cf0b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:09:19.970514+00:00
-- url     : https://prove2.me/submissions/020fc087-744e-4b53-9d3d-892ba130d211

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveGermComponents

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
open MvPolynomial ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.CurveGermComponents
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.CurveGermComponents
theorem _root_.solution {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hm : RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) ∈ I.minimalPrimes) :
    ringKrullDim (curveLocalRing I q) ≤ 0 := by
  set m := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) with hmdef
  let L := Localization.AtPrime m
  let J : Ideal L := I.map (algebraMap (MvPolynomial (Fin n) ℂ) L)
  change ringKrullDim (L ⧸ J) ≤ 0
  have hK : Ring.KrullDimLE 0 (L ⧸ J) := by
    rw [Ring.krullDimLE_zero_iff]
    intro p hp
    set Q := p.comap (Ideal.Quotient.mk J) with hQdef
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have hP : (Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L)).IsPrime := Ideal.comap_isPrime _ _
    have hIP : I ≤ Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L) := by
      rw [← Ideal.map_le_iff_le_comap]
      intro y hy
      rw [hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hy]
      exact p.zero_mem
    have hPm : Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L) ≤ m := by
      exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)).trans
        (Localization.AtPrime.under_maximalIdeal (I := m)).le
    have hPeq : Q.under (MvPolynomial (Fin n) ℂ) = m := le_antisymm hPm (hm.2 ⟨hP, hIP⟩ hPm)
    have hQmax : Q = IsLocalRing.maximalIdeal L := Localization.AtPrime.eq_maximalIdeal_iff_under_eq.1 hPeq
    have hQm : Q.IsMaximal := hQmax ▸ IsLocalRing.maximalIdeal.isMaximal L
    have h := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective hQm
    rw [hQdef, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h
    exact h.resolve_left hp.ne_top
  exact_mod_cast Ring.krullDimLE_iff.1 hK
end GroundTheory.Heights₂.Heights.CurveGermComponents
