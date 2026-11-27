-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CMHeightAddDim_proof_d95468e9191c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:53:50.095817+00:00
-- url     : https://prove2.me/submissions/0ce7afda-4e1e-49ed-952b-1ed94e8f724c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMHeightAddDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CMDepthAssoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_HeightCoheightQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMHeightAddDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CMHeightAddDim_height_add_ringKrullDim_quotient_of_isPrime_87ff078efbe1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_eq_coheight_d0c00cc69dc4


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
open IsLocalRing
universe u
namespace GroundTheory.Heights₂.Heights
namespace CMHeightAddDim
theorem _root_.solution (hreg : CMRegularElement.Statement.{u}) : CMHeightAddDim.Statement.{u} := by
  intro B _ _ J hJ
  obtain ⟨rs, -, -, hd⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hprime := CMHeightAddDim.height_add_ringKrullDim_quotient_of_isPrime hreg rs.length B hd
  refine le_antisymm ?_ ?_
  ·
    have : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
    have : Nonempty (PrimeSpectrum (B ⧸ J)) := inferInstance
    rw [show ringKrullDim (B ⧸ J) = Order.krullDim (PrimeSpectrum (B ⧸ J)) from rfl,
      Order.krullDim_eq_iSup_coheight_of_nonempty, ← WithBot.coe_add, ENat.add_iSup,
      WithBot.coe_iSup (OrderTop.bddAbove _)]
    refine iSup_le fun a => ?_
    obtain ⟨a, ha⟩ := a
    set Q := a.comap (Ideal.Quotient.mk J) with hQdef
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have hJQ : J ≤ Q := fun z hz => by
      rw [hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hz]
      exact Ideal.zero_mem _
    have hmap : a = Q.map (Ideal.Quotient.mk J) :=
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective a).symm
    have hco : (Order.coheight (⟨a, ha⟩ : PrimeSpectrum (B ⧸ J)) : WithBot ℕ∞) = ringKrullDim (B ⧸ Q) := by
      rw [← ringKrullDim_quotient_eq_coheight a,
        ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hmap).trans (DoubleQuot.quotQuotEquivQuotOfLE hJQ))]
    rw [WithBot.coe_add, hco, ← hprime Q]
    gcongr
    exact_mod_cast Ideal.height_mono hJQ
  ·
    obtain ⟨P, hPmin, hPle⟩ := Set.exists_min_image J.minimalPrimes Ideal.height
      (Ideal.finite_minimalPrimes_of_isNoetherianRing B J) (Set.nonempty_coe_sort.mp (Ideal.nonempty_minimalPrimes hJ))
    have : P.IsPrime := hPmin.1.1
    have hht : J.height = P.height := by
      rw [Ideal.height_eq_inf_minimalPrimes]
      exact le_antisymm (iInf₂_le P hPmin) (le_iInf₂ fun Q hQ => hPle Q hQ)
    rw [hht, ← hprime P]
    gcongr
    exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hPmin.1.2)
end CMHeightAddDim
end GroundTheory.Heights₂.Heights
