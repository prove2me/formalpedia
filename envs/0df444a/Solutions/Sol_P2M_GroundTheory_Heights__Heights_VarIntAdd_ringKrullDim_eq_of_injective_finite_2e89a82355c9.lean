-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VarIntAdd_ringKrullDim_eq_of_injective_finite_2e89a82355c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:22:50.279508+00:00
-- url     : https://prove2.me/submissions/40fff4b2-db3b-4089-a199-a9545bbaa419

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntAdd

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
open MvPolynomial MeasureTheory ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.VarIntAdd
namespace GroundTheory.Heights₂.Heights.VarIntAdd
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective f) (hfin : f.Finite) : ringKrullDim S = ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hfin.to_isIntegral⟩
  apply le_antisymm
  · have hg : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
      intro q₁ q₂ hq
      have hlt : q₁.asIdeal < q₂.asIdeal := hq
      obtain ⟨hle, x, hx2, hx1⟩ := SetLike.lt_iff_le_and_exists.mp hlt
      show q₁.asIdeal.comap (algebraMap R S) < q₂.asIdeal.comap (algebraMap R S)
      exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hx2, hx1⟩
        (Algebra.IsIntegral.isIntegral x)
    exact Order.krullDim_le_of_strictMono _ hg
  · refine iSup_le fun l => ?_
    have hker : (⊥ : Ideal S).comap (algebraMap R S) ≤ (RelSeries.head l).asIdeal := by
      intro r hr
      have : f r = 0 := hr
      rw [show r = 0 from hinj (by rw [this, map_zero])]
      exact Ideal.zero_mem _
    obtain ⟨P, -, hP, hPo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ ⊥ hker
    have : P.LiesOver (RelSeries.head l).asIdeal := ⟨hPo.symm⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    exact le_iSup_of_le L (by rw [hlen])
end GroundTheory.Heights₂.Heights.VarIntAdd
