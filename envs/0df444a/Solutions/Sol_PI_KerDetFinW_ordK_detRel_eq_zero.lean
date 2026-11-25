-- Prove2me | solution 1 for PI.KerDetFinW.ordK_detRel_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:07:07.089982+00:00
-- url     : https://prove2.me/submissions/99a7b0a2-f88b-44d1-aab1-56b682d6e82b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom
import Theorems.Thm_PI_KerDetFinW_det_valuation_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KerDetFinW
open PI.KerIso
namespace PI.KerDetFinW
theorem _root_.solution {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type}
    [Fintype n] {M : Set E} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)} {p : ℕ}
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal)
    (hg : AtP M g p) (hg' : AtP M g' p) : ordK 𝔭 (detRel g' g) = 0 := by
  have h1 : 𝔭.valuation K (detRel g' g) ≤ 1 := det_valuation_le_one 𝔭 hp𝔭 hg hg'
  have h2 : 𝔭.valuation K (detRel g g') ≤ 1 := det_valuation_le_one 𝔭 hp𝔭 hg' hg
  have hprod : detRel g' g * detRel g g' = 1 := by
    unfold detRel
    rw [← LinearMap.det_comp]
    have hc : ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] _) :
        (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)).comp
        ((g'.symm.trans g : (Fin 4 × n → K) ≃ₗ[K] _) :
        (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)) = LinearMap.id :=
      LinearMap.ext fun x => by simp
    rw [hc, LinearMap.det_id]
  have hm : 𝔭.valuation K (detRel g' g) * 𝔭.valuation K (detRel g g') = 1 := by
    rw [← map_mul, hprod, map_one]
  have hv : 𝔭.valuation K (detRel g' g) = 1 := by
    refine le_antisymm h1 ?_
    calc 1 = 𝔭.valuation K (detRel g' g) * 𝔭.valuation K (detRel g g') := hm.symm
      _ ≤ 𝔭.valuation K (detRel g' g) * 1 := by gcongr
      _ = 𝔭.valuation K (detRel g' g) := mul_one _
  unfold ordK
  rw [hv]
  simp
end PI.KerDetFinW
