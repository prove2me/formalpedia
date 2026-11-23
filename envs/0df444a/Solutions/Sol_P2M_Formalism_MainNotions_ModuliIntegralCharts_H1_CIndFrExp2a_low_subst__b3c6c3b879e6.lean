-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2a_low_subst__b3c6c3b879e6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:08.711485+00:00
-- url     : https://prove2.me/submissions/7982a534-ebf4-4fee-9a54-2b09dc18fa96

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.FG.SolveVAux Formalism.L2.Pj
variable {S : Type} [CommRing S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
theorem _root_.solution {ι τ : Type} [Finite ι] {N : ℕ} {k : ι → MvPowerSeries τ S} (hk : ∀ i, Low 1 (k i))
    {g : MvPowerSeries ι S} (hg : Low N g) : Low N (subst k g) := by
  classical
  have hk0 : ∀ i, constantCoeff (k i) = 0 := fun i => (low_one_iff _).1 (hk i)
  have ha : HasSubst k := ⟨fun s => by rw [hk0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have key : ∀ (m : ι →₀ ℕ) (t : Finset ι), Low (∑ s ∈ t, m s) (∏ s ∈ t, k s ^ m s) := by
    intro m t
    refine Finset.induction_on t ?_ ?_
    · rw [Finset.sum_empty]
      exact low_zero _
    · intro a t hat ih
      rw [Finset.sum_insert hat, Finset.prod_insert hat]
      exact low_mul (low_pow (hk a) (m a)) ih
  intro e he
  have hz : ∀ m : ι →₀ ℕ, coeff m g • coeff e (m.prod fun s n => k s ^ n) = 0 := by
    intro m
    by_cases hm : m.degree < N
    · rw [hg m hm, zero_smul]
    · have hprod : Low m.degree (m.prod fun s n => k s ^ n) := key m m.support
      rw [hprod e (lt_of_lt_of_le he (not_lt.mp hm)), smul_zero]
  rw [coeff_subst ha]
  simp only [hz, finsum_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
