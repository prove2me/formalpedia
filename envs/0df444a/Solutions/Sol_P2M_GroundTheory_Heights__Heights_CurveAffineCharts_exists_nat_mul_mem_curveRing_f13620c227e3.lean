-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_nat_mul_mem_curveRing_f13620c227e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:07:39.492651+00:00
-- url     : https://prove2.me/submissions/fd07dd80-abca-40e2-ab2c-33e9aac7f183

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_nat_mul_mem_adjoin_e048a425d326
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_adjoin_of_mem_blockFnField_0a47ea1c92ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_curveRing_46da28e9018f


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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.CurveAffineCharts
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
namespace GroundTheory.Heights₂.Heights.CurveAffineCharts
theorem _root_.solution [NumberField K'] {x : K'} (hx : x ∈ blockFnField y) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K') * x ∈ curveRing y := by
  classical
  have key : ∀ t : T, ∃ n : ℕ, n ≠ 0 ∧ (y ⟨(), t⟩ ≠ 0 → (n : K') * x ∈ chartRingZ y (fun _ => t)) := by
    intro t
    by_cases ht : y ⟨(), t⟩ = 0
    · exact ⟨1, one_ne_zero, fun h => (h ht).elim⟩
    · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_adjoin (mem_adjoin_of_mem_blockFnField y t ht hx)
      exact ⟨n, hn, fun _ => h⟩
  choose N hN0 hN using key
  refine ⟨∏ t, N t, Finset.prod_ne_zero_iff.mpr (fun t _ => hN0 t), ?_⟩
  rw [mem_curveRing]
  intro c hc
  have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
  have h1 := hN (c ()) (hc ())
  rw [← hc'] at h1
  have e : ((∏ t, N t : ℕ) : K') * x =
      ((∏ t ∈ Finset.univ.erase (c ()), N t : ℕ) : K') * ((N (c ()) : K') * x) := by
    rw [← Finset.mul_prod_erase Finset.univ N (Finset.mem_univ (c ()))]
    push_cast; ring
  rw [e]
  exact mul_mem (natCast_mem _ _) h1
end GroundTheory.Heights₂.Heights.CurveAffineCharts
