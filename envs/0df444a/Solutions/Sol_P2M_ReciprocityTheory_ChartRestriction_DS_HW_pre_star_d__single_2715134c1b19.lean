-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_star_d__single_2715134c1b19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:19.895394+00:00
-- url     : https://prove2.me/submissions/8c6b8c12-4f2f-4d2a-ab76-f79c70c7d549

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelGenA
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_star_d__9265fbbd55c9
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_single_eq_kp__f6287b255e07
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_inK_hermitian_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_inK_skew_hermitian_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_single_eq_kp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] {ε : Fin n → Bool} (τ : KG ε →* unitary (V →L[ℂ] V))
  (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V))
variable (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
    HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0)
include hder
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {a b : Fin n} (hab : ε a = ε b) :
    star (dτ (Matrix.single a b 1)) = dτ (Matrix.single b a 1) := by
  rw [single_eq_kp a b, single_eq_kp' a b, map_add, map_smul, map_add, map_smul, map_neg, star_add,
    star_smul, pre_star_dτ τ dτ hder (inK_hermitian_unit hab), pre_star_dτ τ dτ hder (inK_skew_hermitian_unit hab)]
  simp [Complex.conj_I]
end ReciprocityTheory.ChartRestriction.DS.HW
