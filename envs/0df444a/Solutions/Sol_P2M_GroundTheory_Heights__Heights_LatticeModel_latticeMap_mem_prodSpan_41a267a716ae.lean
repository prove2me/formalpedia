-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_mem_prodSpan_41a267a716ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:59.128798+00:00
-- url     : https://prove2.me/submissions/ec53e3cd-318b-49b8-908b-a7a6b1baffbe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_mem_prodSpan_one_cbb7b48e9694
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_pow_mem_prodSpan_82b72063b8f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_prod_mem_prodSpan_0cba948c4940
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_mem_dual_8941773f3eb5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_weight_one_eq_degree_27ee5a5b405e


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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}
variable {φ : Fin (N + 1) → Fin m → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (hφ : IsDualBasis L φ) {d : ℕ}
    {f : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ} (hf : f.IsHomogeneous d) : latticeMap φ f ∈ prodSpan L d := by
  rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun s hs ↦ ?_
  have hdeg : s.degree = d := by
    have := hf (mem_support_iff.mp hs)
    rwa [weight_one_eq_degree] at this
  rw [latticeMap, coe_eval₂Hom, eval₂_monomial, eq_intCast, ← zsmul_eq_mul]
  refine zsmul_mem ?_ _
  rw [← hdeg, Finsupp.prod, Finsupp.degree]
  exact prod_mem_prodSpan _ _ _ fun v _ ↦ pow_mem_prodSpan (latticeForm_mem_prodSpan_one (mem_dual hφ v.2)) _
end GroundTheory.Heights₂.Heights.LatticeModel
