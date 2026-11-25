-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.eabV_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:41:50.877998+00:00
-- url     : https://prove2.me/submissions/ff401c65-9964-4134-8ad5-61d6839b7f55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_ccb_cpart_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_ccb_inG_cpart1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_ccb_inG_cpart2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_ccb_rdv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → E} {V W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ}
    (hV : IsOpen V) (hF : DifferentiableOn ℂ F V) (hW : IsOpen W)
    (hWV : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ V) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : ∀ g ∈ W, inUJ ε g → f g = F (g⁻¹ * m)) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ W)
    (hgu : inUJ ε g) :
    EabV ε a b f g = -(Lhol (Matrix.single a b 1) F (g⁻¹ * m)) := by
  have h1 := ccb_rdv ε hV hF hW hWV hf (ccb_inG_cpart1 ε (Matrix.single a b 1)) hg hgu
  have h2 := ccb_rdv ε hV hF hW hWV hf (ccb_inG_cpart2 ε (Matrix.single a b 1)) hg hgu
  simp only [EabV, EcV, RdV, Lhol]
  rw [h1.deriv, h2.deriv]
  conv_rhs => rw [← ccb_cpart_sum ε (Matrix.single a b 1)]
  rw [add_mul, smul_mul_assoc, map_add, map_smul, smul_neg, neg_add]
end ReciprocityTheory.ChartRestriction.DS.S7
