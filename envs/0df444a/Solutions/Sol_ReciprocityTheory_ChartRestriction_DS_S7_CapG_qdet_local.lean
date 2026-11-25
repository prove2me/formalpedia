-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CapG.qdet_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:43.812361+00:00
-- url     : https://prove2.me/submissions/6afe9780-39dc-4123-bf4d-25cb0e74d384

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ChainHSlice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LholClmEventually
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_TopContDiffOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapG_foldr_local

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
open ReciprocityTheory.ChartRestriction.DS.S7.CapG
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace ReciprocityTheory.ChartRestriction.DS.S7.CapG
theorem _root_.solution (ε : Fin n → Bool) (Lk : E →L[ℂ] E') {G : Matrix (Fin n) (Fin n) ℂ → E}
    {U W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℂ ∞ G U) (hW : IsOpen W) (hWU : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ U)
    {f : Matrix (Fin n) (Fin n) ℂ → E'} (hf : ∀ g ∈ W, inUJ ε g → f g = Lk (G (g⁻¹ * m)))
    (u : ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ W) (hgu : inUJ ε g) :
    Formalism.QuantumDeterminants.qdetOp (EabV ε) u f g = Lk (Formalism.QuantumDeterminants.qdetOp negL u G (g⁻¹ * m)) := by
  simp only [Formalism.QuantumDeterminants.qdetOp, Formalism.QuantumDeterminants.qminorOp, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have key := (foldr_local ε Lk hU hG hW hWU hf
    (List.ofFn fun k : Fin n => (u - ((k : ℕ) : ℂ), σ k, k))).2 g hg hgu
  rw [List.map_ofFn, List.map_ofFn] at key
  exact key
end ReciprocityTheory.ChartRestriction.DS.S7.CapG
