-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CapG.foldr_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:41:42.148673+00:00
-- url     : https://prove2.me/submissions/2661e6a3-fa6e-47a2-a3c5-aa4fa0c302a9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ChainHSlice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LholClmEventually
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_TopContDiffOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapG_top_contDiffOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasG_lhol_clm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_eabV_of_local


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
    (l : List (ℂ × Fin n × Fin n)) :
    ContDiffOn ℂ ∞ ((l.map fun x => Formalism.QuantumDeterminants.Top negL x.1 x.2.1 x.2.2).foldr (fun T h => T h) G) U ∧
    ∀ g ∈ W, inUJ ε g →
      (l.map fun x => Formalism.QuantumDeterminants.Top (EabV ε) x.1 x.2.1 x.2.2).foldr (fun T h => T h) f g =
        Lk ((l.map fun x => Formalism.QuantumDeterminants.Top negL x.1 x.2.1 x.2.2).foldr (fun T h => T h) G (g⁻¹ * m)) := by
  induction l with
  | nil => exact ⟨hG, fun g hg hgu => by simpa using hf g hg hgu⟩
  | cons x l ih =>
    obtain ⟨ihc, ihf⟩ := ih
    simp only [List.map_cons, List.foldr_cons]
    refine ⟨top_contDiffOn hU ihc _ _ _, fun g hg hgu => ?_⟩
    have hz := (hWU g hg).2
    have hHd := ihc.differentiableOn (by simp)
    set H := (l.map fun x => Formalism.QuantumDeterminants.Top negL x.1 x.2.1 x.2.2).foldr (fun T h => T h) G with hH
    have hF : DifferentiableOn ℂ (fun z => Lk (H z)) U := Lk.differentiable.comp_differentiableOn hHd
    have e := eabV_of_local ε hU hF hW hWU ihf x.2.1 x.2.2 hg hgu
    show (if x.2.1 = x.2.2 then x.1 • _ else 0) + EabV ε x.2.1 x.2.2 _ g =
      Lk ((if x.2.1 = x.2.2 then x.1 • _ else 0) + negL x.2.1 x.2.2 _ (g⁻¹ * m))
    rw [e, CasG.lhol_clm _ _ ((hHd _ hz).differentiableAt (hU.mem_nhds hz)), ihf g hg hgu, map_add]
    simp only [negL, map_neg]
    split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.DS.S7.CapG
