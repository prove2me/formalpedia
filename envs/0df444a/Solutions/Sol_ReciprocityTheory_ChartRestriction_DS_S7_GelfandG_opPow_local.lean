-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GelfandG.opPow_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:10:01.49739+00:00
-- url     : https://prove2.me/submissions/f2b849c0-069b-4141-9ead-5695569c30fa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LholClmEventually
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasG_lhol_clm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GelfandGA_opPow_contDiffOn
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
open ReciprocityTheory.ChartRestriction.DS.S7.GelfandG
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace ReciprocityTheory.ChartRestriction.DS.S7.GelfandG
theorem _root_.solution (ε : Fin n → Bool) (Lk : E →L[ℂ] E') {G : Matrix (Fin n) (Fin n) ℂ → E}
    {U W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℂ ∞ G U) (hW : IsOpen W) (hWU : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ U)
    {f : Matrix (Fin n) (Fin n) ℂ → E'} (hf : ∀ g ∈ W, inUJ ε g → f g = Lk (G (g⁻¹ * m)))
    (p q : Fin n → Fin n → Fin n) (s : ℂ)
    (A : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E') → (Matrix (Fin n) (Fin n) ℂ → E'))
    (hA : ∀ a b h, A a b h = s • EabV ε (p a b) (q a b) h) (j : ℕ) :
    ∀ a b, ∀ g ∈ W, inUJ ε g →
      opPow A j a b f g = (-s) ^ j •
        Lk (opPow (fun a b => Lhol (Matrix.single (p a b) (q a b) (1 : ℂ))) j a b G (g⁻¹ * m)) := by
  induction j with
  | zero =>
    intro a b g hg hgu
    simp only [opPow, pow_zero, one_smul]
    split_ifs
    · exact hf g hg hgu
    · simp
  | succ j ih =>
    intro a b g hg hgu
    have hz : g⁻¹ * m ∈ U := (hWU g hg).2
    simp only [opPow, Finset.sum_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hGd : DifferentiableOn ℂ
        (opPow (fun a b => Lhol (Matrix.single (p a b) (q a b) (1 : ℂ))) j c b G) U :=
      (GelfandGA.opPow_contDiffOn hU hG _ j c b).differentiableOn (by simp)
    have hF : DifferentiableOn ℂ (fun z => ((-s) ^ j • Lk)
        (opPow (fun a b => Lhol (Matrix.single (p a b) (q a b) (1 : ℂ))) j c b G z)) U :=
      ((-s) ^ j • Lk).differentiable.comp_differentiableOn hGd
    have hloc : ∀ g ∈ W, inUJ ε g → opPow A j c b f g = ((-s) ^ j • Lk)
        (opPow (fun a b => Lhol (Matrix.single (p a b) (q a b) (1 : ℂ))) j c b G (g⁻¹ * m)) :=
      fun g hg hgu => by rw [ih c b g hg hgu, _root_.smul_apply]
    rw [hA, Pi.smul_apply, eabV_of_local ε hU hF hW hWU hloc _ _ hg hgu,
      CasG.lhol_clm _ _ ((hGd _ hz).differentiableAt (hU.mem_nhds hz)),
      _root_.smul_apply, smul_neg, smul_smul, ← neg_smul, pow_succ]
    congr 1
    ring
end ReciprocityTheory.ChartRestriction.DS.S7.GelfandG
