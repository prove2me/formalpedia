-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.inner_actM_add_inner_actM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:54.666028+00:00
-- url     : https://prove2.me/submissions/322aba1f-875f-4893-880e-02e7598ff444

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_inner_map_map_of_isURep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exp_smul_mem_UJset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v w : D) :
    inner ℂ (actM E X v) w + inner ℂ v (actM E X w) = 0 := by
  have hσ' := hσ
  unfold IsURepOn at hσ'
  obtain ⟨-, -, hder⟩ := hD
  have hd := (hder X hX v).inner ℂ (hder X hX w)
  have hc : HasDerivAt (fun t : ℝ => inner ℂ ((σ (NormedSpace.exp ((t : ℂ) • X))) (v : H))
      ((σ (NormedSpace.exp ((t : ℂ) • X))) (w : H))) 0 0 := by
    have e : (fun t : ℝ => inner ℂ ((σ (NormedSpace.exp ((t : ℂ) • X))) (v : H))
        ((σ (NormedSpace.exp ((t : ℂ) • X))) (w : H))) = fun _ => inner ℂ (v : H) (w : H) := by
      funext t
      exact inner_map_map_of_isURep hσ (exp_smul_mem_UJset hX t) _ _
    rw [e]
    exact hasDerivAt_const _ _
  have h0 := hd.unique hc
  simp [hσ'.1.1] at h0
  first
    | (rw [Submodule.coe_inner, Submodule.coe_inner]; linear_combination h0)
    | (simpa [add_comm] using h0)
end ReciprocityTheory.ChartRestriction.DS
