-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.phi_one_Wm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:30:57.433803+00:00
-- url     : https://prove2.me/submissions/5332d712-0f4f-4156-b0b0-0d79811a6d81

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchPhiOneApply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Wm_kStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Wm_khw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Wm_le_ncV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_bAct_isKUnitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimir_genSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exists_khw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_finiteDimensional_ncV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isKUnitary_of_isInfUnitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_khw_lowK_sub_root_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_le_genSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lift_khw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_phi_bAct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_phi_mem_layer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sch_gap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {x : Big n 1 M} (hx : x ∈ Wm ε E V) : phi E 1 x = 0 := by
  by_contra hne
  have := finiteDimensional_ncV (ε := ε) hV.1 1
  have hfdW : FiniteDimensional ℂ (Wm ε E V) := Submodule.finiteDimensional_of_le Wm_le_ncV
  have hWst : IsKStableSub ε (bAct E 1) (Wm ε E V) := Wm_kStable hE hU hV
  set T : Submodule ℂ M := (Wm ε E V).map (phi E 1) with hTdef
  have hfdT : FiniteDimensional ℂ T := inferInstance
  have hTst : IsKStableSub ε E T := by
    intro a b hab v hv
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv
    rw [← phi_bAct hE 1 hab y]
    exact Submodule.mem_map_of_mem (hWst a b hab y hy)
  have hTne : T ≠ ⊥ := by
    intro hT
    have : phi E 1 x ∈ T := Submodule.mem_map_of_mem hx
    rw [hT, Submodule.mem_bot] at this
    exact hne this
  have hKU : IsKUnitary ε E := isKUnitary_of_isInfUnitary hU
  obtain ⟨y, hyT, hy0, μ, hyμ⟩ := exists_khw hE hKU hfdT hTst hTne
  obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.1 hyT
  obtain ⟨x1, hx1, -, hkhw, hfx⟩ := lift_khw (A := bAct E 1) (bAct_isKUnitary hU 1) (phi E 1)
    (fun a b hab z => phi_bAct hE 1 hab z) hfdW hWst hx₀ hyμ
  have hx10 : x1 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hfx
    exact hy0 hfx.symm
  obtain ⟨a, b, hab, hε, hμ⟩ := Wm_khw hE hU hV hmono hh hbig hx1 hx10 hkhw
  have hlay : phi E 1 x₀ ∈ layer ε E V 1 := phi_mem_layer (Wm_le_ncV hx₀)
  have hcas : casimir E (phi E 1 x₀) = (casVal lam : ℂ) • phi E 1 x₀ :=
    casimir_genSub hE hc _ (layer_le_genSub (ε := ε) 1 hlay)
  rw [hμ] at hyμ
  exact hy0 (khw_lowK_sub_root_eq_zero ε hE hU lam hab hε
    (sch_gap ⟨hmono, h, hh, hbig⟩ hab hε) hyμ hcas)
end ReciprocityTheory.ChartRestriction.DS
