-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.exists_khw_of_not_sch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:31:01.875165+00:00
-- url     : https://prove2.me/submissions/42f12390-37c6-46b3-8f54-f1f54bdbbc83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchForm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Wm_kStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Wm_khw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Wm_le_ncV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_bAct_isKUnitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exists_khw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_finiteDimensional_ncV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isKUnitary_of_isInfUnitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lift_khw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_phi_bAct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_phi_mem_layer


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
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h)
    (hne : ∃ x ∈ Wm ε E V, phi E 1 x ≠ 0) :
    ∃ a b : Fin n, a < b ∧ ε a ≠ ε b ∧
      ∃ w ∈ layer ε E V 1, w ≠ 0 ∧ IsKHWVec ε E (lowK ε lam - root a b) w := by
  classical
  obtain ⟨x₀, hx₀, hphi⟩ := hne
  have hKU : IsKUnitary ε E := isKUnitary_of_isInfUnitary hU
  have : FiniteDimensional ℂ (ncV ε V 1) := finiteDimensional_ncV hV.1 1
  have hfdW : FiniteDimensional ℂ (Wm ε E V) := Submodule.finiteDimensional_of_le Wm_le_ncV
  have hTst : IsKStableSub ε E ((Wm ε E V).map (phi E 1)) := by
    intro a b hab v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    exact Submodule.mem_map.mpr
      ⟨bAct E 1 a b x, Wm_kStable hE hU hV a b hab x hx, phi_bAct hE 1 hab x⟩
  have hTne : (Wm ε E V).map (phi E 1) ≠ ⊥ := by
    intro hbot
    have hm := Submodule.mem_map_of_mem (f := phi E 1) hx₀
    rw [hbot] at hm
    exact hphi ((Submodule.mem_bot ℂ).mp hm)
  obtain ⟨w, hwT, hw0, μ, hkμ⟩ := exists_khw hE hKU inferInstance hTst hTne
  obtain ⟨x₁, hx₁, rfl⟩ := Submodule.mem_map.mp hwT
  obtain ⟨x, hx, -, hkx, hfx⟩ := lift_khw (bAct_isKUnitary hU 1) (phi E 1)
    (fun a b hab y => phi_bAct hE 1 hab y) hfdW (Wm_kStable hE hU hV) hx₁ hkμ
  have hx0 : x ≠ 0 := by
    intro h0
    apply hw0
    rw [← hfx, h0, map_zero]
  obtain ⟨a, b, hab, hε, hμe⟩ := Wm_khw hE hU hV hmono hh hbig hx hx0 hkx
  refine ⟨a, b, hab, hε, phi E 1 x₁, ?_, hw0, hμe ▸ hkμ⟩
  rw [← hfx]
  exact phi_mem_layer (Wm_le_ncV hx)
end ReciprocityTheory.ChartRestriction.DS
