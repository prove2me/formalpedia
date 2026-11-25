-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.eig_casimirK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:53:42.810039+00:00
-- url     : https://prove2.me/submissions/38928021-aede-4785-b58f-cbb1cb65d39c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_khwVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exists_khw


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
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hA : IsGlRep A) (hU : IsKUnitary ε A) {S : Submodule ℂ X}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) {x : X} (hx : x ∈ S) (hx0 : x ≠ 0)
    {θ : ℂ} (hθ : casimirK ε A x = θ • x) :
    ∃ w ∈ S, w ≠ 0 ∧ casimirK ε A w = θ • w ∧ ∃ μ : Fin n → ℝ, IsKHWVec ε A μ w ∧
      θ = (casValK ε μ : ℂ) := by
  classical
  set T : Submodule ℂ X := S ⊓ LinearMap.ker (casimirK ε A - θ • (1 : Module.End ℂ X)) with hTdef
  have memT : ∀ y, y ∈ T ↔ y ∈ S ∧ casimirK ε A y = θ • y := by
    intro y
    simp only [T, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  have := hfd
  have hTfd : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le inf_le_left
  have hTs : IsKStableSub ε A T := by
    intro a b hab y hy
    rw [memT] at hy ⊢
    refine ⟨hS a b hab y hy.1, ?_⟩
    have := congrArg (fun F : Module.End ℂ X => F y) (casimirK_comm ε hA a b hab)
    simp only [Module.End.mul_apply] at this
    rw [this, hy.2, map_smul]
  have hne : T ≠ ⊥ := by
    intro h
    have hxT : x ∈ T := (memT x).2 ⟨hx, hθ⟩
    rw [h, Submodule.mem_bot] at hxT
    exact hx0 hxT
  obtain ⟨w, hw, hw0, μ, hμ⟩ := exists_khw hA hU hTfd hTs hne
  rw [memT] at hw
  refine ⟨w, hw.1, hw0, hw.2, μ, hμ, ?_⟩
  have h1 := casimirK_khwVec ε hA hμ
  rw [hw.2] at h1
  exact smul_left_injective ℂ hw0 h1
end ReciprocityTheory.ChartRestriction.DS
