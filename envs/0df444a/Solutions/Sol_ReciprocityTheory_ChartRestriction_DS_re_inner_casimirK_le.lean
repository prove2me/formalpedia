-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.re_inner_casimirK_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:31.032577+00:00
-- url     : https://prove2.me/submissions/f871d09e-b8b8-47ae-a5d9-811a4307745e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_re_inner_le_of_isSymmetric_eigen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_inner_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_mem_of_kStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eig_casimirK

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
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) (C : ℝ)
    (hC : ∀ w ∈ S, w ≠ 0 → ∀ μ : Fin n → ℝ, IsKHWVec ε A μ w → casValK ε μ ≤ C) :
    ∀ x ∈ S, RCLike.re (inner ℂ (casimirK ε A x) x) ≤ C * ‖x‖ ^ 2 := by
  haveI := hfd
  intro x hx
  let T : S →ₗ[ℂ] S := (casimirK ε A).restrict (fun y hy => casimirK_mem_of_kStable hS hy)
  have hTc : ∀ y : S, ((T y : S) : X) = casimirK ε A y := fun y => rfl
  have hT : T.IsSymmetric := by
    intro y z
    rw [Submodule.coe_inner, Submodule.coe_inner, hTc, hTc]
    exact casimirK_inner_symm hU _ _
  have key := re_inner_le_of_isSymmetric_eigen hT C (fun v hv0 θ hθ => by
    have hθ' : casimirK ε A v = (θ : ℂ) • (v : X) := congrArg Subtype.val hθ
    obtain ⟨w, hwS, hw0, -, μ, hkhw, hθμ⟩ := eig_casimirK hA hU hfd hS v.2
      (fun h => hv0 (Subtype.ext h)) hθ'
    have e : θ = casValK ε μ := by exact_mod_cast hθμ
    rw [e]
    exact hC w hwS hw0 μ hkhw) ⟨x, hx⟩
  rw [Submodule.coe_inner, hTc] at key
  have e1 : ((⟨x, hx⟩ : S) : X) = x := rfl
  have e2 : ‖(⟨x, hx⟩ : S)‖ = ‖x‖ := rfl
  rw [e1, e2] at key
  exact key
end ReciprocityTheory.ChartRestriction.DS
