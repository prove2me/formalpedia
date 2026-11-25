-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_coefE___pow_8e1cd4cc143f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:28.134802+00:00
-- url     : https://prove2.me/submissions/9041a46c-08ae-4d3a-9c10-abb47f8e7247

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefDTensActPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefETensGrpMul
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_coefE___act_9443caaf5a71
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
open scoped Matrix
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section Rep
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
private theorem actM_pow_apply_mem_genSub {M : Type*} [AddCommGroup M] [Module ℂ M]
    {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M} (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ)
    {v : M} (hv : v ∈ genSub E S) : ((actM E X) ^ m) v ∈ genSub E S := by
  have hE : ∀ a b, ∀ w ∈ genSub E S, E a b w ∈ genSub E S := by
    intro a b w hw
    simp only [genSub, Submodule.mem_sInf, Set.mem_setOf_eq] at hw ⊢
    intro T hT
    exact hT.2 a b w (hw T hT)
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (hE a b _ ih)
end Rep
section Propag
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
end Propag
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (dual : Bool) {V' : Submodule ℂ D} {ι : D →ₗ[ℂ] (Fin n → D)}
    (hιE : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x))
    (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) {y : D} (hy : y ∈ genSub E V') :
    ι (((actM E X) ^ m) y) = ((actM (tensF dual E) X) ^ m) (ι y) := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    have h1 : actM E X y ∈ genSub E V' := by simpa using actM_pow_apply_mem_genSub X 1 hy
    rw [pow_succ, Module.End.mul_apply, ih h1,
      coefE_ι_act dual hιE X hy, pow_succ, Module.End.mul_apply]
end ReciprocityTheory.ChartRestriction.DS
