-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.layer_le_genSub
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T03:16:10.911733+00:00
-- url     : https://prove2.me/submissions/02d7150d-7ddc-4890-9549-8b27d3d3d0ad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
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
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
theorem AuxLG_closed {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} (a b : Fin n) {v : M}
    (hv : v ∈ ReciprocityTheory.ChartRestriction.DS.genSub E V) :
    E a b v ∈ ReciprocityTheory.ChartRestriction.DS.genSub E V := by
  unfold ReciprocityTheory.ChartRestriction.DS.genSub at hv ⊢
  rw [Submodule.mem_sInf] at hv ⊢
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem AuxLG_base {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} :
    V ≤ ReciprocityTheory.ChartRestriction.DS.genSub E V := by
  unfold ReciprocityTheory.ChartRestriction.DS.genSub
  exact le_sInf fun T hT => hT.1


theorem ReciprocityTheory.ChartRestriction.DS.layer_le_genSub (k : ℕ) : layer ε E V k ≤ genSub E V := by
  induction k with
  | zero => exact AuxLG_base
  | succ k ih =>
    simp only [ReciprocityTheory.ChartRestriction.DS.layer]
    refine sup_le ih (iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_)
    rintro _ ⟨v, hv, rfl⟩
    exact AuxLG_closed a b (ih hv)


end

theorem solution {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} (k : ℕ) :
    ReciprocityTheory.ChartRestriction.DS.layer ε E V k ≤ ReciprocityTheory.ChartRestriction.DS.genSub E V :=
  ReciprocityTheory.ChartRestriction.DS.layer_le_genSub k
