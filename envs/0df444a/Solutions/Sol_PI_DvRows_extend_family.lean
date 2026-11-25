-- Prove2me | solution 1 for PI.DvRows.extend_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:36:03.053689+00:00
-- url     : https://prove2.me/submissions/96e99afb-cb69-4632-96b4-28dd536ff4a7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Adapted
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] {k m : ℕ} (u : Fin k → V) (t : Fin m → V)
    (hu : LinearIndependent K u) :
    ∃ (d : ℕ) (z : Fin d → V), LinearIndependent K (Fin.append u z) ∧ (∀ i, ∃ j, z i = t j) ∧
      Set.range u ∪ Set.range t ⊆ Submodule.span K (Set.range (Fin.append u z)) := by
  classical
  let v : Fin k ⊕ Fin m → V := Sum.elim u t
  have hs : LinearIndepOn K v (Set.range Sum.inl) := by
    rw [linearIndepOn_range_iff Sum.inl_injective]
    exact hu
  obtain ⟨b, -, hsb, hspan, hli⟩ := exists_linearIndepOn_extension hs (Set.subset_univ _)
  let T : Finset (Fin m) := Finset.univ.filter (fun j => Sum.inr j ∈ b)
  let en : Fin T.card ↪o Fin m := T.orderEmbOfFin rfl
  have hen : ∀ i, en i ∈ T := fun i => T.orderEmbOfFin_mem rfl i
  let g : Fin (k + T.card) → Fin k ⊕ Fin m := Fin.append Sum.inl (Sum.inr ∘ en)
  have hg : Function.Injective g := by
    intro i j hij
    revert hij
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i <;>
      refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j <;> intro hij <;>
      simp [g, Fin.append_left, Fin.append_right] at hij ⊢
    · exact hij
    · exact hij
  have hrange : Set.range g = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
      · simp only [g, Fin.append_left]; exact hsb ⟨i', rfl⟩
      · simp only [g, Fin.append_right, Function.comp]
        have := hen i'
        simpa [T] using this
    · intro hx
      rcases x with x | x
      · exact ⟨Fin.castAdd _ x, by simp [g]⟩
      · have hxT : x ∈ T := by simp [T, hx]
        obtain ⟨i, hi⟩ : ∃ i, en i = x := by
          have := T.range_orderEmbOfFin rfl
          have hx' : x ∈ Set.range (T.orderEmbOfFin rfl) := by rw [this]; exact hxT
          exact hx'
        exact ⟨Fin.natAdd _ i, by simp [g, hi]⟩
  have hvg : v ∘ g = Fin.append u (t ∘ en) := by
    funext i
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
    · simp [g, v]
    · simp [g, v]
  refine ⟨T.card, t ∘ en, ?_, fun i => ⟨en i, rfl⟩, ?_⟩
  · rw [← hvg, ← linearIndepOn_range_iff hg, hrange]
    exact hli
  · have h1 : v '' b = Set.range (Fin.append u (t ∘ en)) := by
      rw [← hvg, Set.range_comp, hrange]
    rw [← h1]
    intro x hx
    apply hspan
    rcases hx with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨Sum.inl i, Set.mem_univ _, rfl⟩
    · exact ⟨Sum.inr j, Set.mem_univ _, rfl⟩
end PI.DvRows
