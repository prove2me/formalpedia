-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.latLoc_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:52:47.76494+00:00
-- url     : https://prove2.me/submissions/76e36f1c-4920-4a8e-8d92-c8804a3cc81f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_NatCastTmul
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).FG := by
  classical
  have hL : (I.L.restrictScalars ℤ).FG := I.L_fg.restrictScalars
  obtain ⟨S, hS⟩ := hL
  have hSL : ∀ s ∈ S, s ∈ I.L := by
    intro s hs
    have : s ∈ I.L.restrictScalars ℤ := hS ▸ Submodule.subset_span hs
    exact this
  refine ⟨S.image (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v)), ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro y hy
    simp only [Finset.coe_image] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact Submodule.subset_span ⟨s, hSL s hs, rfl⟩
  · rw [Formalism.L2.SG.Sub.latLoc, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl' : l ∈ Submodule.span ℤ (S : Set (Fin I.n → I.E)) := by
      rw [hS]; exact hl
    clear hl
    induction hl' using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨s, hs, rfl⟩)
    | zero =>
      have : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (0 : Fin I.n → I.E) = 0 := by
        funext i; simp [Formalism.L2.SG.Sub.ratV]
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (x + y) =
          Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) x +
            Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) y := by
        funext i; simp [Formalism.L2.SG.Sub.ratV]
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (a • x) =
          a • Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) x := by
        funext i; simp [Formalism.L2.SG.Sub.ratV]
      rw [this]; exact Submodule.smul_of_tower_mem _ a hx
end PI.UnitaryGroupMassFormula.ScXuExists
