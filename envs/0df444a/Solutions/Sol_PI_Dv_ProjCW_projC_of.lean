-- Prove2me | solution 1 for PI.Dv.ProjCW.projC_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:54:10.575672+00:00
-- url     : https://prove2.me/submissions/66a74bf7-1236-4357-9a34-d20af4ce5377

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSpans_SpanPowSmul
import Theorems.Thm_PI_Dv_ProjCW_locLe_map
import Theorems.Thm_PI_Dv_ProjCW_span_map_eq
import Theorems.Thm_PI_Dv_ProjCW_span_pow_smul
import Theorems.Thm_PI_Dv_ProjCW_ker_one_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjCW
open Formalism.BasicNotions NumberField IsDedekindDomain
namespace PI.Dv.ProjCW
theorem _root_.solution (hI : PI.Dv.IdxCalc) : PI.Dv.ProjC := by
  intro K _ _ _ _ A e n hP
  obtain ⟨hG, -, he, -, -⟩ := hP
  obtain ⟨-, hAfg, hAsp⟩ := hG
  intro Th hTh
  obtain ⟨hTfg, hTsp⟩ := hTh
  have hker : LinearMap.ker (1 - e) = LinearMap.range e := ker_one_sub e he
  have hsp : Submodule.span K (A.L : Set A.V) = Submodule.span K (Th : Set A.V) := by rw [hAsp, hTsp]
  set φ : A.V →ₗ[𝓞 K] A.V := (1 - e : Module.End K A.V).restrictScalars (𝓞 K) with hφ
  set φA := A.L.map φ with hφA
  set φT := Th.map φ with hφT
  have fgA : φA.FG := hAfg.map φ
  have fgT : φT.FG := hTfg.map φ
  have spA : Submodule.span K (φA : Set A.V) = LinearMap.range (1 - e) := span_map_eq (1 - e) A.L hAsp
  have spT : Submodule.span K (φT : Set A.V) = LinearMap.range (1 - e) := span_map_eq (1 - e) Th hTsp
  have rkA : Formalism.HN.rkK φA = dimE A (1 - e) := by
    unfold Formalism.HN.rkK dimE; rw [spA]
  have rkT : Formalism.HN.rkK φT = dimE A (1 - e) := by
    unfold Formalism.HN.rkK dimE; rw [spT]
  have hex : ∀ w, idxAt w A.L Th = idxAt w (cutE A e A.L) (cutE A e Th) + idxAt w φA φT := by
    intro w
    have h3 := (hI K A.V w A.L Th hAfg hTfg hsp).2.2.1 A.V (1 - e)
    rw [hker] at h3
    exact h3
  refine ⟨?_, ?_, ?_⟩
  · intro w F hL
    have h4 := (hI K A.V w φA φT fgA fgT (spA.trans spT.symm)).2.2.2.1 F (locLe_map w F Th A.L φ hL)
    rw [rkA] at h4
    have := hex w
    linarith
  · intro w F hL
    set P : Submodule (𝓞 K) A.V := (w.asIdeal ^ F) • φT with hPdef
    have fgP : P.FG := Submodule.FG.of_le fgT Submodule.smul_le_right
    have spP : Submodule.span K (P : Set A.V) = LinearMap.range (1 - e) := by
      rw [hPdef, span_pow_smul, spT]
    have hLP : LocLe w 0 P φA := by
      have := locLe_map w 0 ((w.asIdeal ^ F) • Th) A.L φ hL
      rw [Submodule.map_smul''] at this
      exact this
    have h2 := (hI K A.V w φA P fgA fgP (spA.trans spP.symm)).2.1 φT fgT (spT.trans spP.symm)
    have h4 := (hI K A.V w φA P fgA fgP (spA.trans spP.symm)).2.2.2.1 0 hLP
    have h5 := (hI K A.V w φT φT fgT fgT rfl).2.2.2.2.1 F
    rw [rkT] at h5
    have hanti : idxAt w P φT = - idxAt w φT P := by
      unfold idxAt; ring
    have := hex w
    push_cast at h4
    linarith
  · intro x hx
    obtain ⟨hxT, y, hy⟩ := hx
    refine ⟨x, hxT, ?_⟩
    show e x = x
    rw [← hy, ← Module.End.mul_apply, he]
end PI.Dv.ProjCW
