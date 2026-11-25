-- Prove2me | solution 1 for PositivityTheory.CW.casimir_eigen_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:35:52.071842+00:00
-- url     : https://prove2.me/submissions/ea817221-1d5c-46a9-8e95-e2d267fb4baf

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CasimirRealScalar
import Theorems.Thm_PositivityTheory_CW_CasimirEigenvector_comm_casimirK
import Theorems.Thm_PositivityTheory_CW_CasimirEigenvector_exists_eig_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
namespace PositivityTheory.CW
theorem _root_.solution : A3 := by
  intro n ε V _ _ E h T hT
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨0, fun v => Subsingleton.elim _ _⟩
  obtain ⟨μ, v, hv0, hv⟩ := CasimirEigenvector.exists_eig_ne h
  set W := Module.End.eigenspace (casimirK ε E) (μ : ℂ) with hWdef
  have hWle : W ≤ Submodule.span ℂ {v | ∃ ν : ℝ, ν ≤ μ ∧ Eig ε E ν v} := by
    intro x hx
    apply Submodule.subset_span
    exact ⟨μ, le_rfl, Module.End.mem_eigenspace_iff.mp hx⟩
  have := h.fin μ
  have : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWle
  have hvW : v ∈ W := Module.End.mem_eigenspace_iff.mpr hv
  have : Nontrivial W := ⟨⟨⟨v, hvW⟩, 0, fun he => hv0 (congrArg Subtype.val he)⟩⟩
  have hTW : ∀ x ∈ W, T x ∈ W := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    have hc := congrArg (fun f : Module.End ℂ V => f x) (CasimirEigenvector.comm_casimirK (ε := ε) T hT)
    simp only [Module.End.mul_apply] at hc
    rw [hc, hx, map_smul]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T.restrict hTW)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hN : LinearMap.ker (T - c • 1) = ⊥ ∨ LinearMap.ker (T - c • 1) = ⊤ := by
    apply h.irr
    intro a b x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have he := congrArg (fun f : Module.End ℂ V => f x) (hT a b)
    simp only [Module.End.mul_apply] at he
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hx ⊢
    rw [← he, ← LinearMap.map_smul, ← map_sub, hx, map_zero]
  have hw1 : T (w : V) = c • (w : V) := by
    have := Module.End.mem_eigenspace_iff.mp hw.1
    exact congrArg Subtype.val this
  have hw0 : (w : V) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
  rcases hN with hN | hN
  · exfalso
    apply hw0
    have : (w : V) ∈ LinearMap.ker (T - c • 1) := by
      rw [LinearMap.mem_ker]
      simp [hw1]
    rw [hN] at this
    exact (Submodule.mem_bot ℂ).mp this
  · intro x
    have : x ∈ LinearMap.ker (T - c • 1) := by rw [hN]; trivial
    rw [LinearMap.mem_ker] at this
    simpa [sub_eq_zero] using this
end PositivityTheory.CW
