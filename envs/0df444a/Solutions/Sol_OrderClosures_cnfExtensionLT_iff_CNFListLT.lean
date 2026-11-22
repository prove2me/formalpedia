-- Prove2me | solution 1 for OrderClosures.cnfExtensionLT_iff_CNFListLT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:21.82559+00:00
-- url     : https://prove2.me/submissions/ec102211-b040-4810-ab80-dc5202892d7d

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution {ζ ζ' : Ordinal.{u}} :
    cnfExtensionLT ζ ζ' ↔
      CNFListLT (Ordinal.CNF Ordinal.omega0 ζ)
        (Ordinal.CNF Ordinal.omega0 ζ') := by
  constructor
  · rintro ⟨pre, tail, β, c, γ, d, hζ, hζ', hstep⟩
    refine ⟨pre, tail, (β, c), (γ, d), hζ, hζ', ?_⟩
    rcases hstep with hstep | ⟨hβγ, hpre⟩
    · exact Or.inl hstep
    · refine Or.inr ⟨hβγ, ?_⟩
      rcases hpre with rfl | ⟨δ, e, hlast, hγδ⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨(δ, e), hlast, hγδ⟩
  · rintro ⟨pre, tail, ⟨β, c⟩, ⟨γ, d⟩, hζ, hζ', hstep⟩
    refine ⟨pre, tail, β, c, γ, d, hζ, hζ', ?_⟩
    rcases hstep with hstep | ⟨hβγ, hpre⟩
    · exact Or.inl hstep
    · refine Or.inr ⟨hβγ, ?_⟩
      rcases hpre with rfl | ⟨⟨δ, e⟩, hlast, hγδ⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨δ, e, hlast, hγδ⟩
end OrderClosures
