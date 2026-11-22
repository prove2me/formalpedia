-- Prove2me | solution 1 for UlmsTheorem.kaplansky_extend_one_of_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:02:33.35511+00:00
-- url     : https://prove2.me/submissions/298eebb6-fb16-4470-9ede-6caf9ef7355f

module
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
public import Theorems.Thm_UlmsTheorem_kaplansky_extend_one_of_target
public import Theorems.Thm_UlmsTheorem_exists_kaplanskyTarget_caseI
public import Theorems.Thm_UlmsTheorem_exists_kaplanskyTarget_caseII

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
namespace UlmsTheorem
theorem _root_.solution
    (hG : IsReducedPGroup p G)
    (s : UlmStage p (G := G) (H := H))
    {x : G} {α : Ordinal.{0}}
    (hinv : ulmInvariant p α (G := G) = ulmInvariant p α (G := H))
    (hx_notin : x ∉ s.A)
    (hpxA : p • x ∈ s.A)
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hxProper : IsProper p s.A x)
    (hpxMax : ∀ y : G, y - x ∈ s.A → IsProper p s.A y →
      ulmHeight p (p • y) ≤ ulmHeight p (p • x)) :
    ∃ (s' : UlmStage p (G := G) (H := H))
      (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      x ∈ s'.A ∧
      ∀ a : s.A, (s'.e ⟨a, hAA a.prop⟩ : H) = s.e a := by
  obtain ⟨w, hpw, hwα, hwSucc, hwProper⟩ :
      ∃ w : H,
        p • w = (s.e ⟨p • x, hpxA⟩ : H) ∧
        w ∈ ulmSubgroup p α (G := H) ∧
        w ∉ ulmSubgroup p (Order.succ α) (G := H) ∧
        IsProper p s.B w := by
    by_cases hcaseII :
        p • x ∈
          ulmSubgroup p (Order.succ (Order.succ α)) (G := G)
    · exact exists_kaplanskyTarget_caseII p (UlmStage.at (p := p) s α) hinv hpxA
        hxα hxSucc hxProper hcaseII
    · exact exists_kaplanskyTarget_caseI p (UlmStage.at (p := p) s α) hpxA
        hxα hxSucc hxProper
        hpxMax hcaseII
  exact kaplansky_extend_one_of_target p hG s hx_notin hpxA hpw
    hxα hxSucc hwα hwSucc hxProper hwProper
end UlmsTheorem
