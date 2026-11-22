-- Prove2me | solution 1 for OrderClosures.CNF_cnfValue_add_monomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:49.791809+00:00
-- url     : https://prove2.me/submissions/acea1678-6999-40f3-932c-591bc4e57522

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Theorems.Thm_OrderClosures_CNF_cnfValue
public import Theorems.Thm_OrderClosures_cnfValue_cnfAddMonomial
public import Theorems.Thm_OrderClosures_cnfAddMonomial_valid

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hpos : ∀ p ∈ l, 0 < p.2)
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0)
    (γ d : Ordinal.{u}) (hdpos : 0 < d) (hdlt : d < Ordinal.omega0) :
    Ordinal.CNF Ordinal.omega0
      (cnfValue l + Ordinal.omega0 ^ γ * d) = cnfAddMonomial l γ d := by
  rw [← cnfValue_cnfAddMonomial l hsorted hlt γ d hdpos]
  obtain ⟨hsorted', hpos', hlt'⟩ :=
    cnfAddMonomial_valid l hsorted hpos hlt γ d hdpos hdlt
  exact CNF_cnfValue _ hsorted' hpos' hlt'
end OrderClosures
