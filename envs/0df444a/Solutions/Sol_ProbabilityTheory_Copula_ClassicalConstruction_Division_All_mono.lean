-- Prove2me | solution 1 for ProbabilityTheory.Copula.ClassicalConstruction.Division.All.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:54:56.27352+00:00
-- url     : https://prove2.me/submissions/d0c01656-d8f6-43dc-941c-7e648eca5306

module
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_Classical_Approximation

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval ENNReal BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}
open ProbabilityTheory.Copula.ClassicalConstruction
open ProbabilityTheory.Copula.ClassicalConstruction.Division
variable {a b : Fin d → I}
namespace ProbabilityTheory.Copula.ClassicalConstruction.Division
namespace All
theorem _root_.solution {P Q : (Fin d → I) → (Fin d → I) → Prop} {D : Division a b}
    (h : D.All P) (hPQ : ∀ a b, P a b → Q a b) : D.All Q := by
  induction D with
  | leaf hab => exact hPQ _ _ h
  | cut i t hat htb left right ihl ihr => exact ⟨ihl h.1, ihr h.2⟩
end All
end ProbabilityTheory.Copula.ClassicalConstruction.Division
