-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isHomogeneous_lex_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:25.392071+00:00
-- url     : https://prove2.me/submissions/b747cfde-1852-45ab-96ad-54396bf088ea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsPrimeFiltrationOfIsMultiHomogIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_of_mem_lex
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mem_lex_of_isMultiHomog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
attribute [local instance 2000] lexDecEq
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (e : K ≃ Fin n) (J : Ideal (MRing ι)) :
    J.IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) ↔ IsMultiHomogIdeal J := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists _ J).1 h
    refine ⟨Subtype.val '' S, ?_, hS⟩
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨i, hi⟩ := x.2
    exact ⟨_, isMultiHomog_of_mem_lex e hi⟩
  · rintro ⟨S, hS, rfl⟩
    apply Ideal.homogeneous_span
    intro x hx
    obtain ⟨a, ha⟩ := hS x hx
    exact ⟨_, mem_lex_of_isMultiHomog e ha⟩
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
