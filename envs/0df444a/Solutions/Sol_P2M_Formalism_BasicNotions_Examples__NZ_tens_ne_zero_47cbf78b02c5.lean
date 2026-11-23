-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_tens_ne_zero_47cbf78b02c5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:23.457996+00:00
-- url     : https://prove2.me/submissions/19994618-9ab9-4208-9316-1f88f6ab34d8

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_tens_coeff_b71da958868c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open MonoidAlgebra
variable {k : Type} [Field k] {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (x : ∀ i, MonoidAlgebra k (G i)) (h : ∀ i, x i ≠ 0) : tens x ≠ 0 := by
  have h1 : ∀ i, ∃ g : G i, (x i).coeff g ≠ 0 := fun i => by
    by_contra hc
    push Not at hc
    exact h i (MonoidAlgebra.coeff_injective (Finsupp.ext hc))
  choose g hg using h1
  intro h0
  have := congrArg (fun z => z.coeff g) h0
  simp only [tens_coeff] at this
  exact (Finset.prod_ne_zero_iff.mpr fun i _ => hg i) this
end Formalism.BasicNotions.Examples₂.NZ
