-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.exists_of_ratRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:36:27.309122+00:00
-- url     : https://prove2.me/submissions/cc8aa28f-dd8b-4905-b92e-0c91513cd354

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane Pointwise
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {Ω M : Type*} [Field Ω] [IsAlgClosed Ω] [Field M] (e : Ω →+* M)
    (f₀ : ℚ →+* Ω) (f : ℚ →+* M) {p : Polynomial ℚ} (hp : p ≠ 0) {y : M}
    (hy : p.eval₂ f y = 0) : ∃ a : Ω, e a = y := by
  have hP : p.map f₀ ≠ 0 := (Polynomial.map_ne_zero_iff f₀.injective).2 hp
  have hr : ((p.map f₀).map e).roots = (p.map f₀).roots.map e :=
    (IsAlgClosed.splits _).roots_map e
  have hf : e.comp f₀ = f := Subsingleton.elim _ _
  have hmem : y ∈ ((p.map f₀).map e).roots := by
    rw [Polynomial.mem_roots ((Polynomial.map_ne_zero_iff e.injective).2 hP), Polynomial.map_map, hf,
      Polynomial.IsRoot.def, Polynomial.eval_map]
    exact hy
  rw [hr, Multiset.mem_map] at hmem
  obtain ⟨a, -, ha⟩ := hmem
  exact ⟨a, ha⟩
end ReciprocityTheory.ChartRestriction.L1
