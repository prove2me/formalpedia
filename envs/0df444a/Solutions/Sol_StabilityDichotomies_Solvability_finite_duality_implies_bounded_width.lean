-- Prove2me | solution 1 for StabilityDichotomies.Solvability.finite_duality_implies_bounded_width
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:22:34.876445+00:00
-- url     : https://prove2.me/submissions/b8d7e34c-de20-4a34-a0c2-53f0da1f59e4

import Definitions.Def_StabilityDichotomies_Approximability_Core
import Definitions.Def_StabilityDichotomies_Solvability_FiniteDuality
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability

private theorem locally_satisfying_induced {Γ : Language} {V : Type} [Fintype V]
    (I : Instance Γ V) (U : Finset V) (g : V → Option Bool)
    (hdom : partialDomain g = U) (hloc : LocallySatisfying I g) : Satisfiable (I.induce U) := by
  refine ⟨fun v => (g v.1).getD false, ?_⟩
  intro c' hc'
  change c' ∈ I.constraints.bind (fun c =>
    if h : ∀ i, c.scope i ∈ U then {⟨c.rel, fun i => ⟨c.scope i, h i⟩⟩} else 0) at hc'
  obtain ⟨c,hc,hc'⟩ := Multiset.mem_bind.mp hc'
  split_ifs at hc' with hscope
  · have hc'eq : c' = ⟨c.rel, fun i => ⟨c.scope i, hscope i⟩⟩ := by simpa using hc'
    subst c'
    apply hloc c hc
    intro i
    have hi : c.scope i ∈ partialDomain g := by rw [hdom]; exact hscope i
    exact (Finset.mem_filter.mp hi).2
  · simp at hc'

theorem solution (Γ : Language) (hdual : FiniteDuality Γ) :
    BoundedWidth Γ := by
  obtain ⟨d, hd⟩ := hdual
  refine ⟨max 1 d, max 1 d, le_max_left _ _, le_refl _, ?_⟩
  intro V _ I H hH
  by_contra hunsat
  obtain ⟨U,hU,hbad⟩ := hd V I hunsat
  obtain ⟨g,hg⟩ := hH.1
  let g0 := partialRestrict g ∅
  have hg0 : g0 ∈ H := hH.2.2.1 g hg ∅ (by simp)
  have hdom0 : partialDomain g0 = ∅ := by
    ext v
    simp [g0, partialDomain, partialRestrict]
  have hU' : U.card ≤ max 1 d := le_trans hU (le_max_right _ _)
  obtain ⟨gU,hgU,hdomU,_⟩ := hH.2.2.2 ∅ U (by simp) (by simp) hU' g0 hg0 hdom0
  exact hbad (locally_satisfying_induced I U gU hdomU (hH.2.1 gU hgU).1)

