-- Prove2me | solution 1 for PathsTreesFlowers.Invariance.exposed_only_outer_6_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:03:37.736894+00:00
-- url     : https://prove2.me/submissions/af1099d6-d383-4b63-acc7-5389f5491f21

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic.Linarith
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Definitions.Def_PathsTreesFlowers_Invariance_Config
import Theorems.Thm_PathsTreesFlowers_Invariance_max_matching_erase_6_6

open PathsTreesFlowers.Invariance

/-- 6.6, p. 465: only the outer vertices are ever exposed for a maximum matching (the converse
half of 6.2 (a)). -/
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : Config60 G M) :
    ∀ (M' : Finset E) (v : V), PathsTreesFlowers.Duality.IsMaxMatching G M' →
      PathsTreesFlowers.Duality.IsExposed G M' v → v ∈ outerSet C := by
  intro M' v hM' hexp
  by_contra hv
  obtain ⟨⟨e, heM, hve⟩, herase⟩ := max_matching_erase_6_6 G M C v hv
  have hmax_erase := herase e heM hve
  have hM'_sub : M' ⊆ (induced G (Finset.univ.erase v)).edges := by
    intro f hf
    simp only [induced, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sym2_iff,
      Finset.mem_erase, ne_eq]
    intro w hw
    refine ⟨?_, trivial⟩
    rintro rfl
    exact hexp f hf hw
  have hle₁ : M'.card ≤ (M.erase e).card := hmax_erase.2.2 M' hM'_sub hM'.1
  have hle₂ : M.card ≤ M'.card := hM'.2 M C.hM.1
  have hcard : (M.erase e).card + 1 = M.card := Finset.card_erase_add_one heM
  omega
