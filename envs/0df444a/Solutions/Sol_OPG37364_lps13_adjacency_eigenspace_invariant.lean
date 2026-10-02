-- Prove2me | solution 1 for OPG37364.lps13_adjacency_eigenspace_invariant
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T15:40:36.786465+00:00
-- url     : https://prove2.me/submissions/fa89a4ec-9b2c-4a6a-8afa-42ce793f8b21

import Definitions.Def_opg37364_lps13_eigenspaces

set_option autoImplicit false

namespace OPG37364

/-- Every ordinary adjacency eigenspace of the fixed-p=13 PGL Cayley graph
is preserved by the natural PSL₂ left action. The eigenspace may be zero. -/
theorem _root_.solution
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q) (μ : ℝ) :
    ∀ g : LPS13ActingGroup q,
      Set.MapsTo (lps13LeftRepresentation g)
        ((lps13AdjacencyEnd hq i).eigenspace (μ : ℂ))
        ((lps13AdjacencyEnd hq i).eigenspace (μ : ℂ)) := by
  intro g f hf
  have hf' := Module.End.mem_eigenspace_iff.mp hf
  apply Module.End.mem_eigenspace_iff.mpr
  calc
    lps13AdjacencyEnd hq i (lps13LeftRepresentation g f) =
        lps13LeftRepresentation g (lps13AdjacencyEnd hq i f) :=
      LinearMap.congr_fun (lps13AdjacencyEnd_commute hq i g).eq f
    _ = (μ : ℂ) • lps13LeftRepresentation g f := by
      rw [hf', map_smul]

end OPG37364
