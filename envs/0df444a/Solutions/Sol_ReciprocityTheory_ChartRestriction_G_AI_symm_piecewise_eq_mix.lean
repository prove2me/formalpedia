-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.symm_piecewise_eq_mix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:35:26.238583+00:00
-- url     : https://prove2.me/submissions/9da37c6a-177a-4c37-aee0-cc6a3460c67f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_CompRightEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_symm_piecewise_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (x y : V) (s : Finset (Fin n)) :
    I (s.piecewise (fun _ => x) fun _ => y) = I (mix s.card x y) := by
  classical
  set t : Finset (Fin n) := Finset.univ.filter fun i : Fin n => (i : ℕ) < s.card with ht_def
  have ht : t.card = s.card := by
    have hle : s.card ≤ n := by simpa using Finset.card_le_univ s
    have hmap : t.map Fin.valEmbedding = Finset.range s.card := by
      ext m
      simp only [ht_def, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
        Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hi
      · intro hm
        exact ⟨⟨m, by omega⟩, hm, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, hmap, Finset.card_range]
  rw [symm_piecewise_eq I hI x y s t ht.symm]
  congr 1
  funext i
  simp [ht_def, mix, Finset.piecewise]
end ReciprocityTheory.ChartRestriction.G.AI
