-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.sum_finset_fin_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:07:01.119896+00:00
-- url     : https://prove2.me/submissions/e4d169db-20c4-4ac0-8d68-553e9920925f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {β : Type*} [AddCommMonoid β] {n : ℕ} (g : Finset (Fin (n + 1)) → β) :
    ∑ S, g S = ∑ S : Finset (Fin n),
      (g (S.map (Fin.succEmb n)) + g (insert 0 (S.map (Fin.succEmb n)))) := by
  classical
  have hu : (Finset.univ : Finset (Fin (n + 1))) =
      insert 0 (Finset.univ.map (Fin.succEmb n)) := by
    ext x; cases x using Fin.cases <;> simp
  have h0 : (0 : Fin (n + 1)) ∉ Finset.univ.map (Fin.succEmb n) := by
    simp [Fin.succ_ne_zero]
  have hp : (Finset.univ.map (Fin.succEmb n)).powerset =
      (Finset.univ : Finset (Finset (Fin n))).map (Finset.mapEmbedding (Fin.succEmb n)).toEmbedding := by
    ext t; simp [Finset.subset_map_iff, eq_comm]
  rw [← Finset.powerset_univ, hu, Finset.sum_powerset_insert h0, hp,
    Finset.sum_map, Finset.sum_map, ← Finset.sum_add_distrib]
  rfl
end ReciprocityTheory.AnForm.A
