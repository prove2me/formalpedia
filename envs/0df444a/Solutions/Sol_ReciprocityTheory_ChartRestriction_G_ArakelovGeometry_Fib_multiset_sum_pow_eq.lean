-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.multiset_sum_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:51:59.959536+00:00
-- url     : https://prove2.me/submissions/3db25c53-2517-4f57-ae39-010ee420ba78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_sum_pow_eq_aeval_psumQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution {S : Type*} [CommRing S] (s : Multiset S) {n : ℕ}
    (hn : Multiset.card s = n) (k : ℕ) :
    (s.map (· ^ k)).sum = aeval (fun i : Fin n => s.esymm (i + 1)) (psumQ n k) := by
  obtain ⟨l, rfl⟩ : ∃ l : List S, (l : Multiset S) = s := ⟨_, (Quotient.exists_rep s).choose_spec⟩
  rw [Multiset.coe_card] at hn
  subst hn
  have hs : (Finset.univ.val.map l.get : Multiset S) = (l : Multiset S) := by
    first
    | rw [Fin.univ_val_map, List.ofFn_get]
    | simp [Fin.univ_val_map, List.ofFn_get]
  have key := sum_pow_eq_aeval_psumQ l.get k
  rw [hs] at key
  rw [← key, Finset.sum_eq_multiset_sum, ← hs, Multiset.map_map] <;> rfl
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
