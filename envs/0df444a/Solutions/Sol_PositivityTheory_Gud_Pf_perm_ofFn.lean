-- Prove2me | solution 1 for PositivityTheory.Gud.Pf.perm_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:18:48.333576+00:00
-- url     : https://prove2.me/submissions/5e9ace44-26af-408f-ba4d-63fc82b584a4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitaryDualGL_GenericUnitaryDual_PComb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Gud PositivityTheory.Gud.Pf
namespace PositivityTheory.Gud.Pf
theorem _root_.solution {β : Type*} {h : ℕ} (x : Fin h → β) (l : List β) (hp : List.Perm l (List.ofFn x)) :
    ∃ (y : Fin h → β), List.ofFn y = l ∧ ∃ σ : Equiv.Perm (Fin h), y = fun j => x (σ j) := by
  classical
  have hlen : l.length = h := by rw [hp.length_eq, List.length_ofFn]
  subst hlen
  refine ⟨l.get, List.ofFn_get l, ?_⟩
  have key : ∀ (f : Fin l.length → β) (c : β), Fintype.card {a // f a = c} = (List.ofFn f).count c := by
    intro f c
    rw [Fintype.card_subtype, ← Multiset.coe_count, ← Fin.univ_val_map, Multiset.count_map,
      Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun a _ => eq_comm)
  have hcard : ∀ c, Fintype.card {a // l.get a = c} = Fintype.card {b // x b = c} := by
    intro c
    rw [key, key, List.ofFn_get, hp.count_eq]
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hcard c)),
    funext fun j => (Equiv.ofFiberEquiv_map _ j).symm⟩
end PositivityTheory.Gud.Pf
