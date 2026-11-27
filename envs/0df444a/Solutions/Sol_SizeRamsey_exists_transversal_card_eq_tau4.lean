-- Prove2me | solution 1 for SizeRamsey.exists_transversal_card_eq_tau4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:18:19.064387+00:00
-- url     : https://prove2.me/submissions/afdec223-db7b-4421-8874-511cc4434cc5

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ S : Finset V,
      c4Transversal G S ∧ S.card = tau4 G := by
  have h := Nat.sInf_mem
    (s := {k : ℕ | ∃ S : Finset V, c4Transversal G S ∧ S.card = k})
    ⟨_, Finset.univ, fun _ _ => ⟨0, Finset.mem_univ _⟩, rfl⟩
  exact h
end SizeRamsey
