-- Prove2me | solution 1 for SizeRamsey.Plan.tau4_eq_of_certificates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:19.881942+00:00
-- url     : https://prove2.me/submissions/c6470ccc-709c-4b3f-ad1d-0cf5b2e571d1

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
public import Theorems.Thm_SizeRamsey_tau4_le_card
public import Theorems.Thm_SizeRamsey_exists_transversal_card_eq_tau4

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution
    {V : Type u} [Fintype V] {G : SimpleGraph V} (k : ℕ)
    (hupper : ∃ S : Finset V, c4Transversal G S ∧ S.card = k)
    (hlower : ∀ S : Finset V,
      S.card < k → ¬ c4Transversal G S) :
    tau4 G = k := by
  obtain ⟨S, hS, rfl⟩ := hupper
  refine le_antisymm (tau4_le_card hS) ?_
  by_contra hlt
  obtain ⟨T, hT, hcard⟩ := exists_transversal_card_eq_tau4 G
  exact hlower T (by omega) hT
end SizeRamsey.Plan
