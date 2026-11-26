-- Prove2me | solution 1 for SemigroupBetti.IsPairAntichain.fst_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:02:54.978494+00:00
-- url     : https://prove2.me/submissions/d95cb501-11e1-408d-8387-f42673ccc201

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_SharesVar_symm


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
variable {T : Finset (ℕ × ℕ)}
namespace SemigroupBetti
namespace IsPairAntichain
theorem _root_.solution (hT : IsPairAntichain T) {x y : ℕ × ℕ} (hx : x ∈ T) (hy : y ∈ T)
    (h : x.1 = y.1) : x = y := by
  rcases le_total x.2 y.2 with h2 | h2
  · exact hT x hx y hy h.le h2
  · exact (hT y hy x hx h.ge h2).symm
end IsPairAntichain
end SemigroupBetti
