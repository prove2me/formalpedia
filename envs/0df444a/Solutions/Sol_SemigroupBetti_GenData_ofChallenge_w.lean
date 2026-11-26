-- Prove2me | solution 1 for SemigroupBetti.GenData.ofChallenge_w
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:17:49.017651+00:00
-- url     : https://prove2.me/submissions/445ee944-8564-448d-b632-ca417ee0ab9d

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (n : Fin 4 → ℕ) (hpos : 0 < n 0) (hmono : StrictMono n)
  (hgcd : Finset.univ.gcd n = 1)
  (hmin : ∀ i : Fin 4, n i ∉ AddSubmonoid.closure (n '' {j | j ≠ i}))
namespace SemigroupBetti.GenData
theorem _root_.solution : (ofChallenge n hpos hmono hgcd hmin).w = n 3 - n 0 := rfl
end SemigroupBetti.GenData
