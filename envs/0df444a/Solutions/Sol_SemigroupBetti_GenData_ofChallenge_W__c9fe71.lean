-- Prove2me | solution 1 for SemigroupBetti.GenData.ofChallenge_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:18:27.597992+00:00
-- url     : https://prove2.me/submissions/2e133255-fad8-4b5d-a047-6c489f98f16d

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
theorem _root_.solution : (ofChallenge n hpos hmono hgcd hmin).W =
    (n 3 - n 0) / Nat.gcd (n 1 - n 0) (Nat.gcd (n 2 - n 0) (n 3 - n 0)) := rfl
end SemigroupBetti.GenData
