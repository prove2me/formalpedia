-- Prove2me | solution 1 for QuadraticFloor.exists_admissible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:06:15.808895+00:00
-- url     : https://prove2.me/submissions/173e6fc4-f0f5-48e5-b020-52f4ffa0a2c2

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_exists_admissible__0fba7458ce99


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution {A : ℕ} (hA : Odd A) {B₀ : ℤ} (hB₀ : Int.gcd B₀ A = 1) :
    ∃ B C : ℤ, Admissible A B C ∧ B ≡ B₀ [ZMOD A] :=
  exists_admissible' hA hB₀
end QuadraticFloor
