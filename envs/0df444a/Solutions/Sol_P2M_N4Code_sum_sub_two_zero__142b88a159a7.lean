-- Prove2me | solution 1 for P2M_N4Code_sum_sub_two_zero__142b88a159a7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:20:00.771701+00:00
-- url     : https://prove2.me/submissions/df07ad3f-6362-4782-b96e-3dd743934828

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_P2M_N4Code_sum_sub_two_zero__0b418aa7372d

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (f g : Fin n → ℕ) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : f t₁ + 1 = g t₁) (h2 : f t₂ = g t₂ + 1)
    (hrest : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → f u = g u) :
    (∑ u : Fin n, f u) = (∑ u : Fin n, g u) := by
  exact (sum_sub_two_zero₁ g f t₁ t₂ htne
    (by omega) (by omega) (fun u hu1 hu2 => (hrest u hu1 hu2).symm)).symm
end N4Code
