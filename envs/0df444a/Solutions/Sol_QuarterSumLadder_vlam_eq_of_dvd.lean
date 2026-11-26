-- Prove2me | solution 1 for QuarterSumLadder.vlam_eq_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:12:27.272573+00:00
-- url     : https://prove2.me/submissions/8c16f579-23d0-4634-be40-cff6711b6aad

module
public import Definitions.Def_QuarterSumLadder_Ladder
public import Definitions.Def_QuarterSumLadder_Boundary

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution {z : GaussianInt} {k : ℕ} (h1 : (2 : ℤ) ^ k ∣ z.norm)
    (h2 : ¬ (2 : ℤ) ^ (k + 1) ∣ z.norm) : vlam z = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : z.norm ≠ 0 := fun h => h2 (h ▸ dvd_zero _)
  have a := (padicValInt_dvd_iff (p := 2) k z.norm).1 (by exact_mod_cast h1)
  have b : ¬ (k + 1 ≤ padicValInt 2 z.norm) := fun hle =>
    h2 (by exact_mod_cast (padicValInt_dvd_iff (p := 2) (k + 1) z.norm).2 (Or.inr hle))
  unfold vlam
  rcases a with a | a
  · exact absurd a hne
  · omega
end QuarterSumLadder
