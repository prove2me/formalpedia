-- Prove2me | solution 1 for QuarterSumLadder.le_vlam_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:12:27.734826+00:00
-- url     : https://prove2.me/submissions/4808aad0-c3ae-4b54-8e83-a00c43feff48

module
public import Definitions.Def_QuarterSumLadder_Ladder
public import Definitions.Def_QuarterSumLadder_Boundary

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution {z : GaussianInt} (hz : z ≠ 0) {k : ℕ} (h1 : (2 : ℤ) ^ k ∣ z.norm) :
    k ≤ vlam z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : z.norm ≠ 0 := by rwa [Ne, Zsqrtd.norm_eq_zero (fun n h => by nlinarith [sq_nonneg n])]
  rcases (padicValInt_dvd_iff (p := 2) k z.norm).1 (by exact_mod_cast h1) with a | a
  · exact absurd a hne
  · exact a
end QuarterSumLadder
