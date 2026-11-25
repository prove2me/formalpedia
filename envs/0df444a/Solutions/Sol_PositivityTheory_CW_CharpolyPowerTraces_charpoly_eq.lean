-- Prove2me | solution 1 for PositivityTheory.CW.CharpolyPowerTraces.charpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:45:35.336122+00:00
-- url     : https://prove2.me/submissions/ecd66dc8-7bb8-4396-97c7-e4e17a949ab8

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_NilpotentOfPowerTraces
import Theorems.Thm_PositivityTheory_CW_CharpolyPowerTraces_coeff_succ_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.CharpolyPowerTraces
open Polynomial
namespace PositivityTheory.CW.CharpolyPowerTraces
theorem _root_.solution {R : Type} [CommRing R] [Algebra ℚ R] [Nontrivial R] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) R) (h : ∀ k, (N ^ (k + 1)).trace = 0) : N.charpoly = X ^ n := by
  have hRev : ∀ i, 1 ≤ i → N.charpolyRev.coeff i = 0 := by
    intro i hi
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hi
    exact coeff_succ_zero N h m
  have hdeg : N.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  ext j
  rw [Polynomial.coeff_X_pow]
  rcases lt_trichotomy j n with hj | hj | hj
  · rw [if_neg hj.ne]
    have hz := hRev (n - j) (by omega)
    rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, hdeg,
      Polynomial.revAt_le (by omega)] at hz
    rwa [show n - (n - j) = j by omega] at hz
  · rw [if_pos hj]
    have hl := (Matrix.charpoly_monic N).leadingCoeff
    rw [Polynomial.leadingCoeff, hdeg] at hl
    rw [hj]
    exact hl
  · rw [if_neg hj.ne']
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
end PositivityTheory.CW.CharpolyPowerTraces
