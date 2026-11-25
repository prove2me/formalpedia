-- Prove2me | solution 1 for ReciprocityTheory.Coh.TorsionRankLength.len_quot_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:15.422776+00:00
-- url     : https://prove2.me/submissions/15e4efc0-93b3-4ab9-8adc-ea97f1ebaf76

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_RankLenA
import Theorems.Thm_ReciprocityTheory_Coh_TorsionRankLength_len_sub_add_quot
import Theorems.Thm_ReciprocityTheory_Coh_TorsionRankLength_len_K_eq_len_quot
import Theorems.Thm_ReciprocityTheory_Coh_TorsionRankLength_len_quot_pow
import Theorems.Thm_ReciprocityTheory_Coh_TorsionRankLength_torsion_finLen
import Theorems.Thm_ReciprocityTheory_Coh_TorsionRankLength_len_quot_split
import Theorems.Thm_ReciprocityTheory_Coh_TorsionRankLength_len_K_torsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.TorsionRankLength
universe u
open Module Submodule Function
open scoped Pointwise TensorProduct
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace ReciprocityTheory.Coh.TorsionRankLength
theorem _root_.solution (H : Type u) [AddCommGroup H] [Module R H] [Module.Finite R H] {t : R}
    (ht : Irreducible t) (m : ℕ) :
    Module.length R (QuotSMulTop (t ^ m) H) =
        ((m * Module.finrank R H : ℕ) : ℕ∞) + Module.length R (K H (t ^ m)) ∧
      Module.length R (K H (t ^ m)) ≤ Module.length R (torsion R H) ∧
      Module.length R (torsion R H) ≠ ⊤ := by
  have htm : t ^ m ≠ 0 := pow_ne_zero _ ht.ne_zero
  have hT := torsion_finLen (R := R) H
  have hK := len_K_torsion (R := R) H htm
  have hQ := len_K_eq_len_quot hT (t ^ m)
  have hS := len_quot_split (R := R) H (t ^ m)
  have hP := len_quot_pow ht m
  refine ⟨?_, ?_, Module.length_ne_top_iff.2 hT⟩
  · rw [hS, ← hQ, ← hK, hP]
    push_cast
    ring
  · rw [hK]
    have h := len_sub_add_quot (K (torsion R H) (t ^ m))
    rw [h]
    exact le_self_add
end ReciprocityTheory.Coh.TorsionRankLength
