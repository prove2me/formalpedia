-- Prove2me | solution 1 for ThreeSum.LightSelectedPrime.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:35.213812+00:00
-- url     : https://prove2.me/submissions/5779383c-bb4a-478d-a367-7d25fc26c1ea

import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSum_LightSelectedPrime
import Theorems.Thm_ThreeSum_LightSelectedPrime_prime_zero_eq_selectedPrime
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Definitions.Def_WeightedCache3SUM_Alias_2e17023b917df3d1
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Theorems.Thm_ThreeSum_LightPrimePool_size_pos
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_spec
import Theorems.Thm_ThreeSum_WeightedScore_corrections_zero
import Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightSelectedPrime
open Light LocalCoverBounds LightResidues
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSelectedPrime
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {N free : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 2 < lim.depth) (hN : 0 < N) (hspace : space free N ≤ lim.space) (hword : (word N : ℤ) ≤ lim.word) :
    Meets lim P pMain d [N, free] μ (time N)
      (fun r μ' => r = (selectedPrime N : ℤ) ∧ SegN μ' free (LightPrimePool.values (rootCeiling N)) ∧ Kept μ μ' free) :=
  by
  have hypos := rootCeiling_pos N
  have hy : rootCeiling N ≤ N + 1 := by
    unfold rootCeiling
    have hh := Nat.sqrt_le_self (N - 1)
    omega
  have hwordZ : 100 * ((N : ℤ) + 1) ≤ lim.word := by exact_mod_cast hword
  have hsub : (N : ℤ) - 1 = ((N - 1 : ℕ) : ℤ) := by omega
  have hrootWord : (rootCeiling N : ℤ) ≤ lim.word := by omega
  have hpoolWord : (LightPrimePool.word (rootCeiling N) : ℤ) ≤ lim.word :=
    by
    unfold LightPrimePool.word
    push_cast
    omega
  have hfree : free < lim.space := by
    unfold space LightPrimePool.space at hspace
    omega
  have hselectedWord : (selectedPrime N : ℤ) ≤ lim.word :=
    by
    have hp := (selectedPrime_spec N).2.2
    omega
  apply Meets.of_body S.main
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    |
      refine
        _root_.Light.Ends.callToThen ((sqrt_meets (d := d + 1) (K := N - 1) S.sqrt μ (by omega)) _ (by omega)) ?_ ?_ ?_
          ?_
    | refine _root_.Light.Ends.callToThen (sqrt_meets (d := d + 1) (K := N - 1) S.sqrt μ (by omega)) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsub, LightPrimePool.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hsub, LightPrimePool.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsub, LightPrimePool.time] <;> omega)
    on_goal -1 => (rintro root μ₁ ⟨hr, hmem₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₁
  have hr' : root + 1 = (rootCeiling N : ℤ) := by simpa [rootCeiling] using congrArg (fun z : ℤ => z + 1) hr
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (rootCeiling N : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr', LightPrimePool.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hr', LightPrimePool.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr', LightPrimePool.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    |
      refine
        _root_.Light.Ends.callToThen ((S.pool.meets (d := d + 1) hw hd hypos hspace hpoolWord) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (S.pool.meets (d := d + 1) hw hd hypos hspace hpoolWord) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightPrimePool.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightPrimePool.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightPrimePool.time] <;> omega)
    on_goal -1 => (rintro count μ₂ ⟨hc, hseg, hkept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hlen : 0 < (LightPrimePool.values (rootCeiling N)).length := LightPrimePool.size_pos hypos
  have hfirst : μ₂ free = (selectedPrime N : ℤ) :=
    by
    have hh := hseg 0 (by simp; exact hlen)
    rw [← prime_zero_eq_selectedPrime]
    change μ₂ free = ((LightPrimePool.values (rootCeiling N)).getD 0 0 : ℤ)
    rw [List.getD_eq_getElem _ _ hlen]
    simpa using hh
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (selectedPrime N : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hfirst, LightPrimePool.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hfirst, LightPrimePool.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hfirst, LightPrimePool.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  exact ⟨rfl, hseg, hkept⟩
end Procs
end ThreeSum.LightSelectedPrime
