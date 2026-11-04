-- Prove2me | solution 1 for ThreeSum.LightModuloCounts.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:50:19.583893+00:00
-- url     : https://prove2.me/submissions/f2d0d4eb-b8c6-4234-ac37-37427d2890c1

import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_LightLookupSum
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightCyclic
import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_CyclicFold_padTo_length
import Theorems.Thm_ThreeSum_CyclicFold_vector_length
import Theorems.Thm_ThreeSum_KaratsubaInterface_le_capacity
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
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_e1f688d1cacb0f6f
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightResidueHistogram_padded_histogram_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_residue_zmod
import Theorems.Thm_ThreeSum_LightResidueHistogram_signedHistogram_neg
import Theorems.Thm_ThreeSum_LightResidues_residue_lt
import Theorems.Thm_ThreeSum_LightResidues_residues_meets
import Theorems.Thm_ThreeSum_ModuloCounts_correlation_le
import Theorems.Thm_ThreeSum_ModuloCounts_count_eq_correlation
import Theorems.Thm_ThreeSum_ModuloCounts_signedHistogram_congr
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
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
set_option autoImplicit false
open ThreeSum ThreeSum.LightModuloCounts
open Light ThreeSum.LightResidues ThreeSum.LightResidueHistogram
open ThreeSum.KaratsubaInterface ThreeSum.CyclicFold
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightModuloCounts
theorem _root_.solution
    {pMain pCapacity pHist pCyclic pResidues pEmod pHistogram pMultiply pHalf pLinear pFill pLookup : ℕ}
    (hmain : P[pMain]? = some (body pCapacity pHist pCyclic pResidues pLookup))
    (hcap : P[pCapacity]? = some LightCapacity.body)
    (hhist : P[pHist]? = some (LightResidueHistogram.body pResidues pHistogram))
    (hres : P[pResidues]? = some (residuesBody pEmod)) (hem : P[pEmod]? = some emodBody)
    (hcount : P[pHistogram]? = some (LightHistogram.histogramBody pFill))
    (hcyclic : P[pCyclic]? = some (LightCyclic.body pMultiply pLinear))
    (K : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill) (hlookup : P[pLookup]? = some LightLookupSum.body)
    {μ : ℕ → ℤ} {a b c nA nB nC p N free U : ℕ} (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p) (ha : a + nA ≤ free)
    (hb : b + nB ≤ free) (hc : c + nC ≤ free) (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free p N U ≤ lim.space) (hword : (word p N U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 p + 3 ≤ lim.depth) (hA : ∀ i < nA, |μ (a + i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b + i)| ≤ (U : ℤ)) (hC : ∀ i < nC, |μ (c + i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [a, b, c, nA, nB, nC, p, N, free] μ (time p nA nB nC U) fun r μ' =>
      r = (ModuloCounts.count p nA nB nC (fun i => μ (a + i)) (fun i => μ (b + i)) (fun i => μ (c + i)) : ℤ) ∧
        Kept μ μ' free :=
  by
  haveI : NeZero p := ⟨hp.ne'⟩
  let q := capacity p
  have hq : 0 < q := Nat.pow_pos (by decide)
  have hpq : p ≤ q := le_capacity p
  have hspace' : free + 13 * q + N + Nat.log 2 (U + 1) + 2 ≤ lim.space := hspace
  have hkw : (LightKaratsuba.wordBound q N : ℤ) ≤ lim.word :=
    by
    have hh : LightKaratsuba.wordBound q N ≤ word p N U :=
      by
      dsimp [word, q]
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hew : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word :=
    by
    have hh : 4 * U + 4 * p + 16 ≤ word p N U := by unfold word; omega
    have hhZ := (Int.ofNat_le.mpr hh).trans hword
    exact_mod_cast hhZ
  have hcw : ((2 * p + 1 : ℕ) : ℤ) ≤ lim.word := by
    push_cast
    omega
  have hsumword : ((nA * (nB * nC) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hprod : nA * (nB * nC) ≤ N ^ 3 := by
      calc
        _ ≤ N * (N * N) := Nat.mul_le_mul hnA (Nat.mul_le_mul hnB hnC)
        _ = _ := by ring
    have hh : N ^ 3 ≤ word p N U := by unfold word; omega
    exact (Int.ofNat_le.mpr (hprod.trans hh)).trans hword
  let F := signedHistogram p 1 (fun i => μ (c + i)) nC
  let H := signedHistogram p 1 (fun i => μ (b + i)) nB
  have hHneg : signedHistogram p (-1) (fun i => μ (b + i)) nB = (fun z => H (-z)) :=
    by
    funext z
    exact signedHistogram_neg p _ _ z
  have hFbound : Karatsuba.CoeffBound (vector p F) (N : ℤ) :=
    by
    have hh := padded_histogram_bound (p := p) 1 (fun i => μ (c + i)) nC 0
    simp only [padTo, Nat.zero_sub, List.replicate_zero, List.append_nil] at hh
    intro i
    exact (hh i).trans (by exact_mod_cast hnC)
  have hHbound : Karatsuba.CoeffBound (vector p (fun z => H (-z))) (N : ℤ) :=
    by
    have hh := padded_histogram_bound (p := p) (-1) (fun i => μ (b + i)) nB 0
    simp only [padTo, Nat.zero_sub, List.replicate_zero, List.append_nil] at hh
    rw [hHneg] at hh
    intro i
    exact (hh i).trans (Int.ofNat_le.mpr hnB)
  apply Meets.of_body hmain
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
    | refine _root_.Light.Ends.callToThen ((LightCapacity.meets hcap μ hp hcw) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (LightCapacity.meets hcap μ hp hcw) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, q, capacity]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [q, capacity] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, q, capacity] <;> omega)
    on_goal -1 => (rintro capVal μ₀ ⟨hcapacity, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₀
  subst capVal
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (free + q) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
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
    refine _root_.Light.Ends.setToThen (free + 2 * q) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
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
    refine _root_.Light.Ends.setToThen (free + 3 * q) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
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
    refine _root_.Light.Ends.setToThen (free + 5 * q) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
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
    refine _root_.Light.Ends.setToThen (free + 5 * q + N) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
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
        _root_.Light.Ends.callToThen
          ((LightResidueHistogram.meets (d := d + 1) (src := b) (dst := free + 2 * q) (codes := free + 5 * q) (work :=
              free + 5 * q + N) (cap := q) (c := -1) hhist hres hem hcount K.fill hw (by omega) hp hpq (by omega)
              (by omega) (by omega) (by omega) (by norm_num) hew hB)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightResidueHistogram.meets (d := d + 1) (src := b) (dst := free + 2 * q) (codes := free + 5 * q) (work :=
            free + 5 * q + N) (cap := q) (c := -1) hhist hres hem hcount K.fill hw (by omega) hp hpq (by omega)
            (by omega) (by omega) (by omega) (by norm_num) hew hB)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, q, capacity]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [q, capacity] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, q, capacity] <;> omega)
    on_goal -1 => (rintro _ μ₁ ⟨hBseg, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  rw [hHneg] at hBseg
  have hCread (i : ℕ) (hi : i < nC) : μ₁ (c + i) = μ (c + i) := hkeep₁ _ ⟨by omega, by left; omega⟩
  have hC₁ : ∀ i < nC, |μ₁ (c + i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hCread i hi]
    exact hC i hi
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
        _root_.Light.Ends.callToThen
          ((LightResidueHistogram.meets (d := d + 1) (src := c) (dst := free + q) (codes := free + 5 * q) (work :=
              free + 5 * q + N) (cap := q) (c := 1) hhist hres hem hcount K.fill hw (by omega) hp hpq (by omega)
              (by omega) (by omega) (by omega) (by norm_num) hew hC₁)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightResidueHistogram.meets (d := d + 1) (src := c) (dst := free + q) (codes := free + 5 * q) (work :=
            free + 5 * q + N) (cap := q) (c := 1) hhist hres hem hcount K.fill hw (by omega) hp hpq (by omega)
            (by omega) (by omega) (by omega) (by norm_num) hew hC₁)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, q, capacity]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [q, capacity] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, q, capacity] <;> omega)
    on_goal -1 => (rintro _ μ₂ ⟨hCseg, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hCeq := ModuloCounts.signedHistogram_congr (p := p) (c := 1) hCread
  rw [hCeq] at hCseg
  have hBseg₂ : Seg μ₂ (free + 2 * q) (padTo q (vector p (fun z => H (-z)))) :=
    by
    intro i hi
    have hlen : (padTo q (vector p (fun z => H (-z)))).length = q := padTo_length _ _ (by rw [vector_length]; exact hpq)
    have hiq : i < q := by omega
    rw [hkeep₂ _ ⟨by omega, by right; omega⟩]
    exact hBseg i hi
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
        _root_.Light.Ends.callToThen
          ((LightCyclic.correlation_meets (d := d + 1) (k := Nat.clog 2 p) (a := free + q) (b := free + 2 * q) (prod :=
              free + 3 * q) (dst := free) (work := free + 5 * q + N) hcyclic K F H hw hpq hCseg hBseg₂ hFbound hHbound
              (by change free + q + q ≤ free + 5 * q + N; omega) (by change free + 2 * q + q ≤ free + 5 * q + N; omega)
              (by change free + 3 * q + 2 * q ≤ free + 5 * q + N; omega) (by omega)
              (by right; change free + p ≤ free + 3 * q; omega) (by change free + 5 * q + N + 8 * q ≤ lim.space; omega)
              hkw (by omega))
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightCyclic.correlation_meets (d := d + 1) (k := Nat.clog 2 p) (a := free + q) (b := free + 2 * q) (prod :=
            free + 3 * q) (dst := free) (work := free + 5 * q + N) hcyclic K F H hw hpq hCseg hBseg₂ hFbound hHbound
            (by change free + q + q ≤ free + 5 * q + N; omega) (by change free + 2 * q + q ≤ free + 5 * q + N; omega)
            (by change free + 3 * q + 2 * q ≤ free + 5 * q + N; omega) (by omega)
            (by right; change free + p ≤ free + 3 * q; omega) (by change free + 5 * q + N + 8 * q ≤ lim.space; omega)
            hkw (by omega))
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, q, capacity]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [q, capacity] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, q, capacity] <;> omega)
    on_goal -1 => (rintro _ μ₃ ⟨hcorr, hkeep₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hkeepOriginal (i : ℕ) (hi : i < free) : μ₃ i = μ i :=
    by
    rw [hkeep₃ i (by omega) (by left; omega) (by left; omega)]
    exact (hkeep₂ i ⟨by omega, by left; omega⟩).trans (hkeep₁ i ⟨by omega, by left; omega⟩)
  have hAread (i : ℕ) (hi : i < nA) : μ₃ (a + i) = μ (a + i) := hkeepOriginal _ (by omega)
  have hA₃ : ∀ i < nA, |μ₃ (a + i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hAread i hi]
    exact hA i hi
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
        _root_.Light.Ends.callToThen
          ((residues_meets (d := d + 1) (src := a) (dst := free + 5 * q) (work := free + 5 * q + N) (c := 1) hres hem hw
              (by omega) hp (by omega) (by omega) (by omega) (by left; omega) (by norm_num) hew hA₃)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (residues_meets (d := d + 1) (src := a) (dst := free + 5 * q) (work := free + 5 * q + N) (c := 1) hres hem hw
            (by omega) hp (by omega) (by omega) (by omega) (by left; omega) (by norm_num) hew hA₃)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, q, capacity]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [q, capacity] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, q, capacity] <;> omega)
    on_goal -1 => (rintro _ μ₄ ⟨hkeys, hkeep₄⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hkeys₄ (i : ℕ) (hi : i < nA) : μ₄ (free + 5 * q + i) = (residue p 1 (μ (a + i)) : ℤ) := by
    rw [hkeys i hi, hAread i hi]
  have hcorr₄ (r : ℕ) (hr : r < p) : μ₄ (free + r) = (Balancing.correlation F H (r : ZMod p) : ℤ) := by
    rw [hkeep₄ _ ⟨by omega, by left; omega⟩, hcorr r hr]
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
        _root_.Light.Ends.callToThen
          ((LightLookupSum.meets (d := d + 1) (keys := free + 5 * q) (table := free) (n := nA) (p := p) (B := nB * nC)
              hlookup (fun i => residue p 1 (μ (a + i))) (fun r => Balancing.correlation F H (r : ZMod p)) hw (by omega)
              (by omega) hkeys₄ (fun i hi => residue_lt hp 1 (μ (a + i))) hcorr₄
              (fun r hr => ModuloCounts.correlation_le nB nC _ _ _) hsumword)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightLookupSum.meets (d := d + 1) (keys := free + 5 * q) (table := free) (n := nA) (p := p) (B := nB * nC)
            hlookup (fun i => residue p 1 (μ (a + i))) (fun r => Balancing.correlation F H (r : ZMod p)) hw (by omega)
            (by omega) hkeys₄ (fun i hi => residue_lt hp 1 (μ (a + i))) hcorr₄
            (fun r hr => ModuloCounts.correlation_le nB nC _ _ _) hsumword)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, q, capacity]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [q, capacity] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, q, capacity] <;> omega)
    on_goal -1 => (rintro result μ₅ ⟨hresult, hmem₅⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₅
  refine ⟨?_, ?_⟩
  · change result = _
    rw [hresult, ModuloCounts.count_eq_correlation]
    congr 1
    unfold LightLookupSum.prefixSum
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    rw [residue_zmod hp]
    simp only [one_mul]
    rfl
  · intro i hi
    exact (hkeep₄ i ⟨by omega, by left; omega⟩).trans (hkeepOriginal i hi)
end ThreeSum.LightModuloCounts
