-- Prove2me | solution 1 for ThreeSum.LightSignedRowHash.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:36:23.933805+00:00
-- url     : https://prove2.me/submissions/103ad3b5-f100-48e5-a8a3-bd834a7322dd

import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
import Definitions.Def_Submission_ThreeSum_LightSignedRowHash
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightNaturalDot_meets
import Theorems.Thm_ThreeSum_LightNaturalDot_reduced_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedRowHash
open Light
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightSignedRowHash
namespace Procs
theorem _root_.solution {main src row dst n p b : ℕ} (S : Procs P main) (μ : ℕ → ℤ) (z : ℕ → ℤ) (coeff : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth + 2 < lim.depth) (hbp : b < p) (hsrc : src + n ≤ dst)
    (hrow : row + n ≤ dst) (hspace : dst + n ≤ lim.space) (hzRead : ∀ i < n, μ (src + i) = z i)
    (hcRead : ∀ i < n, μ (row + i) = (coeff i : ℤ)) (hzBound : ∀ i < n, |z i| ≤ (b : ℤ))
    (hcBound : ∀ i < n, coeff i ≤ p) (hword : (word n p b : ℤ) ≤ lim.word) :
    Meets lim P main depth [src, row, dst, n, p] μ (time n p b)
      (fun r ν =>
        r = (((LightNaturalDot.dot coeff (fun i => lifted p (z i)) n) % p : ℕ) : ℤ) ∧ SameOutside μ ν dst n) :=
  by
  have hwDot : ((20 * ((n + 1) * (p + 1) * (p + b + 1) + p + 10) : ℕ) : ℤ) ≤ lim.word := by unfold word at hword; omega
  have hpb : p + b ≤ 20 * ((n + 1) * (p + 1) * (p + b + 1) + p + 10) + 100 :=
    by
    have hh : p + b + 1 ≤ (n + 1) * (p + 1) * (p + b + 1) := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hpbWord : ((p + b : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hpb).trans hword
  have hpWord : (p : ℤ) ≤ lim.word := by omega
  have hbWord : (b : ℤ) ≤ lim.word := by omega
  have h1 : (1 : ℤ) ≤ lim.word := by omega
  have hnat (i : ℕ) (hi : i < n) : 0 ≤ (p : ℤ) + z i := by have hh := (abs_le.mp (hzBound i hi)).1; omega
  have hlift (i : ℕ) (hi : i < n) : (lifted p (z i) : ℤ) = (p : ℤ) + z i := Int.toNat_of_nonneg (hnat i hi)
  have hliftBound (i : ℕ) (hi : i < n) : lifted p (z i) ≤ p + b :=
    by
    have hh := (abs_le.mp (hzBound i hi)).2
    have he := hlift i hi
    omega
  have hmul (i : ℕ) (hi : i < n) : |(1 : ℤ) * μ (src + i)| ≤ lim.word := by
    simpa [hzRead i hi] using (hzBound i hi).trans hbWord
  have hsum (i : ℕ) (hi : i < n) : |(p : ℤ) + (1 : ℤ) * μ (src + i)| ≤ lim.word :=
    by
    rw [hzRead i hi, one_mul, abs_of_nonneg (hnat i hi)]
    have hh := (abs_le.mp (hzBound i hi)).2
    omega
  apply Meets.of_body S.mainBody
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightReportingAffine.meets (d := depth + 1) (src := src) (dst := dst) (n := n) (b := (p : ℤ)) (c := 1)
              S.liftBody hw (by omega) hspace (Or.inr (Or.inl hsrc)) hmul hsum)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightReportingAffine.meets (d := depth + 1) (src := src) (dst := dst) (n := n) (b := (p : ℤ)) (c := 1)
            S.liftBody hw (by omega) hspace (Or.inr (Or.inl hsrc)) hmul hsum)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightReportingAffine.time,
            LightNaturalDot.reducedTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightReportingAffine.time, LightNaturalDot.reducedTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightReportingAffine.time,
            LightNaturalDot.reducedTime] <;>
          omega)
    on_goal -1 => (rintro a ν ⟨liftValues, keep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have coeffValues (i : ℕ) (hi : i < n) : ν (row + i) = (coeff i : ℤ) :=
    (keep _ (Or.inl (by omega))).trans (hcRead i hi)
  have liftedValues (i : ℕ) (hi : i < n) : ν (dst + i) = (lifted p (z i) : ℤ) := by
    rw [liftValues i hi, hzRead i hi, one_mul, hlift i hi]
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightNaturalDot.reduced_meets (depth := depth + 1) S.dotBody S.rawBody S.digitBody S.divideBody ν coeff
              (fun i => lifted p (z i)) hw (by omega) (by omega) hspace coeffValues liftedValues hcBound hliftBound
              hwDot)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightNaturalDot.reduced_meets (depth := depth + 1) S.dotBody S.rawBody S.digitBody S.divideBody ν coeff
            (fun i => lifted p (z i)) hw (by omega) (by omega) hspace coeffValues liftedValues hcBound hliftBound hwDot)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightReportingAffine.time,
            LightNaturalDot.reducedTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightReportingAffine.time, LightNaturalDot.reducedTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightReportingAffine.time,
            LightNaturalDot.reducedTime] <;>
          omega)
    on_goal -1 => (rintro r ξ ⟨hr, hξ⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ξ
  exact ⟨hr, keep⟩
end Procs
end ThreeSum.LightSignedRowHash
