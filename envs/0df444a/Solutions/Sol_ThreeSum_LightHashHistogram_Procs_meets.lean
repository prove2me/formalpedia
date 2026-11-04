-- Prove2me | solution 1 for ThreeSum.LightHashHistogram.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:55.559687+00:00
-- url     : https://prove2.me/submissions/0439e769-fc43-4e22-841a-ca7aa4d5167d

import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightHashHistogram
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_a9326e55c9f5f09c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightResidues_residue_lt
import Theorems.Thm_ThreeSum_LightResidues_residues_meets
import Definitions.Def_WeightedCache3SUM_Alias_2f39c5fb289e3702
set_option autoImplicit false
open ThreeSum ThreeSum.LightHashHistogram
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightHashHistogram
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {L masks raw codes hist n src0 src1 p work U : ℕ}
    (mask w0 w1 : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + L + 2 ≤ lim.depth) (hp : 0 < p)
    (hspace : space work L U ≤ lim.space) (hmasks : masks + n ≤ raw) (hsrc0 : src0 + L ≤ raw) (hsrc1 : src1 + L ≤ raw)
    (hraw : raw + n ≤ codes) (hcodes : codes + n ≤ hist) (hhist : hist + p ≤ work) (hword : (word L p U : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks + i) = (mask i : ℤ)) (hmaskLt : ∀ i < n, mask i < 2 ^ L)
    (hread0 : ∀ i < L, μ (src0 + i) = (w0 i : ℤ)) (hread1 : ∀ i < L, μ (src1 + i) = (w1 i : ℤ))
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    Meets lim P pMain d [L, masks, raw, codes, hist, n, src0, src1, p, work] μ (time L n p U)
      (fun _ μ' =>
        (∀ i < n, μ' (codes + i) = (code L p mask w0 w1 i : ℤ)) ∧
          (∀ r < p, μ' (hist + r) = (LightHistogram.count (code L p mask w0 w1) r n : ℤ)) ∧ Kept μ μ' raw) :=
  by
  have hspow : work + (L + 1) ≤ lim.space := (Nat.add_le_add_left (le_max_left _ _) work).trans hspace
  have hsmod : work + (Nat.log 2 (L * U + 1) + 2) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_right _ _) work).trans hspace
  have hsw : work ≤ lim.space := by omega
  have hhashWord : (LightOneHot.word L U : ℤ) ≤ lim.word :=
    by
    have hh : LightOneHot.word L U ≤ word L p U := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hmodWord : (4 * (L * U : ℕ) + 4 * p + 16 : ℤ) ≤ lim.word :=
    by
    have hh : 4 * (L * U) + 4 * p + 16 ≤ word L p U := by unfold word; omega
    exact (by exact_mod_cast hh : (4 * (L * U : ℕ) + 4 * p + 16 : ℤ) ≤ (word L p U : ℤ)).trans hword
  apply Meets.of_body S.main
  unfold body time
  have hh :=
    LightMaskHashes.meets (d := d + 1) (μ := μ) (L := L) (masks := masks) (dst := raw) (n := n) (src0 := src0) (src1 :=
      src1) (work := work) (U := U) S.hashes S.powers S.onehot mask w0 w1 hw (by omega) hspow hmasks hsrc0 hsrc1
      (by omega) hhashWord hmaskRead hmaskLt hread0 hread1 hbound0 hbound1
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
    | refine _root_.Light.Ends.callToThen (hh _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hh ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightMaskHashes.time, LightOneHot.time,
            LightResidues.residuesTime, LightResidues.residueBudget, LightHistogram.histogramTime,
            LightHistogram.countTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightMaskHashes.time, LightOneHot.time, LightResidues.residuesTime, LightResidues.residueBudget,
              LightHistogram.histogramTime, LightHistogram.countTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskHashes.time, LightOneHot.time,
            LightResidues.residuesTime, LightResidues.residueBudget, LightHistogram.histogramTime,
            LightHistogram.countTime] <;> omega)
    on_goal -1 => (rintro v μ₁ ⟨rawValues, _, kept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hrawBound : ∀ i < n, |μ₁ (raw + i)| ≤ ((L * U : ℕ) : ℤ) :=
    by
    intro i hi
    rw [rawValues i hi, abs_of_nonneg (Int.natCast_nonneg _)]
    exact Int.ofNat_le.mpr (OneHotMask.eval_le (m := mask i) hbound0 hbound1)
  have hr :=
    LightResidues.residues_meets (d := d + 1) (μ := μ₁) (src := raw) (dst := codes) (n := n) (p := p) (work := work)
      (U := L * U) (c := 1) S.residues S.emod hw (by omega) hp (by omega) (by omega) hsmod (Or.inl hraw) (by norm_num)
      hmodWord hrawBound
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
    | refine _root_.Light.Ends.callToThen (hr _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hr ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightMaskHashes.time, LightOneHot.time,
            LightResidues.residuesTime, LightResidues.residueBudget, LightHistogram.histogramTime,
            LightHistogram.countTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightMaskHashes.time, LightOneHot.time, LightResidues.residuesTime, LightResidues.residueBudget,
              LightHistogram.histogramTime, LightHistogram.countTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskHashes.time, LightOneHot.time,
            LightResidues.residuesTime, LightResidues.residueBudget, LightHistogram.histogramTime,
            LightHistogram.countTime] <;> omega)
    on_goal -1 => (rintro v μ₂ ⟨residueValues, kept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcodeValues : ∀ i < n, μ₂ (codes + i) = (code L p mask w0 w1 i : ℤ) :=
    by
    intro i hi
    rw [residueValues i hi, rawValues i hi]
    rfl
  have hcodeLt : ∀ i < n, code L p mask w0 w1 i < p := by
    intro i hi
    exact LightResidues.residue_lt hp 1 _
  have hh :=
    LightHistogram.histogram_meets (d := d + 1) (μ := μ₂) (src := codes) (dst := hist) (n := n) (p := p) S.hist S.fill
      (code L p mask w0 w1) hw (by omega) (by omega) (by omega) (Or.inl hcodes) hcodeValues hcodeLt
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
    | refine _root_.Light.Ends.callToThen (hh _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hh ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightMaskHashes.time, LightOneHot.time,
            LightResidues.residuesTime, LightResidues.residueBudget, LightHistogram.histogramTime,
            LightHistogram.countTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightMaskHashes.time, LightOneHot.time, LightResidues.residuesTime, LightResidues.residueBudget,
              LightHistogram.histogramTime, LightHistogram.countTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskHashes.time, LightOneHot.time,
            LightResidues.residuesTime, LightResidues.residueBudget, LightHistogram.histogramTime,
            LightHistogram.countTime] <;> omega)
    on_goal -1 => (rintro v μ₃ ⟨counts, kept₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨?_, counts, ?_⟩
  · intro i hi
    change μ₃ (codes + i) = _
    rw [kept₃ _ (Or.inl (by omega))]
    exact hcodeValues i hi
  · intro a ha
    change μ₃ a = μ a
    rw [kept₃ _ (Or.inl (by omega)), kept₂ _ ⟨by omega, Or.inl (by omega)⟩]
    exact kept₁ a ⟨by omega, Or.inl ha⟩
end Procs
end ThreeSum.LightHashHistogram
