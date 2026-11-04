-- Prove2me | solution 1 for ThreeSum.LightBlockSourceHashes.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:38.099209+00:00
-- url     : https://prove2.me/submissions/02c8b0a2-ac53-42bf-bef1-95fcf8c242eb

import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_ThreeSum_BlockCoefficientRows_flat_le
import Definitions.Def_WeightedCache3SUM_Alias_87e5dc3b34337b28
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Theorems.Thm_ThreeSum_LightBlockCoefficients_row_end_le
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceHashes
open Light BlockCoefficientRows
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBlockSourceHashes
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ}
    {J L p occ maps coeff0 coeff1 masks rawLeft rawRight n work U M : ℕ} (sel mask : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p) (hd : d + J * L + 2 ≤ lim.depth)
    (hspace : space work J L ≤ lim.space) (hocc : occ + J ≤ coeff0) (hmaps : maps + 2 * L * M ≤ coeff0)
    (hmasks : masks + n ≤ coeff0) (hc0 : coeff0 + J * L ≤ coeff1) (hc1 : coeff1 + J * L ≤ rawLeft)
    (hleft : rawLeft + n ≤ rawRight) (hright : rawRight + n ≤ work) (hword : (word J L p U : ℤ) ≤ lim.word)
    (hsel : ∀ j < J, sel j < M) (hselRead : ∀ j < J, μ (occ + j) = (sel j : ℤ))
    (hread0 : ∀ s < M, ∀ i < L, μ (maps + 2 * L * s + i) = (w0 s i : ℤ))
    (hread1 : ∀ s < M, ∀ i < L, μ (maps + 2 * L * s + L + i) = (w1 s i : ℤ)) (hbound0 : ∀ s < M, ∀ i < L, w0 s i ≤ U)
    (hbound1 : ∀ s < M, ∀ i < L, w1 s i ≤ U) (hmaskRead : ∀ i < n, μ (masks + i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2 ^ (J * L)) :
    Meets lim P pMain d [J, L, p, occ, maps, coeff0, coeff1, masks, rawLeft, rawRight, n, work] μ (time J L n)
      (fun _ ν =>
        (∀ i < n, ν (rawLeft + i) = (OneHotMask.eval (flat J L p sel w0) (flat J L p sel w1) (J * L) (mask i) : ℤ)) ∧
          (∀ i < n, ν (rawRight + i) = (OneHotMask.eval (flat J L p sel w1) (flat J L p sel w0) (J * L) (mask i) : ℤ)) ∧
            LightBlockCoefficients.Rows ν coeff0 coeff1 L p sel w0 w1 J ∧ Kept μ ν coeff0) :=
  by
  have hsc : work + (J + 1) ≤ lim.space := (Nat.add_le_add_left (le_max_left _ _) work).trans hspace
  have hsh : work + (J * L + 1) ≤ lim.space := (Nat.add_le_add_left (le_max_right _ _) work).trans hspace
  have hcw : (LightBlockCoefficients.word J p U : ℤ) ≤ lim.word :=
    by
    have hh : LightBlockCoefficients.word J p U ≤ word J L p U := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hhw : (LightOneHot.word (J * L) (p ^ J * U) : ℤ) ≤ lim.word :=
    by
    have hh : LightOneHot.word (J * L) (p ^ J * U) ≤ word J L p U := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwidth : (J : ℤ) * (L : ℤ) ≤ lim.word :=
    by
    have hh : J * L ≤ lim.space := by omega
    exact (by exact_mod_cast hh : (J : ℤ) * (L : ℤ) ≤ lim.space).trans hw
  have hb0 : ∀ i < J * L, flat J L p sel w0 i ≤ p ^ J * U := fun _ hi => flat_le hp hsel hbound0 hi
  have hb1 : ∀ i < J * L, flat J L p sel w1 i ≤ p ^ J * U := fun _ hi => flat_le hp hsel hbound1 hi
  apply Meets.of_body S.main
  unfold body time
  have hc :=
    LightBlockCoefficients.meets (d := d + 1) (μ := μ) (J := J) (L := L) (p := p) (occ := occ) (maps := maps) (dst0 :=
      coeff0) (dst1 := coeff1) (work := work) (U := U) (M := M) S.coefficients S.powers S.scale sel w0 w1 hw hp hocc
      hmaps hc0 (by omega) hsc hcw (by omega) hsel hselRead hread0 hread1 hbound0 hbound1
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
    | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBlockCoefficients.time,
            LightBlockCoefficients.roundTime, LightMaskHashes.time, LightOneHot.time, LightScaleArray.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBlockCoefficients.time, LightBlockCoefficients.roundTime, LightMaskHashes.time, LightOneHot.time,
              LightScaleArray.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBlockCoefficients.time,
            LightBlockCoefficients.roundTime, LightMaskHashes.time, LightOneHot.time, LightScaleArray.time] <;>
          omega)
    on_goal -1 => (rintro r μ₁ ⟨rows, kept₁, _⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  obtain ⟨rows0, rows1⟩ := rows_flat rows
  have masks₁ : ∀ i < n, μ₁ (masks + i) = (mask i : ℤ) :=
    by
    intro i hi
    exact (kept₁ _ (by omega)).trans (hmaskRead i hi)
  have hl :=
    LightMaskHashes.meets (d := d + 1) (μ := μ₁) (L := J * L) (masks := masks) (dst := rawLeft) (n := n) (src0 :=
      coeff0) (src1 := coeff1) (work := work) (U := p ^ J * U) S.hashes S.powers S.onehot mask (flat J L p sel w0)
      (flat J L p sel w1) hw (by omega) hsh (by omega) (by omega) hc1 (by omega) hhw masks₁ hmaskLt rows0 rows1 hb0 hb1
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
    | refine _root_.Light.Ends.callToThen (hl _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hl ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBlockCoefficients.time,
            LightBlockCoefficients.roundTime, LightMaskHashes.time, LightOneHot.time, LightScaleArray.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBlockCoefficients.time, LightBlockCoefficients.roundTime, LightMaskHashes.time, LightOneHot.time,
              LightScaleArray.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBlockCoefficients.time,
            LightBlockCoefficients.roundTime, LightMaskHashes.time, LightOneHot.time, LightScaleArray.time] <;>
          omega)
    on_goal -1 => (rintro r μ₂ ⟨leftValues, _, kept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have masks₂ : ∀ i < n, μ₂ (masks + i) = (mask i : ℤ) :=
    by
    intro i hi
    exact (kept₂ _ ⟨by omega, Or.inl (by omega)⟩).trans (masks₁ i hi)
  have rows0₂ : ∀ i < J * L, μ₂ (coeff0 + i) = (flat J L p sel w0 i : ℤ) :=
    by
    intro i hi
    exact (kept₂ _ ⟨by omega, Or.inl (by omega)⟩).trans (rows0 i hi)
  have rows1₂ : ∀ i < J * L, μ₂ (coeff1 + i) = (flat J L p sel w1 i : ℤ) :=
    by
    intro i hi
    exact (kept₂ _ ⟨by omega, Or.inl (by omega)⟩).trans (rows1 i hi)
  have hr :=
    LightMaskHashes.meets (d := d + 1) (μ := μ₂) (L := J * L) (masks := masks) (dst := rawRight) (n := n) (src0 :=
      coeff1) (src1 := coeff0) (work := work) (U := p ^ J * U) S.hashes S.powers S.onehot mask (flat J L p sel w1)
      (flat J L p sel w0) hw (by omega) hsh (by omega) (by omega) (by omega) hright hhw masks₂ hmaskLt rows1₂ rows0₂ hb1
      hb0
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
    | refine _root_.Light.Ends.callToThen (hr _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hr ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBlockCoefficients.time,
            LightBlockCoefficients.roundTime, LightMaskHashes.time, LightOneHot.time, LightScaleArray.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBlockCoefficients.time, LightBlockCoefficients.roundTime, LightMaskHashes.time, LightOneHot.time,
              LightScaleArray.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBlockCoefficients.time,
            LightBlockCoefficients.roundTime, LightMaskHashes.time, LightOneHot.time, LightScaleArray.time] <;>
          omega)
    on_goal -1 => (rintro r μ₃ ⟨rightValues, _, kept₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨?_, rightValues, ?_, ?_⟩
  · intro i hi
    exact (kept₃ _ ⟨by omega, Or.inl (by omega)⟩).trans (leftValues i hi)
  · intro a ha i hi
    have he := LightBlockCoefficients.row_end_le (L := L) ha
    constructor
    ·
      exact
        (kept₃ _ ⟨by omega, Or.inl (by omega)⟩).trans ((kept₂ _ ⟨by omega, Or.inl (by omega)⟩).trans (rows a ha i hi).1)
    ·
      exact
        (kept₃ _ ⟨by omega, Or.inl (by omega)⟩).trans ((kept₂ _ ⟨by omega, Or.inl (by omega)⟩).trans (rows a ha i hi).2)
  · intro a ha
    exact (kept₃ _ ⟨by omega, Or.inl (by omega)⟩).trans ((kept₂ _ ⟨by omega, Or.inl (by omega)⟩).trans (kept₁ a ha))
end Procs
end ThreeSum.LightBlockSourceHashes
