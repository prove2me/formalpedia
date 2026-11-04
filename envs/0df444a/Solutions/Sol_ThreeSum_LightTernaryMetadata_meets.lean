-- Prove2me | solution 1 for ThreeSum.LightTernaryMetadata.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:35.050871+00:00
-- url     : https://prove2.me/submissions/204df7d9-2188-42fb-9c7b-1d328e6c60df

import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Theorems.Thm_ThreeSum_LightTernaryMetadata_writeRecord_current
import Theorems.Thm_ThreeSum_LightTernaryMetadata_writeRecord_before
import Theorems.Thm_ThreeSum_LightTernaryMetadata_writeRecord_kept
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryCodes_digit_le_two
import Theorems.Thm_ThreeSum_LightTernaryCodes_digit_meets
import Theorems.Thm_ThreeSum_LightTernaryCodes_zero_meets
import Definitions.Def_WeightedCache3SUM_Alias_88b09a412b2c33a9
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryMetadata
theorem _root_.solution {pMain pZero pDigit pErase W low high a n powers base d : ℕ}
    (hmain : P[pMain]? = some (body pZero pDigit pErase)) (hzero : P[pZero]? = some (LightTernaryCodes.zeroBody pErase))
    (hdigit : P[pDigit]? = some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase)) (μ : ℕ → ℤ) (codes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + n ≤ base) (hb : base + 4 * n ≤ powers)
    (hspace : powers + (W + 1) ≤ lim.space) (hword : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (a + j) = (codes j : ℤ)) (hpowers : Powers μ powers W) (hcodes : ∀ j < n, codes j < 2 ^ W)
    (hlow : low ≤ W) (hhigh : high ≤ W) (hd : d + W + 2 ≤ lim.depth) :
    Meets lim P pMain d [W, low, high, a, n, powers, base] μ (time W n)
      (fun _ μ' => (∀ j < n, RecordAt μ' base n j W low high (codes j)) ∧ SameOutside μ μ' base (4 * n)) :=
  by
  have htwo : 2 ≤ lim.word :=
    by
    have h : 2 ^ 1 ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast h : (2 : ℤ) ≤ ((2 ^ (W + 1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv μ W low high a n powers base codes) n (roundTime W) ?start ?round ?done ?bound (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, 0, 0, 0, μ, ?_, SameOn.refl, ?_⟩
    · simp [update_frame_setLocal]
      change
        frame [(W : ℤ), low, high, a, n, powers, base, 0] =
          frame ([(W : ℤ), low, high, a, n, powers, base, 0] ++ [0, 0, 0, 0])
      exact (frame_append_zeros _ 4).symm
    · intro k hk
      omega
  case round =>
    rintro j _ hj _ ⟨m, z0, z1, q, μ', rfl, hkeep, hrows⟩
    have hreadj : μ' (a + j) = (codes j : ℤ) := (hkeep _ (Or.inl (by omega))).trans (hread j hj)
    have hp : Powers μ' powers W := by
      intro k hk
      rw [hkeep _ (Or.inr (by omega)), hpowers k hk]
    have hm := hcodes j hj
    have hmword : (codes j : ℤ) < lim.word :=
      by
      have hpow : 2 ^ W ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      exact (Int.ofNat_lt.mpr hm).trans_le ((Int.ofNat_le.mpr hpow).trans hword)
    have hzc := LightTernaryCodes.zero_meets (d := d + 1) hzero herase μ' hw hspace hword hp hlow hhigh hm (by omega)
    have hoc := LightMaskErase.meets herase μ' hw hspace hword hp W high (codes j) le_rfl hhigh hm (d + 1) (by omega)
    have hdc :=
      LightTernaryCodes.digit_meets (d := d + 1) hdigit herase μ' hw hspace hword hp hlow hhigh hm (by omega) htwo
    have hzle := eraseMask_le (a := low) ((eraseMask_le (a := high) hm).trans_lt hm)
    have hole := eraseMask_le (a := high) hm
    have hdle := LightTernaryCodes.digit_le_two W low high (codes j)
    unfold roundBody roundTime
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (codes j : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadj,
              LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime, LightMaskErase.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hreadj, LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime, LightMaskErase.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadj, LightTernaryCodes.zeroTime,
              LightTernaryCodes.digitTime, LightMaskErase.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
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
      | refine _root_.Light.Ends.callToThen (hzc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hzc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime, LightMaskErase.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime, LightMaskErase.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryCodes.zeroTime,
              LightTernaryCodes.digitTime, LightMaskErase.time] <;>
            omega)
      on_goal -1 => (rintro zr μ0 ⟨hzr, hm0⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst μ0
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
      | refine _root_.Light.Ends.callToThen (hoc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hoc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime, LightMaskErase.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime, LightMaskErase.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryCodes.zeroTime,
              LightTernaryCodes.digitTime, LightMaskErase.time] <;>
            omega)
      on_goal -1 => (rintro one μ1 ⟨hor, hm1⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst μ1
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
      | refine _root_.Light.Ends.callToThen (hdc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hdc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime, LightMaskErase.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime, LightMaskErase.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryCodes.zeroTime,
              LightTernaryCodes.digitTime, LightMaskErase.time] <;>
            omega)
      on_goal -1 => (rintro dr μ2 ⟨hdr, hm2⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst μ2
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (base + j) (LightTernaryCodes.digit W low high (codes j) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hdr,
              LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime, LightMaskErase.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hdr, LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime, LightMaskErase.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdr, LightTernaryCodes.zeroTime,
              LightTernaryCodes.digitTime, LightMaskErase.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (base + n + j) (LightTernaryCodes.zeroCode W low high (codes j) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hzr,
              LightTernaryCodes.zeroCode, LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime, LightMaskErase.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hzr, LightTernaryCodes.zeroCode, LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime,
                LightMaskErase.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hzr, LightTernaryCodes.zeroCode,
              LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime, LightMaskErase.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (base + 2 * n + j) (LightTernaryCodes.oneCode W high (codes j) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hor,
              LightTernaryCodes.oneCode, LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime, LightMaskErase.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hor, LightTernaryCodes.oneCode, LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime,
                LightMaskErase.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hor, LightTernaryCodes.oneCode,
              LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime, LightMaskErase.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (base + 3 * n + j) (codes j : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime, LightMaskErase.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightTernaryCodes.zeroTime, LightTernaryCodes.digitTime, LightMaskErase.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryCodes.zeroTime,
              LightTernaryCodes.digitTime, LightMaskErase.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    let μ'' :=
      writeRecord μ' base n j (LightTernaryCodes.digit W low high (codes j))
        (LightTernaryCodes.zeroCode W low high (codes j)) (LightTernaryCodes.oneCode W high (codes j)) (codes j)
    refine ⟨by simp, (codes j : ℤ), zr, one, dr, μ'', ?_, ?_, ?_⟩
    · simp [update_frame_setLocal, μ'', writeRecord]
    · intro x hx
      exact (writeRecord_kept hj x hx).trans (hkeep x hx)
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact writeRecord_before hk hj (hrows k hk)
      · exact writeRecord_current hj
  case done =>
    rintro _ _ ⟨m, z0, z1, q, μ', rfl, hkeep, hrows⟩
    exact ⟨hrows, hkeep⟩
  case bound =>
    rintro j _ hj _ ⟨m, z0, z1, q, μ', rfl, hkeep, hrows⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightTernaryMetadata
