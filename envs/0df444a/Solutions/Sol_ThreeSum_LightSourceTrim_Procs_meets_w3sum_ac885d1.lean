-- Prove2me | solution 1 for ThreeSum.LightSourceTrim.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:23.217944+00:00
-- url     : https://prove2.me/submissions/2b76aa5e-200e-4f27-ac8c-ee08989923e0

import Definitions.Def_Submission_ThreeSum_LightSourceRowFlag
import Definitions.Def_Submission_ThreeSum_SourceFlagProduct
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Theorems.Thm_ThreeSum_LightSourceTrim_rowFlag_le
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Meets_of_body
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
import Definitions.Def_WeightedCache3SUM_Alias_8f9b8fc511f535d5
import Definitions.Def_WeightedCache3SUM_Alias_e80b8f80e26e0eba
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_zero
import Theorems.Thm_ThreeSum_LightSourceRowScan_hash_zero
import Definitions.Def_WeightedCache3SUM_Alias_d4ec36c7dcd9fa6e
import Theorems.Thm_ThreeSum_SourceFlagProduct_product_le
import Theorems.Thm_ThreeSum_SourceFlagProduct_product_succ
import Theorems.Thm_ThreeSum_SourceFlagProduct_product_zero
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
attribute [local simp] ThreeSum.LightSourceRowScan.count_zero
attribute [local simp] ThreeSum.LightSourceRowScan.hash_zero
attribute [local simp] ThreeSum.SourceFlagProduct.product_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceTrim
open Light SourceFlagProduct
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceTrim
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ}
    {J L h p cap occ maps candidates histL histR bitBase rowOut work dst U V M K : ℕ} (sel candidate bits : ℕ → ℕ)
    (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) (hp : 0 < p)
    (hh : h ≤ L) (hocc : occ + J ≤ rowOut) (hmaps : maps + 2 * L * M ≤ rowOut) (hcandidates : candidates + M ≤ rowOut)
    (hleft : histL + K * p ≤ rowOut) (hright : histR + K * p ≤ rowOut) (hbits : bitBase + J * L ≤ rowOut)
    (hrowOut : rowOut + 2 ≤ work) (hdst : dst + 2 ≤ rowOut) (hspace : LightSourceRowFlag.space work L U ≤ lim.space)
    (hword : (LightSourceRowFlag.word L p U V cap : ℤ) ≤ lim.word) (hsel : ∀ j < J, sel j < M)
    (hcandidate : ∀ s < M, candidate s < K) (hoccRead : ∀ j < J, μ (occ + j) = (sel j : ℤ))
    (hcandidateRead : ∀ s < M, μ (candidates + s) = (candidate s : ℤ))
    (hbitsRead : ∀ i < J * L, μ (bitBase + i) = (bits i : ℤ)) (hbitBound : ∀ i < J * L, bits i ≤ 1)
    (hread0 : ∀ s < M, ∀ a < L, μ (maps + 2 * L * s + a) = (w0 s a : ℤ))
    (hread1 : ∀ s < M, ∀ a < L, μ (maps + 2 * L * s + L + a) = (w1 s a : ℤ)) (hbound0 : ∀ s < M, ∀ a < L, w0 s a ≤ U)
    (hbound1 : ∀ s < M, ∀ a < L, w1 s a ≤ U) (hcountL : ∀ k < K, ∀ r < p, μ (histL + k * p + r) = (leftCount k r : ℤ))
    (hcountR : ∀ k < K, ∀ r < p, μ (histR + k * p + r) = (rightCount k r : ℤ))
    (hcountBoundL : ∀ k < K, ∀ r < p, leftCount k r ≤ V) (hcountBoundR : ∀ k < K, ∀ r < p, rightCount k r ≤ V) :
    Meets lim P pMain d [J, L, h, p, cap, occ, maps, candidates, histL, histR, bitBase, rowOut, work, dst] μ
      (time J L U)
      (fun _ ν =>
        ν dst = (product (rowFlag L h p cap sel candidate bits w0 w1 leftCount) J : ℤ) ∧
          ν (dst + 1) = (product (rowFlag L h p cap sel candidate bits w1 w0 rightCount) J : ℤ) ∧
            KeptBut μ ν rowOut dst 2) :=
  by
  have hspace' : work + 3 + (Nat.log 2 (L * U + 1) + 2) ≤ lim.space := hspace
  have h1 : (1 : ℤ) ≤ lim.word :=
    by
    have hh : 1 ≤ LightSourceRowFlag.word L p U V cap :=
      by
      unfold LightSourceRowFlag.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hleftFlag (j : ℕ) : rowFlag L h p cap sel candidate bits w0 w1 leftCount j ≤ 1 := rowFlag_le ..
  have hrightFlag (j : ℕ) : rowFlag L h p cap sel candidate bits w1 w0 rightCount j ≤ 1 := rowFlag_le ..
  have hleftPrefix (j : ℕ) : product (rowFlag L h p cap sel candidate bits w0 w1 leftCount) j ≤ 1 :=
    product_le _ (n := j) (fun i _ => hleftFlag i) le_rfl
  have hrightPrefix (j : ℕ) : product (rowFlag L h p cap sel candidate bits w1 w0 rightCount) j ≤ 1 :=
    product_le _ (n := j) (fun i _ => hrightFlag i) le_rfl
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
    refine _root_.Light.Ends.setToThen 1 ?_ ?_ ?_
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
    refine _root_.Light.Ends.setToThen 1 ?_ ?_ ?_
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
  refine
    Ends.pieceThen
      (Ends.for
        (Inv μ J L h p cap occ maps candidates histL histR bitBase rowOut work dst sel candidate bits w0 w1 leftCount
          rightCount)
        J (LightSourceRowFlag.time L U + 242) ?start ?round ?done ?bound (Q :=
        Inv μ J L h p cap occ maps candidates histL histR bitBase rowOut work dst sel candidate bits w0 w1 leftCount
          rightCount J)
        (T := J * (LightSourceRowFlag.time L U + 250) + 6) (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;> first
              | omega
              | (ring_nf; omega))))
      ?finish
  case start =>
    refine ⟨0, μ, ?_, fun _ _ => rfl⟩
    simp only [product_zero]
    exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
  case round =>
    rintro j _ hj _ ⟨r, ν, rfl, kept⟩
    have hs := hsel j hj
    have hk := hcandidate (sel j) hs
    have hocc' : ν (occ + j) = (sel j : ℤ) := (kept _ (by omega)).trans (hoccRead j hj)
    have hcan' : ν (candidates + sel j) = (candidate (sel j) : ℤ) :=
      (kept _ (by omega)).trans (hcandidateRead (sel j) hs)
    have hbEnd : j * L + L ≤ J * L :=
      by
      have hh := Nat.mul_le_mul_right L (show j + 1 ≤ J by omega)
      simpa only [Nat.succ_mul] using hh
    have hmEnd : 2 * L * sel j + L + L ≤ 2 * L * M :=
      by
      have hh := Nat.mul_le_mul_left (2 * L) (show sel j + 1 ≤ M by omega)
      nlinarith
    have htEnd : candidate (sel j) * p + p ≤ K * p :=
      by
      have hh := Nat.mul_le_mul_right p (show candidate (sel j) + 1 ≤ K by omega)
      simpa only [Nat.succ_mul] using hh
    have hdoubleNonneg : (0 : ℤ) ≤ 2 * (L : ℤ) := by positivity
    have hdoubleWord : 2 * (L : ℤ) ≤ lim.word :=
      by
      have hm : 2 * L ≤ 2 * L * M := Nat.le_mul_of_pos_right _ (by omega)
      exact (by exact_mod_cast (show 2 * L ≤ lim.space by omega) : 2 * (L : ℤ) ≤ lim.space).trans hw
    have hmapNonneg : (0 : ℤ) ≤ 2 * (L : ℤ) * (sel j : ℤ) := by positivity
    have hmapWord : 2 * (L : ℤ) * (sel j : ℤ) ≤ lim.word := by
      exact
        (by exact_mod_cast (show 2 * L * sel j ≤ lim.space by omega) : 2 * (L : ℤ) * (sel j : ℤ) ≤ lim.space).trans hw
    have hmapEndZ : (maps : ℤ) + 2 * (L : ℤ) * (sel j : ℤ) + (L : ℤ) + (L : ℤ) ≤ rowOut := by
      exact_mod_cast (show maps + 2 * L * sel j + L + L ≤ rowOut by omega)
    have hbRead : ∀ a < L, ν (bitBase + j * L + a) = (bits (j * L + a) : ℤ) :=
      by
      intro a ha
      exact (kept _ (by omega)).trans (by simpa only [Nat.add_assoc] using hbitsRead (j * L + a) (by omega))
    have hw0 : ∀ a < L, ν (maps + 2 * L * sel j + a) = (w0 (sel j) a : ℤ) :=
      by
      intro a ha
      exact (kept _ (by omega)).trans (hread0 (sel j) hs a ha)
    have hw1 : ∀ a < L, ν (maps + 2 * L * sel j + L + a) = (w1 (sel j) a : ℤ) :=
      by
      intro a ha
      exact (kept _ (by omega)).trans (hread1 (sel j) hs a ha)
    have hcL : ∀ r < p, ν (histL + candidate (sel j) * p + r) = (leftCount (candidate (sel j)) r : ℤ) :=
      by
      intro r hr
      exact (kept _ (by omega)).trans (hcountL _ hk r hr)
    have hcR : ∀ r < p, ν (histR + candidate (sel j) * p + r) = (rightCount (candidate (sel j)) r : ℤ) :=
      by
      intro r hr
      exact (kept _ (by omega)).trans (hcountR _ hk r hr)
    have hrow :=
      LightSourceRowFlag.meets (d := d + 1) (μ := ν) (src := bitBase + j * L) (src0 := maps + 2 * L * sel j) (src1 :=
        maps + 2 * L * sel j + L) (L := L) (h := h) (histL := histL + candidate (sel j) * p) (histR :=
        histR + candidate (sel j) * p) (p := p) (cap := cap) (dst := rowOut) (work := work) (U := U) (V := V)
        S.rowFlagDef S.row S.emod S.flag (fun a => bits (j * L + a)) (w0 (sel j)) (w1 (sel j))
        (leftCount (candidate (sel j))) (rightCount (candidate (sel j))) hw (by omega) hp hh (by omega) (by omega)
        (by omega) (by omega) (by omega) hrowOut hspace hword hbRead hw0 hw1
        (fun a ha => hbitBound (j * L + a) (by omega)) (hbound0 (sel j) hs) (hbound1 (sel j) hs) hcL hcR
        (hcountBoundL _ hk) (hcountBoundR _ hk)
    unfold roundBody
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
      | refine _root_.Light.Ends.callToThen (hrow _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hrow ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hocc', hcan',
              LightSourceRowFlag.time, LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hocc', hcan', LightSourceRowFlag.time, LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hocc', hcan', LightSourceRowFlag.time,
              LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time] <;> omega)
      on_goal -1 => (rintro q ν₁ ⟨leftRead, rightRead, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hlRead : ν₁ rowOut = (rowFlag L h p cap sel candidate bits w0 w1 leftCount j : ℤ) := leftRead
    have hrRead : ν₁ (rowOut + 1) = (rowFlag L h p cap sel candidate bits w1 w0 rightCount j : ℤ) := rightRead
    have hlB := hleftPrefix (j + 1)
    have hrB := hrightPrefix (j + 1)
    have hlCast :
      (product (rowFlag L h p cap sel candidate bits w0 w1 leftCount) j : ℤ) *
          (rowFlag L h p cap sel candidate bits w0 w1 leftCount j : ℤ) =
        (product (rowFlag L h p cap sel candidate bits w0 w1 leftCount) (j + 1) : ℤ) :=
      by rw [product_succ, Nat.cast_mul]
    have hrCast :
      (product (rowFlag L h p cap sel candidate bits w1 w0 rightCount) j : ℤ) *
          (rowFlag L h p cap sel candidate bits w1 w0 rightCount j : ℤ) =
        (product (rowFlag L h p cap sel candidate bits w1 w0 rightCount) (j + 1) : ℤ) :=
      by rw [product_succ, Nat.cast_mul]
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine
        _root_.Light.Ends.setToThen (product (rowFlag L h p cap sel candidate bits w0 w1 leftCount) (j + 1) : ℕ) ?_ ?_
          ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlRead, hlCast,
              LightSourceRowFlag.time, LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hlRead, hlCast, LightSourceRowFlag.time, LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlRead, hlCast, LightSourceRowFlag.time,
              LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time] <;> omega)
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
      refine
        _root_.Light.Ends.setToThen (product (rowFlag L h p cap sel candidate bits w1 w0 rightCount) (j + 1) : ℕ) ?_ ?_
          ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrRead, hrCast,
              LightSourceRowFlag.time, LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hrRead, hrCast, LightSourceRowFlag.time, LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrRead, hrCast, LightSourceRowFlag.time,
              LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, q, ν₁, by simp [update_frame_setLocal], ?_⟩
    intro a ha
    exact (hkeep a ⟨by omega, Or.inl ha⟩).trans (kept a ha)
  case done =>
    intro σ hj hshape
    exact hshape
  case bound =>
    rintro j _ hj _ ⟨r, ν, rfl, _⟩
    simp
  case finish =>
    rintro _ ⟨r, ν, rfl, kept⟩
    have hl := hleftPrefix J
    have hr := hrightPrefix J
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine
        _root_.Light.Ends.storeToThen dst (product (rowFlag L h p cap sel candidate bits w0 w1 leftCount) J : ℕ) ?_ ?_
          ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
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
      refine
        _root_.Light.Ends.storeToThen (dst + 1) (product (rowFlag L h p cap sel candidate bits w1 w0 rightCount) J : ℕ)
          ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
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
    refine ⟨by simp, by simp, ?_⟩
    intro a ⟨ha, hout⟩
    simp only [Function.update_of_ne (show a ≠ dst + 1 by omega), Function.update_of_ne (show a ≠ dst by omega)]
    exact kept a ha
end Procs
end ThreeSum.LightSourceTrim
