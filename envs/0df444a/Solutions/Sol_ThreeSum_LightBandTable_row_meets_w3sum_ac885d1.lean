-- Prove2me | solution 1 for ThreeSum.LightBandTable.row_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:29:28.813114+00:00
-- url     : https://prove2.me/submissions/b33cc1db-5194-4a80-88ff-1529e8d8b8a3

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightBandTable
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_Light_wrote_rest
import Theorems.Thm_Light_wrote_succ
import Theorems.Thm_Light_wrote_zero
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
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
open ThreeSum ThreeSum.LightBandTable
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandTable
theorem _root_.solution {pRow pLookup pSearch b loBase hiBase n m dst powers W d U : ℕ} {x s : ℤ}
    (hrow : P[pRow]? = some (rowBody pLookup)) (hlookup : P[pLookup]? = some (LightBandLookup.body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch)) (μ : ℕ → ℤ) (f lo hi : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hb : b + n ≤ dst) (hlo : loBase + m ≤ dst) (hhi : hiBase + m ≤ dst)
    (hdst : dst + n ≤ powers) (hspace : powers + (W + 1) ≤ lim.space)
    (hword : ((m + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word) (hqueryWord : 2 * (U : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (b + j) = f j) (hreadLo : ∀ j < m, μ (loBase + j) = lo j)
    (hreadHi : ∀ j < m, μ (hiBase + j) = hi j) (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i ≤ j → j < m → lo i ≤ lo j) (hm : m < 2 ^ W) (hs : |s| ≤ 1) (hx : |x| ≤ U)
    (hf : ∀ j < n, |f j| ≤ U) (hd : d + W + 2 ≤ lim.depth) :
    Meets lim P pRow d [x, b, loBase, hiBase, n, m, dst, powers, W, s] μ (rowTime n W)
      (fun _ μ' => (∀ j < n, μ' (dst + j) = (rowValue lo hi m x s f j : ℤ)) ∧ SameOutside μ μ' dst n) :=
  by
  let F := fun j => (rowValue lo hi m x s f j : ℤ)
  have hsx : |s * x| ≤ (U : ℤ) := by
    rw [abs_mul]
    exact (mul_le_mul hs hx (abs_nonneg _) (by omega)).trans (by simp)
  have hsxBounds := abs_le.mp hsx
  have hquery (j : ℕ) (hj : j < n) : |s * x + f j| ≤ 2 * (U : ℤ) := by
    exact (abs_add_le _ _).trans (by have := hf j hj; omega)
  apply Meets.of_body hrow
  unfold rowBody rowTime
  refine
    Ends.for (fun j σ => ∃ r : ℤ, σ = ⟨frame [x, b, loBase, hiBase, n, m, dst, powers, W, s, j, r], wrote μ dst F j⟩) n
      (LightBandLookup.time W + 52) ?start ?round ?done ?bound
  case start =>
    refine ⟨0, ?_⟩
    simp [update_frame_setLocal, wrote_zero]
    simpa using (frame_append_zeros [x, b, loBase, hiBase, n, m, dst, powers, W, s, 0] 1).symm
  case round =>
    rintro j _ hj _ ⟨r, rfl⟩
    have hread' : ∀ k < n, wrote μ dst F j (b + k) = f k :=
      by
      intro k hk
      rw [wrote_rest (by omega)]
      exact hread k hk
    have hlo' : ∀ k < m, wrote μ dst F j (loBase + k) = lo k :=
      by
      intro k hk
      rw [wrote_rest (by omega)]
      exact hreadLo k hk
    have hhi' : ∀ k < m, wrote μ dst F j (hiBase + k) = hi k :=
      by
      intro k hk
      rw [wrote_rest (by omega)]
      exact hreadHi k hk
    have hpowers' : Powers (wrote μ dst F j) powers W :=
      by
      intro k hk
      rw [wrote_rest (by omega)]
      exact hpowers k hk
    have hr := hread' j hj
    have hfBounds := abs_le.mp (hf j hj)
    have hqueryBounds := abs_le.mp (hquery j hj)
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
            ((LightBandLookup.meets (d := d + 1) (L := W) (x := s * x + f j) hlookup hsearch (wrote μ dst F j) lo hi hw
                (by omega) (by omega) hspace hword hlo' hhi' hpowers' hsorted le_rfl hm (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (LightBandLookup.meets (d := d + 1) (L := W) (x := s * x + f j) hlookup hsearch (wrote μ dst F j) lo hi hw
              (by omega) (by omega) hspace hword hlo' hhi' hpowers' hsorted le_rfl hm (by omega))
            ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr,
              LightBandLookup.time, LightBandLookup.searchTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hr, LightBandLookup.time, LightBandLookup.searchTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, LightBandLookup.time,
              LightBandLookup.searchTime] <;>
            omega)
      on_goal -1 => (rintro result μ' ⟨hresult, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst μ'
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + j) (F j) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, F, rowValue,
              hresult, LightBandLookup.time, LightBandLookup.searchTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [F, rowValue, hresult, LightBandLookup.time, LightBandLookup.searchTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, F, rowValue, hresult, LightBandLookup.time,
              LightBandLookup.searchTime] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, result, ?_⟩
    simp [update_frame_setLocal, wrote_succ]
  case done =>
    rintro _ _ ⟨r, rfl⟩
    exact
      ⟨fun j hj => wrote_done (μ := μ) (dst := dst) (f := F) hj, by
        ( try refine _root_.Light.SameOn.cell ?_
          intro x_p2m_726010792047762120 hx_p2m_726010792047762120
          first
          | ((  repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_15929973040463102139);
                    (try have := h_p2m_15929973040463102139 x_p2m_726010792047762120 (by omega));
                    revert h_p2m_15929973040463102139)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          |
            (simp [] at hx_p2m_726010792047762120;
              ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_13264637252659265292);
                    (try have := h_p2m_13264637252659265292 x_p2m_726010792047762120 (by omega));
                    revert h_p2m_13264637252659265292)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          | ( ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_6616900514026291753);
                    (try have := h_p2m_6616900514026291753 x_p2m_726010792047762120 (by omega));
                    revert h_p2m_6616900514026291753)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
              fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                          its condition K x does not follow from the hypotheses."))⟩
  case bound =>
    rintro j _ _ _ ⟨r, rfl⟩
    simp
end ThreeSum.LightBandTable
