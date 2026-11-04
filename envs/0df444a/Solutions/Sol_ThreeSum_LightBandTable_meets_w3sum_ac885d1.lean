-- Prove2me | solution 1 for ThreeSum.LightBandTable.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:32.311068+00:00
-- url     : https://prove2.me/submissions/aea35850-1395-4caf-b22d-283199bde04f

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightBandTable
import Definitions.Def_WeightedCache3SUM_Alias_9fcc3660f5e29553
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
import Theorems.Thm_ThreeSum_LightPascal_row_meets
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
theorem _root_.solution {pMain pRow pLookup pSearch a b loBase hiBase nX nY m dst powers W d U : ℕ} {s : ℤ}
    (hmain : P[pMain]? = some (body pRow)) (hrow : P[pRow]? = some (rowBody pLookup))
    (hlookup : P[pLookup]? = some (LightBandLookup.body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch)) (μ : ℕ → ℤ) (f g lo hi : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + nX ≤ dst) (hb : b + nY ≤ dst) (hlo : loBase + m ≤ dst)
    (hhi : hiBase + m ≤ dst) (hdst : dst + nX * nY ≤ powers) (hspace : powers + (W + 1) ≤ lim.space)
    (hword : ((m + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word) (hqueryWord : 2 * (U : ℤ) ≤ lim.word)
    (hreadA : ∀ i < nX, μ (a + i) = f i) (hreadB : ∀ j < nY, μ (b + j) = g j) (hreadLo : ∀ j < m, μ (loBase + j) = lo j)
    (hreadHi : ∀ j < m, μ (hiBase + j) = hi j) (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i ≤ j → j < m → lo i ≤ lo j) (hm : m < 2 ^ W) (hs : |s| ≤ 1) (hf : ∀ i < nX, |f i| ≤ U)
    (hg : ∀ j < nY, |g j| ≤ U) (hd : d + W + 3 ≤ lim.depth) :
    Meets lim P pMain d [a, b, loBase, hiBase, nX, nY, m, dst, powers, W, s] μ (time nX nY W)
      (fun _ μ' =>
        (∀ i < nX, ∀ j < nY, μ' (dst + i * nY + j) = (rowValue lo hi m (f i) s g j : ℤ)) ∧
          SameOutside μ μ' dst (nX * nY)) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for
      (fun i σ =>
        ∃ (r : ℤ) (μ' : ℕ → ℤ),
          σ = ⟨frame [a, b, loBase, hiBase, nX, nY, m, dst, powers, W, s, i, r], μ'⟩ ∧
            (∀ j < i, ∀ k < nY, μ' (dst + j * nY + k) = (rowValue lo hi m (f j) s g k : ℤ)) ∧
              SameOutside μ μ' dst (nX * nY))
      nX (rowTime nY W + 62) ?start ?round ?done ?bound
  case start =>
    refine ⟨0, μ, ?_, ?_, SameOutside.refl⟩
    · simp [update_frame_setLocal]
      simpa using (frame_append_zeros [a, b, loBase, hiBase, nX, nY, m, dst, powers, W, s, 0] 1).symm
    · intro j hj
      omega
  case round =>
    rintro i _ hin _ ⟨r, μ', rfl, written, kept⟩
    have hiMul : i * nY + nY ≤ nX * nY :=
      by
      have hh := Nat.mul_le_mul_right nY (show i + 1 ≤ nX by omega)
      simpa [Nat.add_mul] using hh
    have hiMulLe : i * nY ≤ nX * nY := by omega
    have hiMulNZ : (0 : ℤ) ≤ (i : ℤ) * (nY : ℤ) := by positivity
    have hiAddrWord : (dst : ℤ) + (i : ℤ) * (nY : ℤ) ≤ lim.word :=
      by
      have hz : (dst : ℤ) + (i : ℤ) * (nY : ℤ) ≤ (lim.space : ℤ) := by
        exact_mod_cast (show dst + i * nY ≤ lim.space by omega)
      exact hz.trans hw
    have hrA : μ' (a + i) = f i := (kept (a + i) (Or.inl (by omega))).trans (hreadA i hin)
    have hrB : ∀ j < nY, μ' (b + j) = g j := by
      intro j hj
      exact (kept (b + j) (Or.inl (by omega))).trans (hreadB j hj)
    have hrLo : ∀ j < m, μ' (loBase + j) = lo j := by
      intro j hj
      exact (kept (loBase + j) (Or.inl (by omega))).trans (hreadLo j hj)
    have hrHi : ∀ j < m, μ' (hiBase + j) = hi j := by
      intro j hj
      exact (kept (hiBase + j) (Or.inl (by omega))).trans (hreadHi j hj)
    have hpowers' : Powers μ' powers W := by
      intro j hj
      rw [kept (powers + j) (Or.inr (by omega))]
      exact hpowers j hj
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
            ((row_meets (d := d + 1) (x := f i) (s := s) (dst := dst + i * nY) hrow hlookup hsearch μ' g lo hi hw
                (by omega) (by omega) (by omega) (by omega) hspace hword hqueryWord hrB hrLo hrHi hpowers' hsorted hm hs
                (hf i hin) hg (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (row_meets (d := d + 1) (x := f i) (s := s) (dst := dst + i * nY) hrow hlookup hsearch μ' g lo hi hw
              (by omega) (by omega) (by omega) (by omega) hspace hword hqueryWord hrB hrLo hrHi hpowers' hsorted hm hs
              (hf i hin) hg (by omega))
            ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrA, rowTime,
              LightBandLookup.time, LightBandLookup.searchTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hrA, rowTime, LightBandLookup.time, LightBandLookup.searchTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrA, rowTime, LightBandLookup.time,
              LightBandLookup.searchTime] <;>
            omega)
      on_goal -1 =>
        (rintro returned μ'' ⟨rowWritten, rowKept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, returned, μ'', by simp [update_frame_setLocal], ?_, ?_⟩
    · intro j hj k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hji : j * nY + nY ≤ i * nY :=
          by
          have hh := Nat.mul_le_mul_right nY (show j + 1 ≤ i by omega)
          simpa [Nat.add_mul] using hh
        rw [rowKept (dst + j * nY + k) (Or.inl (by omega))]
        exact written j hj k hk
      · exact rowWritten k hk
    · intro addr haddr
      rw [rowKept addr (by omega)]
      exact kept addr haddr
  case done =>
    rintro _ _ ⟨r, μ', rfl, written, kept⟩
    exact ⟨written, kept⟩
  case bound =>
    rintro i _ _ _ ⟨r, μ', rfl, written, kept⟩
    simp
end ThreeSum.LightBandTable
