-- Prove2me | solution 1 for ThreeSum.LightTernaryWeightedHistogram.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:41:21.501711+00:00
-- url     : https://prove2.me/submissions/3d972754-47f3-402a-914f-2fd0f04b83cb

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_count_ends
import Theorems.Thm_Light_Ends_pieceLast
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_fill_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_c744ea44a98f0b41
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedHistogram
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryWeightedHistogram
theorem _root_.solution {pMain pFill keys pairs source n dst bank sourceCount U : ℕ}
    (hmain : P[pMain]? = some (body pFill)) (hfill : P[pFill]? = some fillBody) (μ : ℕ → ℤ) (key position : ℕ → ℕ)
    (weight : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hkeys : keys + n ≤ dst)
    (hpairs : pairs + 2 * n ≤ dst) (hsource : source + sourceCount ≤ dst) (hdst : dst + bank ≤ lim.space)
    (hkeyRead : ∀ i < n, μ (keys + i) = (key i : ℤ)) (hposRead : ∀ i < n, μ (pairs + 2 * i) = (position i : ℤ))
    (hsourceRead : ∀ i < n, μ (source + position i) = weight i) (hkeyLt : ∀ i < n, key i < bank)
    (hposLt : ∀ i < n, position i < sourceCount) (hweights : ∀ i < n, |weight i| ≤ U)
    (hword : ((n + 1 : ℕ) : ℤ) * U ≤ lim.word) :
    Meets lim P pMain d [keys, pairs, source, n, dst, bank, sourceCount] μ (time n bank)
      (fun _ ν => (∀ r < bank, ν (dst + r) = total key weight r n) ∧ SameOutside μ ν dst bank) :=
  by
  apply Meets.of_body hmain
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
    | refine _root_.Light.Ends.callToThen ((fill_meets hfill (μ := μ) (x := 0) hw hdst) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (fill_meets hfill (μ := μ) (x := 0) hw hdst) ?_ ?_ ?_ ?_
    on_goal -1 =>
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
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro res μ₁ ⟨hfilled, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hk : ∀ i < n, μ₁ (keys + i) = (key i : ℤ) := by
    intro i hi
    exact (hkeep _ (Or.inl (by omega))).trans (hkeyRead i hi)
  have hp : ∀ i < n, μ₁ (pairs + 2 * i) = (position i : ℤ) :=
    by
    intro i hi
    exact (hkeep _ (Or.inl (by omega))).trans (hposRead i hi)
  have hs : ∀ i < n, μ₁ (source + position i) = weight i :=
    by
    intro i hi
    exact (hkeep _ (Or.inl (by have hh := hposLt i hi; omega))).trans (hsourceRead i hi)
  have hz : ∀ r < bank, μ₁ (dst + r) = 0 := by
    intro r hr
    exact (hfilled r (by simpa using hr)).trans (List.getElem_replicate ..)
  apply
    Ends.pieceLast
      (count_ends key position weight (by simp) hw hkeys hpairs hsource hdst hk hp hs hkeyLt hposLt hz hweights hword)
  · intro σ' hpost
    exact ⟨hpost.1, fun a ha => (hpost.2 a ha).trans (hkeep a ha)⟩
end ThreeSum.LightTernaryWeightedHistogram
