-- Prove2me | solution 1 for ThreeSum.LightBalancedOffset.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:26.387842+00:00
-- url     : https://prove2.me/submissions/f8b873d2-b4c0-49ab-a2b4-67d443c7403f

import Definitions.Def_Submission_ThreeSum_LightCyclic
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_e1f688d1cacb0f6f
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
set_option autoImplicit false
open ThreeSum ThreeSum.LightBalancedOffset
open Light Karatsuba CyclicFold LightKaratsuba Finset
open scoped BigOperators
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBalancedOffset
theorem _root_.solution {pMain pCyclic pMinimum pMultiply pHalf pLinear pFill : ℕ}
    (hmain : P[pMain]? = some (body pCyclic pMinimum))
    (hcyclic : P[pCyclic]? = some (LightCyclic.body pMultiply pLinear))
    (hminimum : P[pMinimum]? = some LightMinimum.body) (K : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill)
    {μ : ℕ → ℤ} {k a b prod dst work p U : ℕ} [NeZero p] (F H : ZMod p → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hpn : p ≤ 2 ^ k) (hAseg : Seg μ a (padTo (2 ^ k) (vector p F)))
    (hBseg : Seg μ b (padTo (2 ^ k) (vector p (fun z => H (-z))))) (hA : CoeffBound (vector p F) (U : ℤ))
    (hB : CoeffBound (vector p (fun z => H (-z))) (U : ℤ)) (haf : a + 2 ^ k ≤ work) (hbf : b + 2 ^ k ≤ work)
    (hpf : prod + 2 * 2 ^ k ≤ work) (hdf : dst + p ≤ work) (hsep : Apart prod (2 * 2 ^ k) dst p)
    (hspace : work + 8 * 2 ^ k ≤ lim.space) (hword : (LightKaratsuba.wordBound (2 ^ k) U : ℤ) ≤ lim.word)
    (hd : d + k + 3 ≤ lim.depth) :
    Meets lim P pMain d [2 ^ k, a, b, prod, dst, work, p] μ (time k p) fun r μ' =>
      r = (offset F H : ℤ) ∧ (∀ j < work, (j < prod ∨ prod + 2 * 2 ^ k ≤ j) → (j < dst ∨ dst + p ≤ j) → μ' j = μ j) :=
  by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightCyclic.correlation_meets (d := d + 1) hcyclic K F H hw hpn hAseg hBseg hA hB haf hbf hpf hdf hsep
              hspace hword (by omega))
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightCyclic.correlation_meets (d := d + 1) hcyclic K F H hw hpn hAseg hBseg hA hB haf hbf hpf hdf hsep hspace
            hword (by omega))
          ?_ ?_ ?_ ?_
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
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro _ μ₁ ⟨hcorr, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
          ((LightMinimum.meets (d := d + 1) (src := dst) (n := p) hminimum
              (fun r => (Balancing.correlation F H (r : ZMod p) : ℤ)) hw hp (by omega) hcorr)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightMinimum.meets (d := d + 1) (src := dst) (n := p) hminimum
            (fun r => (Balancing.correlation F H (r : ZMod p) : ℤ)) hw hp (by omega) hcorr)
          ?_ ?_ ?_ ?_
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
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro result μ₂ ⟨hresult, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₂
  exact ⟨by change result = _; exact hresult, hkeep⟩
end ThreeSum.LightBalancedOffset
