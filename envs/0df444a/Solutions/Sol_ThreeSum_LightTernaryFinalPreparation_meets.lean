-- Prove2me | solution 1 for ThreeSum.LightTernaryFinalPreparation.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:53:20.467351+00:00
-- url     : https://prove2.me/submissions/f7b77745-e0f7-44ba-9dc3-cf48ae5262dc

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionScore
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_powTable_meets
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryFinalPreparation
open Light LightSubsetAddress
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000
variable {lim : Limits}
namespace ThreeSum.LightTernaryFinalPreparation
theorem _root_.solution {keyB nB keyC nC q powers W histB histC d : ℕ} (μ : ℕ → ℤ) (keysB keysC : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hkeyB : keyB + nB ≤ powers) (hkeyC : keyC + nC ≤ powers)
    (hpowers : powers + (W + 1) ≤ histB) (hhistB : histB + q ≤ histC) (hhistC : histC + q ≤ lim.space)
    (hwordB : ((nB * nB + nB + q + 16 : ℕ) : ℤ) ≤ lim.word) (hwordC : ((nC * nC + nC + q + 16 : ℕ) : ℤ) ≤ lim.word)
    (hpowerWord : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word) (hkeysB : ∀ i < nB, keysB i < q) (hkeysC : ∀ i < nC, keysC i < q)
    (hreadB : ∀ i < nB, μ (keyB + i) = (keysB i : ℤ)) (hreadC : ∀ i < nC, μ (keyC + i) = (keysC i : ℤ))
    (hd : d + 3 ≤ lim.depth) :
    Meets lim program 5 d [keyB, nB, keyC, nC, q, powers, W, histB, histC] μ (time nB nC q W)
      (fun _ ν =>
        Powers ν powers W ∧
          (∀ k < q, ν (histB + k) = (LightHistogram.count keysB k nB : ℤ)) ∧
            (∀ k < q, ν (histC + k) = (LightHistogram.count keysC k nC : ℤ)) ∧
              Kept μ ν powers ∧ (∀ x, Unwritten powers W histB histC q x → ν x = μ x)) :=
  by
  have hp :=
    powTable_meets (P := program) (p := 4) (d := d + 1) (μ := μ) (dst := powers) (L := W + 1) (b := 2) rfl hw (by omega)
      (by
        intro j hj
        exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hj)).trans hpowerWord)
  apply Meets.of_body (p := 5) (by rfl : program[5]? = some body)
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
    | refine _root_.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime,
            LightOriginalCollisionScore.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, LightOriginalCollisionScore.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime,
            LightOriginalCollisionScore.time] <;>
          omega)
    on_goal -1 => (rintro ignored ν ⟨hPowers, hRestP⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hPB := powers_of_segment hPowers
  have hreadB' : ∀ i < nB, ν (keyB + i) = (keysB i : ℤ) :=
    by
    intro i hi
    exact (hRestP _ (Or.inl (by omega))).trans (hreadB i hi)
  have hB :=
    LightOriginalCollisionScore.meets (P := program) (pMain := 0) (pHist := 1) (pFill := 2) (pSum := 3) (d := d + 1)
      (src := keyB) (n := nB) (hist := histB) (q := q) rfl rfl rfl rfl ν keysB hw (by omega) (by omega)
      (Or.inl (by omega)) hwordB hkeysB hreadB' (by omega)
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
    | refine _root_.Light.Ends.callToThen (hB _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hB ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime,
            LightOriginalCollisionScore.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, LightOriginalCollisionScore.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime,
            LightOriginalCollisionScore.time] <;>
          omega)
    on_goal -1 =>
      (rintro ignoredB ξ ⟨hScoreB, hCountsB, hRestB⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hreadC' : ∀ i < nC, ξ (keyC + i) = (keysC i : ℤ) :=
    by
    intro i hi
    exact (hRestB _ (Or.inl (by omega))).trans ((hRestP _ (Or.inl (by omega))).trans (hreadC i hi))
  have hC :=
    LightOriginalCollisionScore.meets (P := program) (pMain := 0) (pHist := 1) (pFill := 2) (pSum := 3) (d := d + 1)
      (src := keyC) (n := nC) (hist := histC) (q := q) rfl rfl rfl rfl ξ keysC hw (by omega) (by omega)
      (Or.inl (by omega)) hwordC hkeysC hreadC' (by omega)
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
    | refine _root_.Light.Ends.callToThen (hC _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hC ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime,
            LightOriginalCollisionScore.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, LightOriginalCollisionScore.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime,
            LightOriginalCollisionScore.time] <;>
          omega)
    on_goal -1 =>
      (rintro ignoredC ζ ⟨hScoreC, hCountsC, hRestC⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨?_, ?_, hCountsC, ?_, ?_⟩
  · intro i hi
    change ζ (powers + i) = (2 ^ i : ℕ)
    rw [hRestC _ (Or.inl (by omega)), hRestB _ (Or.inl (by omega))]
    exact hPB i hi
  · intro k hk
    exact (hRestC _ (Or.inl (by omega))).trans (hCountsB k hk)
  · intro x hx
    exact (hRestC _ (Or.inl (by omega))).trans ((hRestB _ (Or.inl (by omega))).trans (hRestP _ (Or.inl hx)))
  · intro x hx
    exact (hRestC x hx.2.2).trans ((hRestB x hx.2.1).trans (hRestP x hx.1))
end ThreeSum.LightTernaryFinalPreparation
