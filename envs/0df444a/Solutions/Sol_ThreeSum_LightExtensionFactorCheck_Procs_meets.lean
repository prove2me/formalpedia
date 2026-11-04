-- Prove2me | solution 1 for ThreeSum.LightExtensionFactorCheck.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:33:39.957294+00:00
-- url     : https://prove2.me/submissions/7781828e-a6ba-46ab-a1fd-d8512a38e5f1

import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
import Definitions.Def_Submission_ThreeSum_LightCoefficientDecode
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorCheck
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionFactorCheck
open Light
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightExtensionFactorCheck
namespace Procs
theorem _root_.solution {main d e p u v powers target hBase gBase : ℕ} (S : Procs P main) (μ : ℕ → ℤ) (f : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth + 3 < lim.depth) (hp : 1 < p) (he : 0 < e) (hed : e < d)
    (hpow : powers + (2 * d + 1) ≤ hBase) (htarget : target + 2 * d ≤ hBase) (hh : hBase + 2 * d ≤ gBase)
    (hspace : gBase + 2 * d ≤ lim.space) (hpowRead : ∀ i ≤ 2 * d, μ (powers + i) = ((p ^ i : ℕ) : ℤ))
    (hfRead : ∀ i < 2 * d, μ (target + i) = (f i : ℤ)) (hword : (word d e p u v : ℤ) ≤ lim.word) :
    Meets lim P main depth [u, v, p, d, e, powers, target, hBase, gBase] μ (time d e p u v)
      (fun z ν =>
        z = LightPolynomialProductCheck.flag p (digits p u) (digits p v) f (e + 1) (d - e + 1) (2 * d) ∧
          Kept μ ν hBase) :=
  by
  have hwU : (LightCoefficientDecode.word (2 * d) p u 0 1 : ℤ) ≤ lim.word := by unfold word at hword; omega
  have hwV : (LightCoefficientDecode.word (2 * d) p v 0 1 : ℤ) ≤ lim.word := by unfold word at hword; omega
  have hwCheck : ((20 * ((e + 2) * (p + 1) ^ 2 + 2 * d + (d - e + 1) + 10) : ℕ) : ℤ) ≤ lim.word := by
    unfold word at hword; omega
  have hu : (u : ℤ) ≤ lim.word := by unfold LightCoefficientDecode.word at hwU; omega
  have hv : (v : ℤ) ≤ lim.word := by unfold LightCoefficientDecode.word at hwV; omega
  have hpWord : (p : ℤ) ≤ lim.word := by unfold LightCoefficientDecode.word at hwU; omega
  have hdWord : (d : ℤ) ≤ lim.word := by unfold LightCoefficientDecode.word at hwU; omega
  have h2d : (2 * (d : ℤ)) ≤ lim.word := by unfold LightCoefficientDecode.word at hwU; omega
  have heWord : (e : ℤ) ≤ lim.word := by omega
  have hegWord : ((d - e + 1 : ℕ) : ℤ) ≤ lim.word := by omega
  have he1Word : ((e + 1 : ℕ) : ℤ) ≤ lim.word := by omega
  have htwo : (2 : ℤ) ≤ lim.word := by unfold word at hword; omega
  have hsub : (d : ℤ) - (e : ℤ) = ((d - e : ℕ) : ℤ) := (Int.natCast_sub (by omega)).symm
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
    refine _root_.Light.Ends.setToThen (2 * d : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightCoefficientDecode.time,
            LightPolynomialProductCheck.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightCoefficientDecode.time, LightPolynomialProductCheck.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightCoefficientDecode.time,
            LightPolynomialProductCheck.time] <;>
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightCoefficientDecode.meets (d := depth + 1) (W := 2 * d) (p := p) (k := u) (powers := powers) (start := 0)
              (stride := 1) (dst := hBase) (n := 2 * d) S.decodeBody S.digitBody S.divideBody hw (by omega) (by omega)
              (by omega) (by omega) (Or.inl hpow) hwU (by intro i hi; omega) hpowRead)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightCoefficientDecode.meets (d := depth + 1) (W := 2 * d) (p := p) (k := u) (powers := powers) (start := 0)
            (stride := 1) (dst := hBase) (n := 2 * d) S.decodeBody S.digitBody S.divideBody hw (by omega) (by omega)
            (by omega) (by omega) (Or.inl hpow) hwU (by intro i hi; omega) hpowRead)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightCoefficientDecode.time,
            LightPolynomialProductCheck.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightCoefficientDecode.time, LightPolynomialProductCheck.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightCoefficientDecode.time,
            LightPolynomialProductCheck.time] <;>
          omega)
    on_goal -1 => (rintro z₁ μ₁ ⟨uValues, keep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have pow₁ (i : ℕ) (hi : i ≤ 2 * d) : μ₁ (powers + i) = ((p ^ i : ℕ) : ℤ) :=
    (keep₁ _ (Or.inl (by omega))).trans (hpowRead i hi)
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
          ((LightCoefficientDecode.meets (d := depth + 1) (W := 2 * d) (p := p) (k := v) (powers := powers) (start := 0)
              (stride := 1) (dst := gBase) (n := 2 * d) S.decodeBody S.digitBody S.divideBody hw (by omega) (by omega)
              hspace (by omega) (Or.inl (by omega)) hwV (by intro i hi; omega) pow₁)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightCoefficientDecode.meets (d := depth + 1) (W := 2 * d) (p := p) (k := v) (powers := powers) (start := 0)
            (stride := 1) (dst := gBase) (n := 2 * d) S.decodeBody S.digitBody S.divideBody hw (by omega) (by omega)
            hspace (by omega) (Or.inl (by omega)) hwV (by intro i hi; omega) pow₁)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightCoefficientDecode.time,
            LightPolynomialProductCheck.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightCoefficientDecode.time, LightPolynomialProductCheck.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightCoefficientDecode.time,
            LightPolynomialProductCheck.time] <;>
          omega)
    on_goal -1 => (rintro z₂ μ₂ ⟨vValues, keep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have u₂ (i : ℕ) (hi : i < e + 1) : μ₂ (hBase + i) = (digits p u i : ℤ) :=
    by
    rw [keep₂ _ (Or.inl (by omega))]
    simpa [digits] using uValues i (by omega)
  have v₂ (i : ℕ) (hi : i < d - e + 1) : μ₂ (gBase + i) = (digits p v i : ℤ) := by
    simpa [digits] using vValues i (by omega)
  have f₂ (i : ℕ) (hi : i < 2 * d) : μ₂ (target + i) = (f i : ℤ) := by
    rw [keep₂ _ (Or.inl (by omega)), keep₁ _ (Or.inl (by omega)), hfRead i hi]
  have digBound (code i : ℕ) : digits p code i < p := Nat.mod_lt _ (by omega)
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
          ((LightPolynomialProductCheck.meets (depth := depth + 1) S.checkBody S.coefficientBody S.rawBody S.digitBody
              S.divideBody μ₂ (digits p u) (digits p v) f hw (by omega) (by omega) (by omega) (by omega) u₂ v₂ f₂
              (fun i _ => digBound u i) (fun i _ => digBound v i) hwCheck)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightPolynomialProductCheck.meets (depth := depth + 1) S.checkBody S.coefficientBody S.rawBody S.digitBody
            S.divideBody μ₂ (digits p u) (digits p v) f hw (by omega) (by omega) (by omega) (by omega) u₂ v₂ f₂
            (fun i _ => digBound u i) (fun i _ => digBound v i) hwCheck)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsub, LightCoefficientDecode.time,
            LightPolynomialProductCheck.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hsub, LightCoefficientDecode.time, LightPolynomialProductCheck.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsub, LightCoefficientDecode.time,
            LightPolynomialProductCheck.time] <;>
          omega)
    on_goal -1 => (rintro z ν ⟨hz, hν⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν
  refine ⟨hz, ?_⟩
  intro i hi
  change μ₂ i = μ i
  rw [keep₂ _ (Or.inl (by omega)), keep₁ _ (Or.inl hi)]
end Procs
end ThreeSum.LightExtensionFactorCheck
