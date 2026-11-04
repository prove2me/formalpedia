-- Prove2me | solution 1 for ThreeSum.LightTernaryAppendKeys.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:41.870195+00:00
-- url     : https://prove2.me/submissions/556b0586-5d14-4056-926d-dc2427b5d305

import Definitions.Def_Submission_ThreeSum_LightSignedRowHash
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightNaturalDot_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Theorems.Thm_ThreeSum_LightSignedRowHash_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryAppendKeys
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 6000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightTernaryAppendKeys
namespace Procs
theorem _root_.solution {main matrix row oldBase dst n len p power scratch b : ℕ} (S : Procs P main) (μ : ℕ → ℤ)
    (old : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (c : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth + 3 < lim.depth)
    (hbp : b < p) (hmatrix : matrix + n * len ≤ dst) (hrow : row + len ≤ dst) (hold : oldBase + n ≤ dst)
    (hout : dst + n ≤ scratch) (hspace : scratch + len ≤ lim.space)
    (hmRead : ∀ i < n, ∀ k < len, μ (matrix + i * len + k) = z i k) (hcRead : ∀ k < len, μ (row + k) = (c k : ℤ))
    (hoRead : ∀ i < n, μ (oldBase + i) = (old i : ℤ)) (hzBound : ∀ i < n, ∀ k < len, |z i k| ≤ (b : ℤ))
    (hcBound : ∀ k < len, c k ≤ p) (hoBound : ∀ i < n, old i < power) (hword : (word len p b power : ℤ) ≤ lim.word) :
    Meets lim P main depth [matrix, row, oldBase, dst, n, len, p, power, scratch] μ (time n len p b)
      (fun _ ν => (∀ i < n, ν (dst + i) = (key p power len old z c i : ℤ)) ∧ Kept μ ν dst) :=
  by
  have hp : 0 < p := by omega
  have hwHash : (LightSignedRowHash.word len p b : ℤ) ≤ lim.word := by unfold word at hword; omega
  have hpowerWord : (power : ℤ) ≤ lim.word :=
    by
    have hh : power ≤ power * p := Nat.le_mul_of_pos_right _ hp
    unfold word at hword
    omega
  have hpowerPWord : ((power * p : ℕ) : ℤ) ≤ lim.word := by unfold word at hword; omega
  have hnWord : (n : ℤ) ≤ lim.word := by omega
  have hkeyBound (i : ℕ) (hi : i < n) : key p power len old z c i < power * p :=
    by
    have hh := Nat.mod_lt (LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len) hp
    have ho := hoBound i hi
    unfold key
    nlinarith
  have hkeyWord (i : ℕ) (hi : i < n) : ((key p power len old z c i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (hkeyBound i hi).le).trans hpowerPWord
  apply Meets.of_body S.mainBody
  unfold body time
  refine
    Ends.for (Inv μ matrix row oldBase dst n len p power scratch old z c) n (LightSignedRowHash.time len p b + 110)
      ?start ?round ?done ?bound (hT := by
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
    refine ⟨0, μ, ?_, ?_, SameOn.refl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro i hi; omega
  case round =>
    rintro i _ hi _ ⟨val, ν, rfl, written, kept⟩
    have hprod : i * len + len ≤ n * len := by nlinarith
    have hmatrixEnd : matrix + i * len + len ≤ scratch := by omega
    have hmValues (k : ℕ) (hk : k < len) : ν (matrix + i * len + k) = z i k :=
      (kept _ (by omega)).trans (hmRead i hi k hk)
    have hcValues (k : ℕ) (hk : k < len) : ν (row + k) = (c k : ℤ) := (kept _ (by omega)).trans (hcRead k hk)
    have hoValues : ν (oldBase + i) = (old i : ℤ) := (kept _ (by omega)).trans (hoRead i hi)
    have hrowEnd : row + len ≤ scratch := by omega
    have hrowWord : ((i * len : ℕ) : ℤ) ≤ lim.word := by omega
    unfold key at hkeyWord
    unfold body at *
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
            ((S.hashProcs.meets (depth := depth + 1) ν (z i) c hw (by omega) hbp hmatrixEnd hrowEnd hspace hmValues
                hcValues (hzBound i hi) hcBound hwHash)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (S.hashProcs.meets (depth := depth + 1) ν (z i) c hw (by omega) hbp hmatrixEnd hrowEnd hspace hmValues
              hcValues (hzBound i hi) hcBound hwHash)
            ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightSignedRowHash.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightSignedRowHash.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSignedRowHash.time] <;> omega)
      on_goal -1 => (rintro r ξ ⟨hr, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hoNew : ξ (oldBase + i) = (old i : ℤ) := (hkeep _ (Or.inl (by omega))).trans hoValues
    have haddr : ((oldBase : ℤ) + (i : ℤ)).toNat = oldBase + i := by omega
    have hoWord : (old i : ℤ) ≤ lim.word := by have hh := hoBound i hi; omega
    have hhashBound := Nat.mod_lt (LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len) hp
    have hhashWord :
      (((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len) % p : ℕ) : ℤ) ≤ lim.word :=
      by
      have hpWord : (p : ℤ) ≤ lim.word := by unfold LightSignedRowHash.word at hwHash; omega
      omega
    have hmulWord :
      ((power * (LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len % p) : ℕ) : ℤ) ≤ lim.word :=
      by
      have hh := hkeyWord i hi
      omega
    have hmodcast :
      ((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len : ℕ) : ℤ) % (p : ℤ) =
        ((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len % p : ℕ) : ℤ) :=
      by norm_cast
    have hmulNonneg :
      0 ≤ (power : ℤ) * (((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len % p : ℕ) : ℤ)) := by
      positivity
    have hprodIntNonneg :
      0 ≤
        (power : ℤ) *
          (((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len : ℕ) : ℤ) % (p : ℤ)) :=
      by rw [hmodcast]; positivity
    have hprodIntWord :
      (power : ℤ) * (((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len : ℕ) : ℤ) % (p : ℤ)) ≤
        lim.word :=
      by
      rw [hmodcast]
      exact_mod_cast hmulWord
    have hoMemNonneg : 0 ≤ ξ (oldBase + i) := by rw [hoNew]; positivity
    have hsumMemWord :
      ξ (oldBase + i) +
          (power : ℤ) *
            (((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len : ℕ) : ℤ) % (p : ℤ)) ≤
        lim.word :=
      by
      rw [hoNew, hmodcast]
      exact_mod_cast hkeyWord i hi
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + i) (key p power len old z c i) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, key, hr, hoNew,
              haddr, frame, LightSignedRowHash.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [key, hr, hoNew, haddr, frame, LightSignedRowHash.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, key, hr, hoNew, haddr, frame,
              LightSignedRowHash.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp [frame], r, Function.update ξ (dst + i) (key p power len old z c i : ℤ), by simp [update_frame_setLocal],
        ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega), hkeep _ (Or.inl (by omega))]
        exact written j hj
      · simp
    · intro j hj
      rw [Function.update_of_ne (by omega), hkeep _ (Or.inl (by omega)), kept _ hj]
  case done => rintro _ _ ⟨val, ν, rfl, written, kept⟩; exact ⟨written, kept⟩
  case bound =>
    rintro i _ _ _ ⟨val, ν, rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end Procs
end ThreeSum.LightTernaryAppendKeys
