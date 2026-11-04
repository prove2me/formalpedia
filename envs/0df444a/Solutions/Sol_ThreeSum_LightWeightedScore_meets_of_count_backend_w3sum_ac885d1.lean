-- Prove2me | solution 1 for ThreeSum.LightWeightedScore.meets_of_count_backend_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:40:31.055193+00:00
-- url     : https://prove2.me/submissions/f77c3eb3-97fc-4ba2-a01f-26680223b75d

import Definitions.Def_Submission_ThreeSum_WeightedScore
import Definitions.Def_Submission_ThreeSum_ModuloRuntime
import Definitions.Def_Submission_ThreeSum_LightWeightedScore
import Theorems.Thm_ThreeSum_LightWeightedScore_joint_meets
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_ModuloCounts_count_le
import Theorems.Thm_ThreeSum_WeightedModuli_joint_le_mul
import Theorems.Thm_ThreeSum_WeightedModuli_joint_positive
import Theorems.Thm_ThreeSum_WeightedScore_corrections_zero
import Theorems.Thm_ThreeSum_WeightedScore_next_count_le_remaining
import Theorems.Thm_ThreeSum_WeightedScore_remaining_le
import Theorems.Thm_ThreeSum_WeightedScore_remaining_succ_cast
import Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
import Definitions.Def_WeightedCache3SUM_Alias_31b4729195398428
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedScore
open Light WeightedModuli WeightedScore LightResidues
variable {lim : Limits} {P : Program} {d : ℕ}
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightWeightedScore
theorem _root_.solution {pMain pCount pJoint pEmod : ℕ} (hmain : P[pMain]? = some (body pCount pJoint))
    (hjoint : P[pJoint]? = some (jointBody pEmod)) (hem : P[pEmod]? = some emodBody) {μ : ℕ → ℤ}
    {a b c nA nB nC q N aux s free maxMod countTime : ℕ} (primes : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 1 < lim.depth) (hq : 0 < q) (hqmax : q ≤ maxMod) (ha : a + nA ≤ free) (hb : b + nB ≤ free)
    (hc : c + nC ≤ free) (haux : aux + s ≤ free) (hN : N ≤ lim.space) (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : free + (Nat.log 2 (maxMod + 1) + 2) ≤ lim.space)
    (hword : ((s + 1) * N ^ 3 + 8 * maxMod + 16 : ℕ) ≤ lim.word) (hread : ∀ i < s, μ (aux + i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i)) (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, q * primes i ≤ maxMod)
    (hcount :
      ∀ (ν : ℕ → ℤ) (p : ℕ),
        Kept μ ν free →
          0 < p →
            p ≤ maxMod →
              Meets lim P pCount (d + 1) [a, b, c, nA, nB, nC, p, N, free] ν countTime
                (fun r ν' =>
                  r =
                      (ModuloCounts.count p nA nB nC (fun j => μ (a + j)) (fun j => μ (b + j)) (fun j => μ (c + j)) :
                        ℤ) ∧
                    Kept ν ν' free)) :
    Meets lim P pMain d [a, b, c, nA, nB, nC, q, N, aux, s, free] μ (time countTime s maxMod) fun r μ' =>
      r = (score primes s q nA nB nC (fun j => μ (a + j)) (fun j => μ (b + j)) (fun j => μ (c + j)) : ℤ) ∧
        Kept μ μ' free :=
  by
  let A := fun j => μ (a + j)
  let B := fun j => μ (b + j)
  let C := fun j => μ (c + j)
  let base := ModuloCounts.count q nA nB nC A B C
  have hprodN : nA * nB * nC ≤ N ^ 3 := by
    calc
      _ ≤ N * N * N := Nat.mul_le_mul (Nat.mul_le_mul hnA hnB) hnC
      _ = _ := by ring
  have hbase : base ≤ N ^ 3 := (ModuloCounts.count_le q nA nB nC A B C).trans hprodN
  have hbound (i : ℕ) : remaining primes s q nA nB nC A B C i ≤ s * N ^ 3 :=
    (remaining_le primes s q nA nB nC A B C i).trans (Nat.mul_le_mul_left s hprodN)
  have hbaseZ : (base : ℤ) ≤ lim.word :=
    by
    have hm : N ^ 3 ≤ (s + 1) * N ^ 3 + 8 * maxMod + 16 := by nlinarith
    exact (Int.ofNat_le.mpr (hbase.trans hm)).trans hword
  have hscoreZ (i : ℕ) : (remaining primes s q nA nB nC A B C i : ℤ) ≤ lim.word :=
    by
    have hm : s * N ^ 3 ≤ (s + 1) * N ^ 3 + 8 * maxMod + 16 := by nlinarith
    exact (Int.ofNat_le.mpr ((hbound i).trans hm)).trans hword
  have hinitZ : ((s * base : ℕ) : ℤ) ≤ lim.word := by simpa only [remaining_zero] using hscoreZ 0
  have hinitNonneg : (0 : ℤ) ≤ (s : ℤ) * (base : ℤ) := by positivity
  dsimp [base, A, B, C] at hinitZ hinitNonneg
  have hjword : (8 * maxMod + 16 : ℕ) ≤ lim.word :=
    by
    have hh : 8 * maxMod + 16 ≤ (s + 1) * N ^ 3 + 8 * maxMod + 16 := by omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hNword : (N : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hN).trans hw
  have hmodword : (maxMod : ℤ) ≤ lim.word :=
    by
    have hwZ : (8 * (maxMod : ℤ) + 16) ≤ lim.word := by exact_mod_cast hjword
    omega
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
    | refine _root_.Light.Ends.callToThen ((hcount μ q (fun _ _ => rfl) hq hqmax) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (hcount μ q (fun _ _ => rfl) hq hqmax) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, A, B, C, base]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [A, B, C, base] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, A, B, C, base] <;> omega)
    on_goal -1 => (rintro res μ₀ ⟨hres, hkept₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hres' : res = (base : ℤ) := hres
  subst res
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (s * base : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, A, B, C, base]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [A, B, C, base] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, A, B, C, base] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (T := s * (countTime + jointTime maxMod + 100) + 20) (Q := Inv μ primes a b c nA nB nC q N aux s free s)
        (Inv μ primes a b c nA nB nC q N aux s free) s (countTime + jointTime maxMod + 80) ?_ ?_ ?_ ?_ (hT := by
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
      ?_
  · refine ⟨0, 0, μ₀, ?_, hkept₀⟩
    simp only [Inv, remaining_zero, update_frame_setLocal]
    exact congrArg (fun loc => (⟨loc, μ₀⟩ : State)) (frame_append_zeros _ 2).symm
  · rintro i _ hi _ ⟨jval, cval, ν, rfl, hkept⟩
    have hp := (hprime i hi).pos
    have hpmax : primes i ≤ maxMod := (Nat.le_mul_of_pos_left (primes i) hq).trans (hproduct i hi)
    have hpword : (primes i : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hpmax).trans hmodword
    have hreadν : ν (aux + i) = (primes i : ℤ) := (hkept _ (by omega)).trans (hread i hi)
    have hnext := next_count_le_remaining (q := q) (nA := nA) (nB := nB) (nC := nC) primes A B C hi
    have hremaincast := remaining_succ_cast (q := q) (nA := nA) (nB := nB) (nC := nC) primes A B C hi
    have hscoreNext := hscoreZ (i + 1)
    have hscoreNow := hscoreZ i
    dsimp [A, B, C] at hnext hremaincast hscoreNext hscoreNow
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
            ((joint_meets (d := d + 1) (q := q) (p := primes i) hjoint hem hw (by omega) hq hp (hproduct i hi) hspace
                hjword)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (joint_meets (d := d + 1) (q := q) (p := primes i) hjoint hem hw (by omega) hq hp (hproduct i hi) hspace
              hjword)
            ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadν, A, B, C,
              base]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hreadν, A, B, C, base] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadν, A, B, C, base] <;> omega)
      on_goal -1 => (rintro jres ν₁ ⟨hjres, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst jres
    have hkept₁ : Kept μ ν₁ free := fun j hj => (hkeep₁ j hj).trans (hkept j hj)
    have hjpos := joint_positive hq (hprime i hi)
    have hjmax := (joint_le_mul q (primes i) hp).trans (hproduct i hi)
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
          _root_.Light.Ends.callToThen ((hcount ν₁ (joint q (primes i)) hkept₁ hjpos hjmax) _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen (hcount ν₁ (joint q (primes i)) hkept₁ hjpos hjmax) ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, A, B, C, base]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [A, B, C, base] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, A, B, C, base] <;> omega)
      on_goal -1 => (rintro cres ν₂ ⟨hcres, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst cres
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (remaining primes s q nA nB nC A B C (i + 1)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, A, B, C, base,
              hremaincast]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [A, B, C, base, hremaincast] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, A, B, C, base, hremaincast] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, (joint q (primes i) : ℤ), (ModuloCounts.count (joint q (primes i)) nA nB nC A B C : ℤ), ν₂, ?_, ?_⟩
    · simp [Inv, update_frame_setLocal, A, B, C, base]
    · intro j hj
      exact (hkeep₂ j hj).trans (hkept₁ j hj)
  · intro σ _ hI
    exact hI
  · rintro i _ hi _ ⟨jval, cval, ν, rfl, hkept⟩
    simp
  · rintro σ ⟨jval, cval, ν, rfl, hkept⟩
    have hsc := hscoreZ s
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (remaining primes s q nA nB nC A B C s) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, A, B, C, base]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [A, B, C, base] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, A, B, C, base] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by rw [score_eq_remaining primes s q nA nB nC A B C hprime hinj]; simp, hkept⟩
end ThreeSum.LightWeightedScore
