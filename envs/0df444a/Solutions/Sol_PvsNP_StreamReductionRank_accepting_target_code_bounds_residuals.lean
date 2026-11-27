-- Prove2me | solution 1 for PvsNP.StreamReductionRank.accepting_target_code_bounds_residuals
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T05:26:30.395995+00:00
-- url     : https://prove2.me/submissions/dd97ec7a-f7af-4a73-b9d2-7b0c60e3f4f6

import Definitions.Def_StreamReductionResidualRank

set_option autoImplicit false

namespace PvsNP.StreamReductionRank

universe u v w x y

variable {A : Type u} {B : Type v} {S : Type w}

theorem Transducer.run_append (R : Transducer A B S) (q : S) (xs ys : List A) :
    R.run q (xs ++ ys) =
      let first := R.run q xs
      let rest := R.run first.1 ys
      (rest.1, first.2 ++ rest.2) := by
  induction xs generalizing q with
  | nil => simp [Transducer.run]
  | cons a xs ih => simp [Transducer.run, ih, List.append_assoc]

theorem Transducer.output_append (R : Transducer A B S) (xs ys : List A) :
    R.output (xs ++ ys) =
      let first := R.run R.init xs
      let rest := R.run first.1 ys
      first.2 ++ (rest.2 ++ R.finish rest.1) := by
  simp [Transducer.output,R.run_append,List.append_assoc]

/-- This bounds residual rank using only the transducer state and the
accepting target codes. The reduction may identify complete source words. -/
theorem residual_rank_le_summary {I : Type x} {Code : Type y} {Summary : Type*}
    [Fintype I] [Fintype Summary] [Fintype Code]
    (R : Transducer A B S) (initialWord : I → List A)
    (remember : I → Summary)
    (faithful : ∀ i j, remember i = remember j →
      (R.run R.init (initialWord i)).1 = (R.run R.init (initialWord j)).1)
    (source : List A → Prop) (target : List B → Prop)
    (decode : Code → List B) (limit : ℕ)
    (width : ∀ c, (decode c).length ≤ limit)
    (complete : ∀ i, ∃ tail, source (initialWord i ++ tail))
    (separate : ∀ i j, i ≠ j → ∃ tail, ¬ (source (initialWord i ++ tail) ↔ source (initialWord j ++ tail)))
    (correct : ∀ i tail, target (R.output (initialWord i ++ tail)) ↔ source (initialWord i ++ tail))
    (covers : ∀ z, target z → ∃ c, decode c = z) :
    Fintype.card I ≤ Fintype.card Summary * Fintype.card Code * (limit+1) := by
  classical
  choose tail yes using complete
  have hasCode (i : I) : ∃ c, decode c = R.output (initialWord i ++ tail i) :=
    covers _ ((correct i _).mpr (yes i))
  choose code codeEq using hasCode
  have reconstruct (i : I) :
      ((decode (code i)).take (R.run R.init (initialWord i)).2.length) = (R.run R.init (initialWord i)).2 := by
    rw [codeEq, R.output_append]
    simp
  have emittedBound (i : I) : (R.run R.init (initialWord i)).2.length ≤ limit := by
    have known := width (code i)
    rw [codeEq,R.output_append,List.length_append] at known
    omega
  let label : I → (Summary × Code) × Fin (limit+1) :=
    fun i => ⟨⟨remember i,code i⟩,⟨(R.run R.init (initialWord i)).2.length,Nat.lt_succ_of_le (emittedBound i)⟩⟩
  have inj : Function.Injective label := by
    intro i j same
    have summary := congrArg (fun z => z.1.1) same
    have state := faithful i j summary
    have encoded := congrArg (fun z => z.1.2) same
    have count := congrArg (fun z => z.2.val) same
    change code i = code j at encoded
    change (R.run R.init (initialWord i)).2.length = (R.run R.init (initialWord j)).2.length at count
    have emitted : (R.run R.init (initialWord i)).2 = (R.run R.init (initialWord j)).2 := by
      rw [← reconstruct i,← reconstruct j,count,encoded]
    by_contra unequal
    obtain ⟨tail, witness⟩ := separate i j unequal
    apply witness
    rw [← correct i, ← correct j,R.output_append,R.output_append]
    simp only [state,emitted]
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective label inj

/-- This bounds residual rank using only the transducer state and the
accepting target codes. The reduction may identify complete source words. -/
theorem residual_rank_le {I : Type x} {Code : Type y} [Fintype I] [Fintype S] [Fintype Code]
    (R : Transducer A B S) (initialWord : I → List A)
    (source : List A → Prop) (target : List B → Prop)
    (decode : Code → List B) (limit : ℕ)
    (width : ∀ c, (decode c).length ≤ limit)
    (complete : ∀ i, ∃ tail, source (initialWord i ++ tail))
    (separate : ∀ i j, i ≠ j → ∃ tail, ¬ (source (initialWord i ++ tail) ↔ source (initialWord j ++ tail)))
    (correct : ∀ i tail, target (R.output (initialWord i ++ tail)) ↔ source (initialWord i ++ tail))
    (covers : ∀ z, target z → ∃ c, decode c = z) :
    Fintype.card I ≤ Fintype.card S * Fintype.card Code * (limit+1) :=
  residual_rank_le_summary R initialWord (fun i => (R.run R.init (initialWord i)).1)
    (fun _ _ same => same) source target decode limit width complete separate correct covers

end PvsNP.StreamReductionRank

set_option autoImplicit false

open PvsNP.StreamReductionRank

universe u v w x y

theorem solution {A : Type u} {B : Type v} {S : Type w} {I : Type x} {Code : Type y} {Summary : Type*}
    [Fintype I] [Fintype Summary] [Fintype Code]
    (R : Transducer A B S) (initialWord : I → List A)
    (remember : I → Summary)
    (faithful : ∀ i j, remember i = remember j →
      (R.run R.init (initialWord i)).1 = (R.run R.init (initialWord j)).1)
    (source : List A → Prop) (target : List B → Prop)
    (decode : Code → List B) (limit : ℕ)
    (width : ∀ c, (decode c).length ≤ limit)
    (complete : ∀ i, ∃ tail, source (initialWord i ++ tail))
    (separate : ∀ i j, i ≠ j → ∃ tail, ¬ (source (initialWord i ++ tail) ↔ source (initialWord j ++ tail)))
    (correct : ∀ i tail, target (R.output (initialWord i ++ tail)) ↔ source (initialWord i ++ tail))
    (covers : ∀ z, target z → ∃ c, decode c = z) :
    Fintype.card I ≤ Fintype.card Summary * Fintype.card Code * (limit+1) := by
  exact residual_rank_le_summary R initialWord remember faithful source target decode limit
    width complete separate correct covers

#print axioms solution
