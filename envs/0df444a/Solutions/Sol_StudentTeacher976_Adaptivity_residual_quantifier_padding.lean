-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.residual_quantifier_padding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:40:33.421109+00:00
-- url     : https://prove2.me/submissions/1826ce17-4512-4c41-b831-db430918d60a

import Definitions.Def_StudentTeacher976_Adaptivity_Auxiliary
import Theorems.Thm_StudentTeacher976_Adaptivity_padded_residual_verifier
set_option autoImplicit false
open QAdvFew.PoQOracle
namespace StudentTeacher976.Adaptivity
private def component (u : Word) : Word := u.flatMap (fun b => [true, b]) ++ [false, false]
private theorem read_component (u rest : Word) : readComponent (component u ++ rest) = some (u, rest) := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    simp only [component, List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc] at ih ⊢
    simpa [readComponent] using congrArg (fun o => o.map (fun p : Word × Word => (b :: p.1, p.2))) ih

 theorem tup_pair_injective {x y u v : Word} (h : tup [x, y] = tup [u, v]) : x = u ∧ y = v := by
  have hcode : ∀ a b : Word, tup [a, b] = component a ++ tup [b] := by
    intro a b
    simp [tup, component, List.append_assoc]
  have hfirst := congrArg readComponent h
  rw [hcode, hcode, read_component, read_component] at hfirst
  have hpair : x = u ∧ tup [y] = tup [v] := by simpa using hfirst
  have hsingle : ∀ a : Word, tup [a] = component a ++ [] := by intro a; simp [tup, component]
  have hsecond := congrArg readComponent hpair.2
  rw [hsingle, hsingle, read_component, read_component] at hsecond
  exact ⟨hpair.1, congrArg Prod.fst (Option.some.inj hsecond)⟩


end StudentTeacher976.Adaptivity
set_option autoImplicit false
open QAdvFew.PoQOracle
namespace StudentTeacher976.Adaptivity

private theorem extend_word (n m : ℕ) (hnm : n ≤ m) (u : Word) (hu : u.length = n) :
    ∃ w : Word, w.length = m ∧ w.take n = u := by
  refine ⟨u ++ List.replicate (m - n) false, ?_, ?_⟩
  · simp [hu]; omega
  · rw [← hu, List.take_left]

 theorem altLen_trim {short long : List ℕ} (hrel : List.Forall₂ (· ≤ ·) short long)
    (start : Bool) (P : List Word → Prop) :
    AvgPHETH.AltLen long start
        (fun ys => P (List.zipWith (fun n w => w.take n) short ys)) ↔
      AvgPHETH.AltLen short start P := by
  induction hrel generalizing start P with
  | nil => rfl
  | @cons n m ns ms hnm htail ih =>
    cases start with
    | true =>
      change (∃ w : Word, w.length = m ∧ AvgPHETH.AltLen ms false
        (fun ys => P (w.take n :: List.zipWith (fun n w => w.take n) ns ys))) ↔
        ∃ u : Word, u.length = n ∧ AvgPHETH.AltLen ns false (fun ys => P (u :: ys))
      constructor
      · rintro ⟨w, hw, hrec⟩
        refine ⟨w.take n, by simp [hw, Nat.min_eq_left hnm], ?_⟩
        exact (ih false (fun ys => P (w.take n :: ys))).mp hrec
      · rintro ⟨u, hu, hrec⟩
        obtain ⟨w, hw, ht⟩ := extend_word n m hnm u hu
        refine ⟨w, hw, ?_⟩
        rw [ht]
        exact (ih false (fun ys => P (u :: ys))).mpr hrec
    | false =>
      change (∀ w : Word, w.length = m → AvgPHETH.AltLen ms true
        (fun ys => P (w.take n :: List.zipWith (fun n w => w.take n) ns ys))) ↔
        ∀ u : Word, u.length = n → AvgPHETH.AltLen ns true (fun ys => P (u :: ys))
      constructor
      · intro h u hu
        obtain ⟨w, hw, ht⟩ := extend_word n m hnm u hu
        have hrec := h w hw
        rw [ht] at hrec
        exact (ih true (fun ys => P (u :: ys))).mp hrec
      · intro h w hw
        have hrec := h (w.take n) (by simp [hw, Nat.min_eq_left hnm])
        exact (ih true (fun ys => P (w.take n :: ys))).mpr hrec

private theorem altLen_constant (lengths : List ℕ) (start : Bool) (P : Prop) :
    AvgPHETH.AltLen lengths start (fun _ => P) ↔ P := by
  induction lengths generalizing start with
  | nil => rfl
  | cons n ns ih =>
    cases start with
    | false =>
      simp only [AvgPHETH.AltLen, ih]
      exact ⟨fun h => h (List.replicate n false) (by simp), fun h _ _ => h⟩
    | true =>
      simp only [AvgPHETH.AltLen, ih]
      exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨List.replicate n false, by simp, h⟩⟩

private theorem polynomial_mono (p : Polynomial ℕ) {n m : ℕ} (h : n ≤ m) : p.eval n ≤ p.eval m := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

private theorem pair_length (x y : Word) : (tup [x, y]).length = 2 * x.length + 2 * y.length + 4 := by
  have hbits : ∀ u : Word, (u.flatMap fun b => [true, b]).length = 2 * u.length := by
    intro u
    induction u with
    | nil => simp
    | cons b u ih => simp [ih]; omega
  simp [tup, hbits]
  omega

 theorem polynomial_lengths_mono (ps : List (Polynomial ℕ)) {n m : ℕ} (hnm : n ≤ m) :
    List.Forall₂ (· ≤ ·) (ps.map fun p => p.eval n) (ps.map fun p => p.eval m) := by
  induction ps with
  | nil => exact .nil
  | cons p ps ih => exact .cons (polynomial_mono p hnm) ih

private theorem altLen_dual (lengths : List ℕ) (start : Bool) (V : List Word → Prop) :
    (¬ AvgPHETH.AltLen lengths start V) ↔
      AvgPHETH.AltLen lengths (!start) (fun ys => ¬ V ys) := by
  classical
  induction lengths generalizing start V with
  | nil => simp [AvgPHETH.AltLen]
  | cons n ns ih =>
    cases start with
    | false =>
      simp only [AvgPHETH.AltLen, Bool.not_false, not_forall, exists_prop]
      apply exists_congr
      intro y
      apply and_congr_right
      intro hy
      exact ih true _
    | true =>
      simp only [AvgPHETH.AltLen, Bool.not_true, not_exists, not_and]
      apply forall_congr'
      intro y
      apply imp_congr_right
      intro hy
      exact ih false _

private theorem pair_exists_prop (x y : Word) (P : Word → Word → Prop) :
    (∃ a b : Word, tup [x, y] = tup [a, b] ∧ P a b) ↔ P x y := by
  constructor
  · rintro ⟨a, b, hab, hP⟩
    obtain ⟨ha, hb⟩ := tup_pair_injective hab
    simpa [← ha, ← hb] using hP
  · intro hP; exact ⟨x, y, rfl, hP⟩

end StudentTeacher976.Adaptivity

open StudentTeacher976.Adaptivity

theorem solution (i : ℕ) (hi : 0 < i) (V : OTM) (clock : Polynomial ℕ)
    (ps : List (Polynomial ℕ)) (hlen : ps.length = i)
    (htotal : ∀ s : Word, (V.result (fun _ => false) s (clock.eval s.length)).isSome) :
    {s | ∃ x y : Word, s = tup [x, y] ∧
      ¬ AvgPHETH.AltLen (ps.map fun b => b.eval x.length) false
        (fun ys => V.result (fun _ => false) (tup (x :: y :: ys))
          (clock.eval (tup (x :: y :: ys)).length) = some true)} ∈ StudentTeacher976.Adaptivity.Sigma i := by
  classical
  obtain ⟨M, bound, hMtotal, hcorrect⟩ := padded_residual_verifier V clock ps htotal
  let F : Word → Word → List Word → Prop := fun x y ys =>
    V.result (fun _ => false) (tup (x :: y :: ys)) (clock.eval (tup (x :: y :: ys)).length) = some true
  refine ⟨M, bound, ps, hlen, hMtotal, ?_⟩
  intro s
  change (∃ x y : Word, s = tup [x, y] ∧
      ¬ AvgPHETH.AltLen (ps.map fun b => b.eval x.length) false (F x y)) ↔
    AvgPHETH.AltLen (ps.map fun b => b.eval s.length) true
      (fun ys => M.result (fun _ => false) (tup (s :: ys)) (bound.eval (tup (s :: ys)).length) = some true)
  by_cases hpair : ∃ x y : Word, s = tup [x, y]
  · obtain ⟨x, y, rfl⟩ := hpair
    have hpred : (fun ys => M.result (fun _ => false) (tup (tup [x, y] :: ys))
        (bound.eval (tup (tup [x, y] :: ys)).length) = some true) =
        (fun ys => ¬ F x y (List.zipWith (fun n w => w.take n) (ps.map fun b => b.eval x.length) ys)) := by
      funext ys
      apply propext
      rw [hcorrect]
      exact pair_exists_prop x y _
    rw [pair_exists_prop, hpred]
    have hxlen : x.length ≤ (tup [x, y]).length := by rw [pair_length]; omega
    have htrim := altLen_trim (polynomial_lengths_mono ps hxlen) true (fun ys => ¬ F x y ys)
    exact (altLen_dual _ false (F x y)).trans htrim.symm
  · have hpred : (fun ys => M.result (fun _ => false) (tup (s :: ys))
        (bound.eval (tup (s :: ys)).length) = some true) = (fun _ : List Word => False) := by
      funext ys
      apply propext
      rw [hcorrect]
      constructor
      · rintro ⟨x, y, hxy, hn⟩; exact hpair ⟨x, y, hxy⟩
      · exact False.elim
    rw [hpred, altLen_constant]
    constructor
    · rintro ⟨x, y, hxy, hn⟩; exact hpair ⟨x, y, hxy⟩
    · exact False.elim
