-- Prove2me | solution 1 for collatz_late_mergers_after_first_odd_run_residue_classes
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T20:51:15.927976+00:00
-- url     : https://prove2.me/submissions/5015b6e4-1d26-43a2-8397-11729b7dfe4e

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring

private def traceProgression : ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | 0, a, b => some (a, b)
  | t + 1, a, b =>
    if a % 2 = 0 then
      if b % 2 = 0 then traceProgression t (a / 2) (b / 2)
      else traceProgression t (3 * a) (3 * b + 1)
    else none

private theorem traceProgression_sound (t a b u v : ℕ)
    (h : traceProgression t a b = some (u, v)) (q : ℕ) :
    collatzStep^[t] (a * q + b) = u * q + v := by
  induction t generalizing a b with
  | zero =>
    simp [traceProgression] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | succ t ih =>
    simp only [traceProgression] at h
    split at h
    · rename_i ha
      have ha' : a = 2 * (a / 2) := by omega
      rw [Function.iterate_succ_apply]
      split at h
      · rename_i hb
        have hb' : b = 2 * (b / 2) := by omega
        have hx : a * q + b = 2 * ((a / 2) * q + b / 2) := by
          calc
            a * q + b = (2 * (a / 2)) * q + 2 * (b / 2) := congrArg₂ (· + ·) (congrArg (· * q) ha') hb'
            _ = _ := by ring
        rw [hx]
        simpa [collatzStep] using ih _ _ h
      · rename_i hb
        have hb' : b = 2 * (b / 2) + 1 := by omega
        have hx : a * q + b = 2 * ((a / 2) * q + b / 2) + 1 := by
          calc
            a * q + b = (2 * (a / 2)) * q + (2 * (b / 2) + 1) := congrArg₂ (· + ·) (congrArg (· * q) ha') hb'
            _ = _ := by ring
        have hodd : ¬ Even (a * q + b) := by simp [hx]
        rw [collatzStep, if_neg hodd]
        convert ih _ _ h using 2
        ring
    · contradiction

private def phaseEnd (x : ℕ) : ℕ :=
  let r := (x+1).factorization 2
  3^r*((x+1)/2^r)-1

private def phaseDuration (x : ℕ) : ℕ :=
  (phaseEnd x).factorization 2 + 2*((x+1).factorization 2)

private structure CollatzLateMergerRow where
  period : ℕ
  residue : ℕ
  stride : ℕ
  offset : ℕ
  originalClock : ℕ
  visitorClock : ℕ

private def collatzLateMergerRowValid (c : CollatzLateMergerRow) : Bool :=
  decide (c.residue<c.period ∧ 0<c.offset ∧ c.offset<c.residue ∧ c.stride≤c.period ∧
    c.period%64=0 ∧ c.residue%64=47 ∧ (c.originalClock=13 ∨ c.originalClock=15)) &&
    match traceProgression c.originalClock c.period c.residue with
    | none => false
    | some y => traceProgression c.visitorClock c.stride c.offset == some y

private theorem collatzLateMergerRow_sound (c : CollatzLateMergerRow)
    (hvalid : collatzLateMergerRowValid c=true) (n : ℕ) (hres : n%c.period=c.residue) :
    n%64=47 ∧ ∃ k a b : ℕ, 0<k ∧ k<n ∧ (a=13 ∨ a=15) ∧
      collatzStep^[a] n=collatzStep^[b] k := by
  unfold collatzLateMergerRowValid at hvalid
  obtain ⟨hshape,hmatch⟩ := Bool.and_eq_true_iff.mp hvalid
  obtain ⟨_,hp,hoffset,hstride,hperiod64,hbase64,hclock⟩ := of_decide_eq_true hshape
  let q := n/c.period
  have hn : n=c.period*q+c.residue := by
    rw [Nat.add_comm,←hres]
    exact (Nat.mod_add_div _ _).symm
  have hb : n%64=47 := by
    rw [hn,Nat.add_mod,Nat.mul_mod,hperiod64,hbase64]
    simp
  cases ht : traceProgression c.originalClock c.period c.residue with
  | none => simp [ht] at hmatch
  | some pair =>
    rcases pair with ⟨u,v⟩
    rw [ht] at hmatch
    have ht' : traceProgression c.visitorClock c.stride c.offset=some (u,v) :=
      eq_of_beq hmatch
    refine ⟨hb,c.stride*q+c.offset,c.originalClock,c.visitorClock,by omega,?_,hclock,?_⟩
    · rw [hn]
      exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right q hstride) hoffset
    · rw [hn,traceProgression_sound _ _ _ _ _ ht q,traceProgression_sound _ _ _ _ _ ht' q]

private def collatzLateMergerRows : List CollatzLateMergerRow := [
  ⟨1224440064,524071407,1073741824,459571199,13,49⟩,
  ⟨11019960576,2338056687,8589934592,1822488735,13,54⟩,
  ⟨11019960576,2957834991,8589934592,2305598911,13,54⟩,
  ⟨11019960576,3862823151,8589934592,3011026943,13,54⟩,
  ⟨11019960576,6016620015,8589934592,4689887231,13,54⟩,
  ⟨11019960576,6497574639,8589934592,5064785919,13,54⟩,
  ⟨11019960576,6918369519,8589934592,5392790767,13,54⟩,
  ⟨11019960576,7647666159,8589934592,5961269247,13,54⟩,
  ⟨11019960576,8278858479,8589934592,6453276519,13,54⟩,
  ⟨11019960576,8544237807,8589934592,6660136703,13,54⟩,
  ⟨11019960576,8578203375,8589934592,6686612479,13,54⟩,
  ⟨11019960576,9083530735,8589934592,7080509439,13,54⟩,
  ⟨11019960576,10717660911,8589934592,8354295423,13,54⟩,
  ⟨11019960576,10768609263,8589934592,8394009087,13,54⟩,
  ⟨22039921152,15112762095,17179869184,11780227071,15,56⟩,
  ⟨99179645184,57926895,68719476736,40136319,13,59⟩,
  ⟨99179645184,236993263,68719476736,164207615,13,59⟩,
  ⟨99179645184,818377455,68719476736,567036415,13,59⟩,
  ⟨99179645184,2643882991,68719476736,1831890559,13,59⟩,
  ⟨99179645184,3611896815,68719476736,2502606847,13,59⟩,
  ⟨99179645184,4273203183,68719476736,2960812031,13,59⟩,
  ⟨99179645184,4278013167,68719476736,2964144767,13,59⟩,
  ⟨99179645184,5557880559,68719476736,3850937791,13,59⟩,
  ⟨99179645184,5635018479,68719476736,3904385023,13,59⟩,
  ⟨99179645184,5765693679,68719476736,3994927103,13,59⟩]

private def collatzLateMergerModuli : List (ℕ × ℕ) :=
  collatzLateMergerRows.map (fun c => (c.period,c.residue))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem collatzLateMergerRows_valid :
    collatzLateMergerRows.all collatzLateMergerRowValid=true := by decide +kernel

private theorem collatz_late_mergers_in_second_odd_run_classes (n : ℕ)
    (h : ∃ p : ℕ × ℕ, p∈collatzLateMergerModuli ∧ n%p.1=p.2) :
    n%64=47 ∧ ∃ k a b : ℕ, 0<k ∧ k<n ∧ (a=13 ∨ a=15) ∧
      collatzStep^[a] n=collatzStep^[b] k := by
  obtain ⟨p,hmem,hres⟩ := h
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hmem
  have hvalid := List.all_eq_true.mp collatzLateMergerRows_valid c hc
  exact collatzLateMergerRow_sound c hvalid n hres

private theorem collatz_first_run_duration_of_47_mod_64 (n : ℕ) (hc : n%64=47) :
    phaseDuration n=9 := by
  let m := n/64
  have hn : n+1=16*(4*m+3) := by dsimp [m]; omega
  have hm : ¬ 2∣4*m+3 := by omega
  have hr : (n+1).factorization 2=4 := by
    rw [hn,Nat.factorization_mul (by decide : (16:ℕ)≠0) (by omega),Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hm,add_zero]
    exact Nat.factorization_pow_self (n:=4) Nat.prime_two
  have hw : phaseEnd n=2*(162*m+121) := by
    unfold phaseEnd
    rw [hr,hn]
    norm_num
    omega
  have hob : ¬ 2∣162*m+121 := by omega
  have hs : (phaseEnd n).factorization 2=1 := by
    rw [hw,Nat.factorization_mul (by decide : (2:ℕ)≠0) (by omega),Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hob,add_zero]
    exact Nat.prime_two.factorization_self
  rw [phaseDuration,hs,hr]

theorem solution (n : ℕ) (h : ∃ p : ℕ × ℕ, p∈([(1224440064, 524071407), (11019960576, 2338056687), (11019960576, 2957834991),
      (11019960576, 3862823151), (11019960576, 6016620015), (11019960576, 6497574639),
      (11019960576, 6918369519), (11019960576, 7647666159), (11019960576, 8278858479),
      (11019960576, 8544237807), (11019960576, 8578203375), (11019960576, 9083530735),
      (11019960576, 10717660911), (11019960576, 10768609263), (22039921152, 15112762095),
      (99179645184, 57926895), (99179645184, 236993263), (99179645184, 818377455),
      (99179645184, 2643882991), (99179645184, 3611896815), (99179645184, 4273203183),
      (99179645184, 4278013167), (99179645184, 5557880559), (99179645184, 5635018479),
      (99179645184, 5765693679)] : List (ℕ × ℕ)) ∧ n%p.1=p.2) :
    let r := (n+1).factorization 2
    let w := 3^r*((n+1)/2^r)-1
    w.factorization 2+2*r=9 ∧
      ∃ k a b : ℕ, 0<k ∧ k<n ∧ (a=13 ∨ a=15) ∧ collatzStep^[a] n=collatzStep^[b] k := by
  have hclasses : ∃ p : ℕ × ℕ, p∈collatzLateMergerModuli ∧ n%p.1=p.2 := h
  obtain ⟨h64,hmerge⟩ := collatz_late_mergers_in_second_odd_run_classes n hclasses
  exact ⟨collatz_first_run_duration_of_47_mod_64 n h64,hmerge⟩
