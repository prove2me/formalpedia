-- Prove2me | solution 1 for ReusableMatching.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T20:48:34.493635+00:00
-- url     : https://prove2.me/submissions/9778d6d3-9516-481d-804c-655a713f44f0

import Mathlib
import Definitions.Def_ReusableMatching_OPT
import Definitions.Def_ReusableMatching_matchedPairs
import Definitions.Def_ReusableMatching_reward
import Theorems.Thm_ReusableMatching_lemma_1
import Theorems.Thm_ReusableMatching_lemma_2
import Theorems.Thm_ReusableMatching_lemma_3
import Theorems.Thm_ReusableMatching_lemma_9
import Theorems.Thm_ReusableMatching_theorem_1_min_f

open MeasureTheory

namespace ReusableMatching.RMT1

open ReusableMatching

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

theorem assignment_succ_of_ne (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (t s : ℕ)
    (h : s ≠ t) : assignment I β Y (t + 1) s = assignment I β Y t s := by
  simp only [assignment]
  exact Function.update_of_ne h _ _

theorem assignment_stable (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (s t : ℕ)
    (hst : s < t) : ∀ k, assignment I β Y (t + k) s = assignment I β Y t s := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, assignment_succ_of_ne I β Y _ _ (by omega), ih]

theorem assignment_succ_self (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (t : Fin n) :
    assignment I β Y ((t : ℕ) + 1) t = chooseResource I β Y (assignment I β Y t) t := by
  simp only [assignment, Function.update_self, dif_pos t.isLt]

theorem PR_eq_assignment (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (t : Fin n) (m : ℕ)
    (hm : (t : ℕ) < m) (hmn : m ≤ n) :
    PeriodicReranking I β Y t = assignment I β Y m t := by
  unfold PeriodicReranking
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact assignment_stable I β Y t m hm k

theorem PR_eq_choose (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (t : Fin n) :
    PeriodicReranking I β Y t = chooseResource I β Y (assignment I β Y t) t := by
  rw [PR_eq_assignment I β Y t ((t : ℕ) + 1) (by omega) t.isLt, assignment_succ_self]

omit [Fintype V] in
theorem leastArgmax_mem (C : Finset V) (f : V → ℝ) (v : V) (h : leastArgmax C f = some v) :
    v ∈ C := by
  classical
  unfold leastArgmax at h
  split_ifs at h with hC
  · simp only [Option.some.injEq] at h
    subst h
    have := Finset.min'_mem (C.filter (fun v => f v = C.sup' hC f)) (by
      obtain ⟨v, hv, hvM⟩ := Finset.exists_mem_eq_sup' hC f
      exact ⟨v, Finset.mem_filter.2 ⟨hv, hvM.symm⟩⟩)
    convert (Finset.mem_filter.1 this).1

theorem choose_spec (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (a : ℕ → Option V)
    (t : Fin n) (v : V) (h : chooseResource I β Y a t = some v) :
    (v, t) ∈ I.E ∧ IsAvailable I a v t := by
  classical
  unfold chooseResource at h
  have := leastArgmax_mem _ _ v (by convert h)
  simpa using this

theorem feasible (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) :
    IsFeasibleMatching I (matchedPairs I β Y) := by
  classical
  have hmem : ∀ p, p ∈ matchedPairs I β Y ↔ PeriodicReranking I β Y p.2 = some p.1 := by
    intro p; unfold matchedPairs; simp
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    rw [hmem, PR_eq_choose] at hp
    exact (choose_spec I β Y _ _ _ hp).1
  · rintro ⟨v, s⟩ hp ⟨w, t⟩ hq (hst : s = t)
    subst hst
    rw [hmem] at hp hq
    rw [hp] at hq
    cases hq; rfl
  · rintro ⟨v, s⟩ hp ⟨w, t⟩ hq (hvw : v = w) (hst : s < t)
    subst hvw
    rw [hmem] at hp hq
    rw [PR_eq_choose] at hq
    have hav := (choose_spec I β Y _ _ _ hq).2
    have hs : assignment I β Y t s = some v := by
      rw [← PR_eq_assignment I β Y s t hst (le_of_lt t.isLt)]; exact hp
    exact hav s hst hs

theorem choose_congr (I I' : OBMRRInstance V n) (hr : I'.r = I.r) (hd : I'.d = I.d) (β : ℝ)
    (Y Y' : Seeds V n) (a : ℕ → Option V) (t : Fin n)
    (hE : ∀ v, (v, t) ∈ I.E ↔ (v, t) ∈ I'.E)
    (hY : ∀ v, Y (v, period I t) = Y' (v, period I t)) :
    chooseResource I β Y a t = chooseResource I' β Y' a t := by
  classical
  have hp : period I' t = period I t := by
    unfold period; simp [hd]
  have hav : ∀ v, IsAvailable I a v t ↔ IsAvailable I' a v t := by
    intro v; unfold IsAvailable; rw [hd]
  have hrp : ∀ v, reducedPrice I β Y v t = reducedPrice I' β Y' v t := by
    intro v; unfold reducedPrice; rw [hr, hp, hY]
  unfold chooseResource
  have hC : (Finset.univ.filter (fun v => (v, t) ∈ I.E ∧ IsAvailable I a v t)) =
      (Finset.univ.filter (fun v => (v, t) ∈ I'.E ∧ IsAvailable I' a v t)) := by
    ext v; simp [hE, hav]
  have hf : (fun v => reducedPrice I β Y v t) = (fun v => reducedPrice I' β Y' v t) :=
    funext hrp
  rw [hf]
  convert rfl using 2
  exact hC.symm

theorem online (I I' : OBMRRInstance V n) (hr : I'.r = I.r) (hd : I'.d = I.d) (β : ℝ)
    (Y Y' : Seeds V n) (j : Fin n)
    (hE : ∀ p : V × Fin n, p.2 ≤ j → (p ∈ I.E ↔ p ∈ I'.E))
    (hY : ∀ (v : V) (k : Fin (n + 1)), k ≤ period I j → Y (v, k) = Y' (v, k)) :
    ∀ t : Fin n, t ≤ j → PeriodicReranking I β Y t = PeriodicReranking I' β Y' t := by
  have key : ∀ m : ℕ, m ≤ (j : ℕ) + 1 → assignment I β Y m = assignment I' β Y' m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have ih := ih (by omega)
      have hmn : m < n := by have := j.isLt; omega
      simp only [assignment, dif_pos hmn]
      rw [ih]
      congr 1
      rw [ih] at *
      refine (choose_congr I I' hr hd β Y Y' _ ⟨m, hmn⟩ ?_ ?_)
      · intro v; exact hE (v, ⟨m, hmn⟩) (by show m ≤ (j : ℕ); omega)
      · intro v
        apply hY
        show (m / I.d + 1) ≤ (j : ℕ) / I.d + 1
        have : m / I.d ≤ (j : ℕ) / I.d := Nat.div_le_div_right (by omega)
        omega
  intro t ht
  have ht' : (t : ℕ) ≤ j := ht
  rw [PR_eq_assignment I β Y t ((t : ℕ) + 1) (by omega) t.isLt,
    PR_eq_assignment I' β Y' t ((t : ℕ) + 1) (by omega) t.isLt, key _ (by omega)]

theorem g_pos (β x : ℝ) : 0 < g β x := Real.exp_pos _

theorem g_le_one (β x : ℝ) (hβ : 0 ≤ β) (hx : x ≤ 1) : g β x ≤ 1 := by
  unfold g
  rw [Real.exp_le_one_iff]
  nlinarith

theorem dualAlpha_nonneg (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (i : V) (t : Fin n) :
    0 ≤ dualAlpha I β Y i t := by
  unfold dualAlpha
  split_ifs
  · exact mul_nonneg (I.r_nonneg i) (g_pos _ _).le
  · exact le_rfl

theorem dualBeta_nonneg (I : OBMRRInstance V n) (β : ℝ) (hβ : 0 ≤ β) (Y : Seeds V n)
    (j : Fin n) : 0 ≤ dualBeta I β Y j := by
  unfold dualBeta
  cases PeriodicReranking I β Y j with
  | none => exact le_rfl
  | some i =>
    simp only [Option.elim]
    unfold reducedPrice
    exact mul_nonneg (I.r_nonneg i)
      (sub_nonneg.2 (g_le_one _ _ hβ (Y (i, period I j)).2.2))

theorem crit_mem (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (i : V) (j : Fin n)
    (y1 : unitInterval) (t : Fin n) :
    0 ≤ criticalThreshold I β Y i j y1 t ∧ criticalThreshold I β Y i j y1 t ≤ 1 := by
  classical
  unfold criticalThreshold
  simp only
  generalize hS : {y : ℝ | y ∈ Set.Icc (0 : ℝ) 1 ∧ _} = S
  have hsub : S ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [← hS]; intro y hy; exact hy.1
  rcases S.eq_empty_or_nonempty with h | h
  · rw [h, Real.sSup_empty]; norm_num
  · have hbdd : BddAbove S := ⟨1, fun y hy => (hsub hy).2⟩
    obtain ⟨y, hy⟩ := h
    refine ⟨le_trans (hsub hy).1 (le_csSup hbdd hy), csSup_le ⟨y, hy⟩ fun z hz => (hsub hz).2⟩

theorem competitive (I : OBMRRInstance V n) :
    (5893 / 10000 : ℝ) * OPT I ≤ ∫ Y, reward I (89 / 100) Y ∂(seedMeasure V n) := by
  have hβ : (0 : ℝ) < 89 / 100 := by norm_num
  refine lemma_1 I _ (fun i t => ∫ Y, dualAlpha I (89 / 100) Y i t ∂(seedMeasure V n))
    (fun j => ∫ Y, dualBeta I (89 / 100) Y j ∂(seedMeasure V n)) _ (by norm_num) (by norm_num)
    (fun i t => integral_nonneg fun Y => dualAlpha_nonneg I _ Y i t)
    (fun j => integral_nonneg fun Y => dualBeta_nonneg I _ hβ.le Y j)
    (lemma_2 I _ hβ) ?_
  intro i j hij
  refine lemma_3 I _ hβ i j hij _ (by norm_num) ?_
  intro Y
  obtain ⟨z1, z2, hz1, hz12, hz2, h9⟩ := lemma_9 I (89 / 100) hβ (by norm_num) i j hij Y
  refine le_trans ?_ h9
  have hc := crit_mem I (89 / 100) Y i j 1 j
  have hf := theorem_1_min_f z1 z2 _ hz1 hz12 hz2 hc.1 hc.2
  unfold fBound at hf
  exact mul_le_mul_of_nonneg_left hf.le (I.r_nonneg i) |>.trans' (by rw [mul_comm])

end ReusableMatching.RMT1

open ReusableMatching in
theorem solution {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n) :
    (∀ Y : Seeds V n, IsFeasibleMatching I (matchedPairs I (89 / 100) Y)) ∧
    (∀ I' : OBMRRInstance V n, I'.r = I.r → I'.d = I.d →
      ∀ (Y Y' : Seeds V n) (j : Fin n),
        (∀ p : V × Fin n, p.2 ≤ j → (p ∈ I.E ↔ p ∈ I'.E)) →
        (∀ (v : V) (k : Fin (n + 1)), k ≤ period I j → Y (v, k) = Y' (v, k)) →
        ∀ t : Fin n, t ≤ j →
          PeriodicReranking I (89 / 100) Y t = PeriodicReranking I' (89 / 100) Y' t) ∧
    (5893 / 10000 : ℝ) * OPT I ≤ ∫ Y, reward I (89 / 100) Y ∂(seedMeasure V n) :=
  ⟨fun Y => RMT1.feasible I _ Y,
   fun I' hr hd Y Y' j hE hY => RMT1.online I I' hr hd _ Y Y' j hE hY,
   RMT1.competitive I⟩
