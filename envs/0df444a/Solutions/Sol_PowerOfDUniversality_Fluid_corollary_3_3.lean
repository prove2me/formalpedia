-- Prove2me | solution 1 for PowerOfDUniversality.Fluid.corollary_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T01:50:28.841041+00:00
-- url     : https://prove2.me/submissions/0642961a-c3fd-4208-8890-c924b4806e71

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace
import Theorems.Thm_PowerOfDUniversality_Fluid_proposition_3_1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid.Cor33Aux

open PowerOfDUniversality.Fluid

lemma tailSum_eq_sum (Q : ℕ →₀ ℕ) (m : ℕ) :
    tailSum Q m = Q.sum (fun i a => if m ≤ i then a else 0) := by
  unfold tailSum Finsupp.sum
  rw [Finset.sum_filter]

lemma tailSum_add (Q R : ℕ →₀ ℕ) (m : ℕ) :
    tailSum (Q + R) m = tailSum Q m + tailSum R m := by
  simp only [tailSum_eq_sum]
  rw [Finsupp.sum_add_index']
  · intro i; simp
  · intro i a b; split_ifs <;> simp

lemma tailSum_single (j m : ℕ) :
    tailSum (Finsupp.single j 1) m = if m ≤ j then 1 else 0 := by
  rw [tailSum_eq_sum, Finsupp.sum_single_index]; simp

lemma tailSum_succ (Q : ℕ →₀ ℕ) (m : ℕ) : tailSum Q m = Q m + tailSum Q (m + 1) := by
  simp only [tailSum_eq_sum]
  have h : (fun i a => if m ≤ i then a else 0) =
      (fun (i : ℕ) (a : ℕ) => (if i = m then a else 0) + (if m + 1 ≤ i then a else 0)) := by
    funext i a; split_ifs <;> omega
  rw [h, Finsupp.sum_add, Finsupp.sum_ite_eq']
  by_cases hm : m ∈ Q.support
  · simp [hm]
  · simp only [hm, if_false]
    rw [Finsupp.notMem_support_iff] at hm
    simp [hm]

lemma le_level_iff (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (Q : ℕ →₀ ℕ) (hQ : IsOccupancy N b Q)
    (c : ℕ) (hc1 : 1 ≤ c) (hcN : c ≤ N) (i : ℕ) :
    i ≤ level N Q c ↔ N + 1 ≤ Q i + c := by
  obtain ⟨h0, hanti, _⟩ := hQ
  constructor
  · intro hi
    have hne : (Q.support.filter (fun i => N + 1 ≤ Q i + c)).Nonempty := by
      refine ⟨0, ?_⟩
      rw [Finset.mem_filter, Finsupp.mem_support_iff, h0]
      omega
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup _ hne id
    rw [Finset.mem_filter] at hj
    have hl : level N Q c = j := hjeq
    have := hanti (show i ≤ j by omega)
    omega
  · intro hi
    apply Finset.le_sup (f := id)
    rw [Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨by omega, hi⟩

lemma level_le_b (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (Q : ℕ →₀ ℕ) (hQ : IsOccupancy N b Q)
    (c : ℕ) (hc1 : 1 ≤ c) (hcN : c ≤ N) : ((level N Q c : ℕ) : ℕ∞) ≤ b := by
  by_contra h
  push Not at h
  have h1 := (le_level_iff N hN b Q hQ c hc1 hcN (level N Q c)).mp le_rfl
  have h2 := hQ.2.2 _ h
  omega

lemma add_apply (N : ℕ) (b : ℕ∞) (c : ℕ) (x : Ensemble) (i : ℕ) :
    (addItem N b c x).Q i = x.Q i +
      (if ((level N x.Q c : ℕ) : ℕ∞) < b ∧ i = level N x.Q c + 1 then 1 else 0) := by
  unfold addItem
  by_cases h : ((level N x.Q c : ℕ) : ℕ∞) < b
  · rw [if_pos h]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    by_cases hi : i = level N x.Q c + 1
    · rw [if_pos hi.symm, if_pos ⟨h, hi⟩]
    · rw [if_neg (fun e => hi e.symm), if_neg (fun e => hi e.2)]
  · rw [if_neg h, if_neg (fun e => h e.1)]
    simp

lemma remove_apply (N : ℕ) (k : ℕ) (x : Ensemble) (i : ℕ) :
    (removeItem N k x).Q i = x.Q i -
      (if 1 ≤ level N x.Q k ∧ i = level N x.Q k then 1 else 0) := by
  unfold removeItem
  by_cases h : 1 ≤ level N x.Q k
  · rw [if_pos h]
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
    by_cases hi : i = level N x.Q k
    · rw [if_pos hi.symm, if_pos ⟨h, hi⟩]
    · rw [if_neg (fun e => hi e.symm), if_neg (fun e => hi e.2)]
  · rw [if_neg h, if_neg (fun e => h e.1)]
    simp

lemma occ_add (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (x : Ensemble) (hx : IsOccupancy N b x.Q)
    (c : ℕ) (hc1 : 1 ≤ c) (hcN : c ≤ N) : IsOccupancy N b (addItem N b c x).Q := by
  obtain ⟨I, hI⟩ : ∃ I, level N x.Q c = I := ⟨_, rfl⟩
  have hl := le_level_iff N hN b x.Q hx c hc1 hcN
  have f1 := (hl I).mp (le_of_eq hI.symm)
  have f2 : ¬ N + 1 ≤ x.Q (I + 1) + c := fun h => by have := (hl (I + 1)).mpr h; omega
  obtain ⟨h0, hanti, hzero⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · rw [add_apply, hI, h0]; simp
  · intro i j hij
    show (addItem N b c x).Q j ≤ (addItem N b c x).Q i
    rw [add_apply, add_apply, hI]
    have := hanti hij
    by_cases hj : j = I + 1
    · subst hj
      by_cases hi : i = I + 1
      · subst hi; exact le_rfl
      · have : x.Q I ≤ x.Q i := hanti (by omega)
        split_ifs <;> omega
    · by_cases hi : i = I + 1
      · split_ifs <;> omega
      · split_ifs <;> omega
  · intro i hi
    rw [add_apply, hI, hzero i hi]
    rw [if_neg]
    rintro ⟨h1, rfl⟩
    have : ((I : ℕ∞) + 1) ≤ b := Order.add_one_le_of_lt h1
    push_cast at hi
    exact absurd (lt_of_le_of_lt this hi) (lt_irrefl _)

lemma occ_remove (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (x : Ensemble) (hx : IsOccupancy N b x.Q)
    (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) : IsOccupancy N b (removeItem N k x).Q := by
  obtain ⟨I, hI⟩ : ∃ I, level N x.Q k = I := ⟨_, rfl⟩
  have hl := le_level_iff N hN b x.Q hx k hk1 hkN
  have f1 := (hl I).mp (le_of_eq hI.symm)
  have f2 : ¬ N + 1 ≤ x.Q (I + 1) + k := fun h => by have := (hl (I + 1)).mpr h; omega
  obtain ⟨h0, hanti, hzero⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · rw [remove_apply, hI, h0]; split_ifs <;> omega
  · intro i j hij
    show (removeItem N k x).Q j ≤ (removeItem N k x).Q i
    rw [remove_apply, remove_apply, hI]
    have := hanti hij
    by_cases hi : i = I
    · subst hi
      by_cases hj : j = i
      · subst hj; exact le_rfl
      · have : x.Q j ≤ x.Q (i + 1) := hanti (by omega)
        split_ifs <;> omega
    · split_ifs <;> omega
  · intro i hi
    rw [remove_apply, hzero i hi]
    simp

lemma uniformPos_bounds (N : ℕ) (hN : 1 ≤ N) (x : ℝ) : 1 ≤ uniformPos N x ∧ uniformPos N x ≤ N := by
  unfold uniformPos
  exact ⟨le_min (by omega) hN, min_le_right _ _⟩

open Classical in
/-- Under the S-coupling, two systems whose dispatch choices are ordered (`pol₁ ≤ pol₂`
positionwise) and whose initial states are ordered stay ordered as in (3.1) after every event
(iterating Proposition 3.1). -/
lemma ordered_seq (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (pol₁ pol₂ : Scheme)
    (hp₁ : ∀ j Q u, 1 ≤ pol₁ j Q u) (hp₂ : ∀ j Q u, pol₂ j Q u ≤ N)
    (hle : ∀ j Q Q' u, pol₁ j Q u ≤ pol₂ j Q' u)
    (Q₁ Q₂ : ℕ →₀ ℕ) (hQ₁ : IsOccupancy N b Q₁) (hQ₂ : IsOccupancy N b Q₂)
    (h0 : ∀ m : ℕ, 1 ≤ m → tailSum Q₁ m ≤ tailSum Q₂ m) (ξ : ℕ → ℕ → ℝ) (n : ℕ) :
    IsOccupancy N b (eventState N b lam pol₁ Q₁ ξ n).Q ∧
    IsOccupancy N b (eventState N b lam pol₂ Q₂ ξ n).Q ∧
    StackOrdered (eventState N b lam pol₁ Q₁ ξ n) (eventState N b lam pol₂ Q₂ ξ n) := by
  induction n with
  | zero =>
    refine ⟨hQ₁, hQ₂, ?_⟩
    intro m hm
    simp only [eventState]
    have := h0 m hm
    omega
  | succ n ih =>
    obtain ⟨o1, o2, hd⟩ := ih
    set x := eventState N b lam pol₁ Q₁ ξ n with hx
    set y := eventState N b lam pol₂ Q₂ ξ n with hy
    have e1 : eventState N b lam pol₁ Q₁ ξ (n + 1) =
        if IsArrival N lam (ξ (n + 1)) then addItem N b (pol₁ (n + 1) x.Q (ξ (n + 1))) x
        else removeItem N (uniformPos N (ξ (n + 1) 2)) x := by
      simp only [eventState, step, hx]
    have e2 : eventState N b lam pol₂ Q₂ ξ (n + 1) =
        if IsArrival N lam (ξ (n + 1)) then addItem N b (pol₂ (n + 1) y.Q (ξ (n + 1))) y
        else removeItem N (uniformPos N (ξ (n + 1) 2)) y := by
      simp only [eventState, step, hy]
    rw [e1, e2]
    have P31 := proposition_3_1 N hN b hb x y o1 o2 hd
    obtain ⟨u1, u2⟩ := uniformPos_bounds N hN (ξ (n + 1) 2)
    by_cases harr : IsArrival N lam (ξ (n + 1))
    · simp only [harr, if_true]
      have a1 := hp₁ (n + 1) x.Q (ξ (n + 1))
      have a2 := hp₂ (n + 1) y.Q (ξ (n + 1))
      have a3 := hle (n + 1) x.Q y.Q (ξ (n + 1))
      have a4 := hp₁ (n + 1) y.Q (ξ (n + 1))
      have a5 := hp₂ (n + 1) x.Q (ξ (n + 1))
      exact ⟨occ_add N hN b x o1 _ a1 (le_trans a3 a2), occ_add N hN b y o2 _ (le_trans a4 (hle (n + 1) y.Q y.Q (ξ (n + 1)))) a2,
        P31.2 _ _ a1 a3 a2⟩
    · simp only [harr, if_false]
      exact ⟨occ_remove N hN b x o1 _ u1 u2, occ_remove N hN b y o2 _ u1 u2, P31.1 _ u1 u2⟩

end PowerOfDUniversality.Fluid.Cor33Aux

open PowerOfDUniversality.Fluid PowerOfDUniversality.Fluid.Cor33Aux

theorem solution (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (hlam : 0 ≤ lam)
    (n : ℕ) (hn : n + 1 ≤ N) (pol : Scheme) (hpol : IsCJSQ n pol)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (sysJ sysC sysM : System P N b lam) (hJC : sysJ.ξ = sysC.ξ) (hJM : sysJ.ξ = sysM.ξ)
    (h0JC : ∀ ω (m : ℕ), 1 ≤ m → tailSum (sysJ.Q0 ω) m ≤ tailSum (sysC.Q0 ω) m)
    (h0CM : ∀ ω (m : ℕ), 1 ≤ m → tailSum (sysC.Q0 ω) m ≤ tailSum (sysM.Q0 ω) m) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ m : ℕ, 1 ≤ m →
      ((tailSum (sysJ.occ jsq ω t) m : ℤ) - tailSum (sysM.occ (mjsq n) ω t) (m + 1)
          + sysJ.overflow jsq ω t - sysM.overflow (mjsq n) ω t
        ≤ (sysC.occ pol ω t m : ℤ)) ∧
      ((sysC.occ pol ω t m : ℤ)
        ≤ (tailSum (sysM.occ (mjsq n) ω t) m : ℤ) - tailSum (sysJ.occ jsq ω t) (m + 1)
          + sysM.overflow (mjsq n) ω t - sysJ.overflow jsq ω t) := by
  refine Filter.Eventually.of_forall (fun ω t _ m hm => ?_)
  have mC : sysC.marks ω = sysJ.marks ω := by funext j r; simp [System.marks, hJC]
  have mM : sysM.marks ω = sysJ.marks ω := by funext j r; simp [System.marks, hJM]
  have cC : sysC.count ω t = sysJ.count ω t := by simp only [System.count, mC]
  have cM : sysM.count ω t = sysJ.count ω t := by simp only [System.count, mM]
  have hJC' := (ordered_seq N hN b hb lam jsq pol (fun _ _ _ => le_rfl)
    (fun j Q u => le_trans (hpol.1 j Q u).2 hn) (fun j Q Q' u => (hpol.1 j Q' u).1)
    (sysJ.Q0 ω) (sysC.Q0 ω) (sysJ.isOccupancy_Q0 ω) (sysC.isOccupancy_Q0 ω) (h0JC ω)
    (sysJ.marks ω) (sysJ.count ω t)).2.2
  have hCM' := (ordered_seq N hN b hb lam pol (mjsq n) (fun j Q u => (hpol.1 j Q u).1)
    (fun _ _ _ => hn) (fun j Q Q' u => (hpol.1 j Q u).2)
    (sysC.Q0 ω) (sysM.Q0 ω) (sysC.isOccupancy_Q0 ω) (sysM.isOccupancy_Q0 ω) (h0CM ω)
    (sysJ.marks ω) (sysJ.count ω t)).2.2
  have e1 := hJC' m hm
  have e2 := hJC' (m + 1) (by omega)
  have e3 := hCM' m hm
  have e4 := hCM' (m + 1) (by omega)
  have sC := tailSum_succ (eventState N b lam pol (sysC.Q0 ω) (sysJ.marks ω) (sysJ.count ω t)).Q m
  simp only [System.occ, System.overflow, System.stateSeq, cC, cM, mC, mM]
  push_cast
  omega
