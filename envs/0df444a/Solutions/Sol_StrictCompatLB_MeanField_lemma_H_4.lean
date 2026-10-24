-- Prove2me | solution 1 for StrictCompatLB.MeanField.lemma_H_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:36:32.879473+00:00
-- url     : https://prove2.me/submissions/0eeb6c78-5b2d-4182-abf2-026b43e8f729

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory Finset
open scoped ENNReal

namespace StrictCompatLB.MeanField.H4

open StrictCompatLB.MeanField

/-- A set is petite as soon as some fixed number of steps reaches a fixed state `x₀` with
probability bounded below uniformly on the set. -/
lemma petite_of_uniform {S : Type*} [DecidableEq S] (K : S → S → ℝ) (C : Set S) (x₀ : S)
    (L : ℕ) (c : ℝ) (hc : 0 < c) (h : ∀ z ∈ C, c ≤ stepProb K L z x₀) : IsPetite K C := by
  refine ⟨fun n => if n = L then 1 else 0, fun n => by dsimp only; split_ifs <;> norm_num,
    hasSum_ite_eq L 1, fun x => if x = x₀ then ENNReal.ofReal c else 0, ?_, ?_⟩
  · rw [tsum_ite_eq]; simpa using hc
  · intro z hz A
    have hL : (∑' x, A.indicator (fun x => if x = x₀ then ENNReal.ofReal c else 0) x) =
        A.indicator (fun _ => ENNReal.ofReal c) x₀ := by
      have : A.indicator (fun x => if x = x₀ then ENNReal.ofReal c else 0) =
          fun x => if x = x₀ then A.indicator (fun _ => ENNReal.ofReal c) x₀ else 0 := by
        funext x
        by_cases hx : x = x₀
        · subst hx; simp [Set.indicator]
        · simp [Set.indicator, hx]
      rw [this, tsum_ite_eq]
    rw [hL]
    by_cases hA : x₀ ∈ A
    · rw [Set.indicator_of_mem hA]
      calc ENNReal.ofReal c ≤ ENNReal.ofReal (stepProb K L z x₀) := ENNReal.ofReal_le_ofReal (h z hz)
        _ = A.indicator (fun y => ENNReal.ofReal (stepProb K L z y)) x₀ := by
            rw [Set.indicator_of_mem hA]
        _ ≤ ∑' x, A.indicator (fun y => ENNReal.ofReal (stepProb K L z y)) x := ENNReal.le_tsum _
        _ = ENNReal.ofReal (if L = L then 1 else 0) *
              ∑' x, A.indicator (fun y => ENNReal.ofReal (stepProb K L z y)) x := by simp
        _ ≤ _ := ENNReal.le_tsum (f := fun n => ENNReal.ofReal (if n = L then 1 else 0) *
              ∑' x, A.indicator (fun y => ENNReal.ofReal (stepProb K n z y)) x) L
    · rw [Set.indicator_of_notMem hA]; exact bot_le

variable (lam : ℝ) (d : ℕ) (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)

lemma jsqdRoute_nonneg (w : Fin (M N)) (z : Fin N → ℕ) (v : Fin N) :
    0 ≤ jsqdRoute M G N d w z v := by
  unfold jsqdRoute
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro U _
  split_ifs
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact le_refl _

lemma kernel_nonneg (hlam : 0 < lam) (z z' : Fin N → ℕ) : 0 ≤ jsqdKernel lam d M G N z z' := by
  unfold jsqdKernel lbKernel
  have h1 : 0 ≤ lam / (lam + 1) * (1 / (M N : ℝ)) :=
    mul_nonneg (div_nonneg hlam.le (by linarith)) (div_nonneg zero_le_one (Nat.cast_nonneg _))
  have h2 : 0 ≤ 1 / (lam + 1) * (1 / (N : ℝ)) :=
    mul_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg zero_le_one (Nat.cast_nonneg _))
  apply add_nonneg
  · apply mul_nonneg h1
    apply Finset.sum_nonneg; intro w _
    apply Finset.sum_nonneg; intro v _
    apply mul_nonneg (jsqdRoute_nonneg d M G N w z v)
    split_ifs <;> norm_num
  · apply mul_nonneg h2
    apply Finset.sum_nonneg; intro v _
    split_ifs <;> norm_num

lemma kernel_depart (hlam : 0 < lam) (y : Fin N → ℕ) (v : Fin N) :
    1 / (lam + 1) * (1 / (N : ℝ)) ≤ jsqdKernel lam d M G N y (depart y v) := by
  unfold jsqdKernel lbKernel
  have h1 : 0 ≤ lam / (lam + 1) * (1 / (M N : ℝ)) :=
    mul_nonneg (div_nonneg hlam.le (by linarith)) (div_nonneg zero_le_one (Nat.cast_nonneg _))
  have h2 : 0 ≤ 1 / (lam + 1) * (1 / (N : ℝ)) :=
    mul_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg zero_le_one (Nat.cast_nonneg _))
  have hA : 0 ≤ lam / (lam + 1) * (1 / (M N : ℝ)) *
      ∑ w : Fin (M N), ∑ x : Fin N, jsqdRoute M G N d w y x *
        (if depart y v = arrive y x then (1 : ℝ) else 0) := by
    apply mul_nonneg h1
    apply Finset.sum_nonneg; intro w _
    apply Finset.sum_nonneg; intro x _
    apply mul_nonneg (jsqdRoute_nonneg d M G N w y x)
    split_ifs <;> norm_num
  have hB : (1 : ℝ) ≤ ∑ v' : Fin N, (if depart y v = depart y v' then (1 : ℝ) else 0) := by
    calc (1 : ℝ) = (if depart y v = depart y v then (1 : ℝ) else 0) := by simp
      _ ≤ _ := Finset.single_le_sum (f := fun v' => if depart y v = depart y v' then (1 : ℝ) else 0)
          (fun i _ => by split_ifs <;> norm_num) (mem_univ v)
  nlinarith

lemma kernel_supp (z' y : Fin N → ℕ)
    (hy : y ∉ Fintype.piFinset (fun u => Finset.range (z' u + 2))) :
    jsqdKernel lam d M G N y z' = 0 := by
  unfold jsqdKernel lbKernel
  have hex : ∃ u, z' u + 2 ≤ y u := by
    by_contra hc
    push Not at hc
    apply hy
    rw [Fintype.mem_piFinset]
    intro u; simp only [mem_range]; exact hc u
  obtain ⟨u, hu⟩ := hex
  have ha : ∀ v, z' ≠ arrive y v := by
    intro v h
    have := congrFun h u
    unfold arrive at this
    by_cases huv : u = v
    · subst huv; simp at this; omega
    · rw [Function.update_of_ne huv] at this; omega
  have hd : ∀ v, z' ≠ depart y v := by
    intro v h
    have := congrFun h u
    unfold depart at this
    by_cases huv : u = v
    · subst huv; simp at this; omega
    · rw [Function.update_of_ne huv] at this; omega
  simp [ha, hd]

lemma stepProb_nonneg (hlam : 0 < lam) (n : ℕ) (z y : Fin N → ℕ) :
    0 ≤ stepProb (jsqdKernel lam d M G N) n z y := by
  induction n generalizing y with
  | zero => simp only [stepProb]; split_ifs <;> norm_num
  | succ n ih =>
    simp only [stepProb]
    exact tsum_nonneg (fun w => mul_nonneg (ih w) (kernel_nonneg lam d M G N hlam w y))

lemma stepProb_succ_ge (hlam : 0 < lam) (n : ℕ) (z y w : Fin N → ℕ) :
    stepProb (jsqdKernel lam d M G N) n z w * jsqdKernel lam d M G N w y ≤
      stepProb (jsqdKernel lam d M G N) (n + 1) z y := by
  simp only [stepProb]
  refine Summable.le_tsum (f := fun x => stepProb (jsqdKernel lam d M G N) n z x *
      jsqdKernel lam d M G N x y) ?_ w ?_
  · apply summable_of_ne_finset_zero (s := Fintype.piFinset (fun u => Finset.range (y u + 2)))
    intro b hb
    rw [kernel_supp lam d M G N y b hb, mul_zero]
  · intro j _
    exact mul_nonneg (stepProb_nonneg lam d M G N hlam n z j) (kernel_nonneg lam d M G N hlam j y)

lemma stepProb_down (hlam : 0 < lam) (n : ℕ) :
    ∀ z y : Fin N → ℕ, (∀ u, y u ≤ z u) → ∑ u, z u = ∑ u, y u + n →
      (1 / (lam + 1) * (1 / (N : ℝ))) ^ n ≤ stepProb (jsqdKernel lam d M G N) n z y := by
  have hβ : 0 ≤ 1 / (lam + 1) * (1 / (N : ℝ)) :=
    mul_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg zero_le_one (Nat.cast_nonneg _))
  induction n with
  | zero =>
    intro z y hle hsum
    have : ∀ u ∈ (univ : Finset (Fin N)), y u = z u :=
      (Finset.sum_eq_sum_iff_of_le (fun u _ => hle u)).mp (by simpa using hsum.symm)
    have hyz : y = z := funext (fun u => this u (mem_univ u))
    subst hyz
    simp [stepProb]
  | succ n ih =>
    intro z y hle hsum
    have hex : ∃ v, y v < z v := by
      by_contra hc
      push Not at hc
      have : ∑ u, z u ≤ ∑ u, y u := Finset.sum_le_sum (fun u _ => hc u)
      omega
    obtain ⟨v, hv⟩ := hex
    set y' := arrive y v with hy'
    have hle' : ∀ u, y' u ≤ z u := by
      intro u
      by_cases huv : u = v
      · subst huv; simp [hy', arrive]; omega
      · simp only [hy', arrive]; rw [Function.update_of_ne huv]; exact hle u
    have hsum' : ∑ u, z u = ∑ u, y' u + n := by
      have : ∑ u, y' u = ∑ u, y u + 1 := by
        simp only [hy', arrive]
        rw [Finset.sum_update_of_mem (mem_univ v), ← Finset.add_sum_erase _ _ (mem_univ v)]
        rw [Finset.sdiff_singleton_eq_erase]
        ring
      omega
    have hdep : depart y' v = y := by
      simp only [hy', arrive, depart]
      funext u
      by_cases huv : u = v
      · subst huv; simp
      · simp [Function.update_of_ne huv]
    have h1 := ih z y' hle' hsum'
    have h2 := kernel_depart lam d M G N hlam y' v
    rw [hdep] at h2
    have h3 := stepProb_succ_ge lam d M G N hlam n z y y'
    rw [pow_succ]
    calc _ ≤ stepProb (jsqdKernel lam d M G N) n z y' * jsqdKernel lam d M G N y' y :=
          mul_le_mul h1 h2 hβ (stepProb_nonneg lam d M G N hlam n z y')
      _ ≤ _ := h3

lemma stepProb_zero_ge (hlam : 0 < lam) (hN : 1 ≤ N) (z : Fin N → ℕ) :
    ∀ m, ∑ u, z u ≤ m →
      (1 / (lam + 1) * (1 / (N : ℝ))) ^ m ≤ stepProb (jsqdKernel lam d M G N) m z 0 := by
  have hβ : 0 ≤ 1 / (lam + 1) * (1 / (N : ℝ)) :=
    mul_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg zero_le_one (Nat.cast_nonneg _))
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k with
  | zero =>
    exact stepProb_down lam d M G N hlam _ z 0 (fun u => Nat.zero_le _) (by simp)
  | succ k ih =>
    have h1 := ih (by omega)
    have v : Fin N := ⟨0, hN⟩
    have h2 := kernel_depart lam d M G N hlam (0 : Fin N → ℕ) v
    have hd0 : depart (0 : Fin N → ℕ) v = 0 := by
      funext u; simp [depart, Function.update_apply]
    rw [hd0] at h2
    have h3 := stepProb_succ_ge lam d M G N hlam (∑ u, z u + k) z 0 0
    rw [← add_assoc, pow_succ]
    calc _ ≤ _ := mul_le_mul h1 h2 hβ (stepProb_nonneg lam d M G N hlam _ z 0)
      _ ≤ _ := h3

lemma sum_Qcount {N : ℕ} (z : Fin N → ℕ) :
    ∑ i ∈ Ico 1 (maxLen z + 1), (Qcount z i : ℝ) = ((∑ u, z u : ℕ) : ℝ) := by
  have : ∑ i ∈ Ico 1 (maxLen z + 1), Qcount z i = ∑ u, z u := by
    unfold Qcount
    simp only [card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    have hu : z u ≤ maxLen z := Finset.le_sup (f := z) (mem_univ u)
    rw [← Finset.card_filter]
    have : (Ico 1 (maxLen z + 1)).filter (fun i => i ≤ z u) = Ico 1 (z u + 1) := by
      ext i; simp only [mem_filter, mem_Ico]; omega
    rw [this, Nat.card_Ico]; omega
  exact_mod_cast this

end StrictCompatLB.MeanField.H4

open StrictCompatLB.MeanField StrictCompatLB.MeanField.H4 in
theorem solution (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (d : ℕ) (hd : 1 ≤ d)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (Γ : ℝ) (hΓ : 0 ≤ Γ) :
    IsPetite (jsqdKernel lam d M G N) (CGamma N Γ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    apply petite_of_uniform _ _ 0 0 1 one_pos
    intro z _
    have : z = 0 := funext (fun u => Fin.elim0 u)
    subst this
    simp [stepProb]
  · apply petite_of_uniform _ _ 0 ⌊Γ⌋₊ ((1 / (lam + 1) * (1 / (N : ℝ))) ^ ⌊Γ⌋₊)
    · apply pow_pos
      apply mul_pos (div_pos one_pos (by linarith))
      exact div_pos one_pos (by exact_mod_cast hN)
    · intro z hz
      apply stepProb_zero_ge lam d M G N hlam0 hN z
      unfold CGamma at hz
      simp only [Set.mem_setOf_eq] at hz
      rw [sum_Qcount] at hz
      exact Nat.le_floor hz
