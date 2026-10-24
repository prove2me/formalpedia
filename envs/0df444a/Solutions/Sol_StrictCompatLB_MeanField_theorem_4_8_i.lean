-- Prove2me | solution 1 for StrictCompatLB.MeanField.theorem_4_8_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:54:50.004539+00:00
-- url     : https://prove2.me/submissions/21b46ceb-6f91-487f-ac09-8a5a7603e365

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model
import Theorems.Thm_StrictCompatLB_MeanField_lemma_H_5

open Filter Topology MeasureTheory Finset
open scoped ENNReal

namespace StrictCompatLB.MeanField.T48

open StrictCompatLB.MeanField

/-! ### Generic facts for kernels with finitely supported columns -/

section generic
variable {S : Type*} (K : S → S → ℝ)

/-- Every column `z ↦ K z y` has finite support. -/
def ColFin : Prop := ∀ y, ∃ s : Finset S, ∀ z ∉ s, K z y = 0

lemma col_summable (hc : ColFin K) (p : S → ℝ) (y : S) : Summable (fun z => p z * K z y) := by
  obtain ⟨s, hs⟩ := hc y
  exact summable_of_ne_finset_zero (s := s) (fun z hz => by rw [hs z hz, mul_zero])

lemma push_hasSum (hK0 : ∀ z y, 0 ≤ K z y) (hrow : ∀ z, HasSum (K z) 1) (hc : ColFin K)
    (p : S → ℝ) (hp0 : ∀ z, 0 ≤ p z) {a : ℝ} (hp : HasSum p a) :
    HasSum (fun y => ∑' z, p z * K z y) a := by
  set f : S × S → ℝ := fun x => p x.1 * K x.1 x.2 with hfdef
  have hf0 : 0 ≤ f := fun x => mul_nonneg (hp0 _) (hK0 _ _)
  have hrowf : ∀ z, HasSum (fun y => f (z, y)) (p z) := by
    intro z
    have := (hrow z).mul_left (p z)
    simpa [f] using this
  have e : (fun z => ∑' y, f (z, y)) = p := funext (fun z => (hrowf z).tsum_eq)
  have hfs : Summable f := (summable_prod_of_nonneg hf0).mpr
    ⟨fun z => (hrowf z).summable, by rw [e]; exact hp.summable⟩
  have hfa : HasSum f a := by
    have h1 := hfs.hasSum
    rw [hfs.tsum_prod' (fun z => (hrowf z).summable)] at h1
    have h2 : (∑' z, ∑' y, f (z, y)) = a := by rw [e]; exact hp.tsum_eq
    rw [h2] at h1
    exact h1
  have hg : HasSum (f ∘ (Equiv.prodComm S S)) a := (Equiv.hasSum_iff _).mpr hfa
  exact hg.prod_fiberwise (fun y => by
    have := (col_summable K hc p y).hasSum
    simpa [f, Function.comp] using this)

lemma pos_part_stat (hK0 : ∀ z y, 0 ≤ K z y) (hrow : ∀ z, HasSum (K z) 1) (hc : ColFin K)
    (ν : S → ℝ) (hνs : Summable ν) (hνK : ∀ y, HasSum (fun z => ν z * K z y) (ν y)) :
    ∀ y, HasSum (fun z => max (ν z) 0 * K z y) (max (ν y) 0) := by
  set νp : S → ℝ := fun z => max (ν z) 0 with hνp
  have hνp0 : ∀ z, 0 ≤ νp z := fun z => le_max_right _ _
  have hνps : Summable νp := Summable.of_nonneg_of_le hνp0
    (fun z => max_le (le_abs_self _) (abs_nonneg _)) hνs.abs
  set r : S → ℝ := fun y => ∑' z, νp z * K z y with hr
  have hrs : HasSum r (∑' z, νp z) := push_hasSum K hK0 hrow hc νp hνp0 hνps.hasSum
  have hle : ∀ y, νp y ≤ r y := by
    intro y
    apply max_le
    · rw [← (hνK y).tsum_eq]
      exact Summable.tsum_le_tsum
        (fun z => mul_le_mul_of_nonneg_right (le_max_left _ _) (hK0 _ _))
        (col_summable K hc ν y) (col_summable K hc νp y)
    · exact tsum_nonneg (fun z => mul_nonneg (hνp0 z) (hK0 z y))
  have hdiff : HasSum (fun y => r y - νp y) 0 := by
    have := hrs.sub hνps.hasSum
    simpa using this
  have hz := (hasSum_zero_iff_of_nonneg (fun y => sub_nonneg.mpr (hle y))).mp hdiff
  intro y
  have : r y = νp y := by
    have := congrFun hz y
    simp only [Pi.zero_apply] at this
    linarith
  have h := (col_summable K hc νp y).hasSum
  rw [show (∑' z, νp z * K z y) = r y from rfl, this] at h
  exact h

end generic

/-! ### Facts about the JSQ(d) kernel -/

section kernel
variable (lam : ℝ) (d : ℕ) (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)

/-- Total number of tasks. -/
def tot {N : ℕ} (z : Fin N → ℕ) : ℕ := ∑ u, z u

lemma tot_update {N : ℕ} (z : Fin N → ℕ) (v : Fin N) (c : ℕ) :
    tot (Function.update z v c) + z v = tot z + c := by
  unfold tot
  rw [Finset.sum_update_of_mem (mem_univ v), ← Finset.add_sum_erase _ _ (mem_univ v),
    Finset.sdiff_singleton_eq_erase]
  ring

lemma tot_arrive {N : ℕ} (z : Fin N → ℕ) (v : Fin N) : tot (arrive z v) = tot z + 1 := by
  have := tot_update z v (z v + 1); unfold arrive; omega

lemma tot_depart {N : ℕ} (z : Fin N → ℕ) (v : Fin N) : tot (depart z v) ≤ tot z := by
  have := tot_update z v (z v - 1); unfold depart; omega

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

/-- `K y z' ≠ 0` forces `z'` to be `y ± e_v`, so the total changes by at most one. -/
lemma kernel_zero_of_tot (z' y : Fin N → ℕ) (h : tot y + 1 < tot z') :
    jsqdKernel lam d M G N y z' = 0 := by
  unfold jsqdKernel lbKernel
  have ha : ∀ v, z' ≠ arrive y v := by
    intro v hv; have := tot_arrive y v; rw [← hv] at this; omega
  have hd : ∀ v, z' ≠ depart y v := by
    intro v hv; have := tot_depart y v; rw [← hv] at this; omega
  simp [ha, hd]

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

lemma kernel_colfin : ColFin (jsqdKernel lam d M G N) := fun y =>
  ⟨Fintype.piFinset (fun u => Finset.range (y u + 2)), fun z hz => kernel_supp lam d M G N y z hz⟩

lemma kernel_hasSum (V : (Fin N → ℕ) → ℝ) (z : Fin N → ℕ) :
    HasSum (fun z' => jsqdKernel lam d M G N z z' * V z')
      (lam / (lam + 1) * (1 / (M N : ℝ)) *
        ∑ w : Fin (M N), ∑ v : Fin N, jsqdRoute M G N d w z v * V (arrive z v) +
      1 / (lam + 1) * (1 / (N : ℝ)) * ∑ v : Fin N, V (depart z v)) := by
  set A := lam / (lam + 1) * (1 / (M N : ℝ))
  set Bc := 1 / (lam + 1) * (1 / (N : ℝ))
  have hfun : (fun z' => jsqdKernel lam d M G N z z' * V z') = fun z' =>
      (∑ w : Fin (M N), ∑ v : Fin N, A * jsqdRoute M G N d w z v *
        (if z' = arrive z v then V (arrive z v) else 0)) +
      ∑ v : Fin N, Bc * (if z' = depart z v then V (depart z v) else 0) := by
    funext z'
    simp only [jsqdKernel, lbKernel]
    rw [add_mul]
    simp only [Finset.mul_sum, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl; intro w _
      apply Finset.sum_congr rfl; intro v _
      split_ifs with h
      · subst h; ring
      · ring
    · apply Finset.sum_congr rfl; intro v _
      split_ifs with h
      · subst h; ring
      · ring
  rw [hfun]
  have e : A * ∑ w : Fin (M N), ∑ v : Fin N, jsqdRoute M G N d w z v * V (arrive z v) +
      Bc * ∑ v : Fin N, V (depart z v) =
      (∑ w : Fin (M N), ∑ v : Fin N, A * jsqdRoute M G N d w z v * V (arrive z v)) +
        ∑ v : Fin N, Bc * V (depart z v) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro w _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro v _
    ring
  rw [e]
  exact (hasSum_sum (fun w _ => hasSum_sum (fun v _ =>
      (hasSum_ite_eq (arrive z v) (V (arrive z v))).mul_left (A * jsqdRoute M G N d w z v)))).add
      (hasSum_sum (fun v _ => (hasSum_ite_eq (depart z v) (V (depart z v))).mul_left Bc))

lemma route_sum_eq_one (hd : 1 ≤ d) (w : Fin (M N)) (hne : (nbrW M G N w).Nonempty)
    (z : Fin N → ℕ) : ∑ v : Fin N, jsqdRoute M G N d w z v = 1 := by
  unfold jsqdRoute
  rw [← Finset.mul_sum, Finset.sum_comm]
  set n := (nbrW M G N w).card with hn
  have hn1 : 1 ≤ n := hne.card_pos
  set s := (nbrW M G N w).powersetCard (min d n)
  have hsc : s.card = Nat.choose n (min d n) := by
    simp only [s, n, Finset.card_powersetCard]
  have hU : ∀ U ∈ s, ∑ v : Fin N,
      (if v ∈ argminSet U z then ((argminSet U z).card : ℝ)⁻¹ else 0) = 1 := by
    intro U hU
    rw [Finset.mem_powersetCard] at hU
    have hUne : U.Nonempty := by
      rw [← Finset.card_pos, hU.2]; exact lt_min (by omega) (by omega)
    obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image U z hUne
    have hAne : (argminSet U z).Nonempty := ⟨u, by
      simp only [argminSet, mem_filter]; exact ⟨hu, hmin⟩⟩
    rw [Finset.sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast hAne.card_pos.ne')
  rw [Finset.sum_congr rfl hU, sum_const, nsmul_eq_mul, mul_one, hsc]
  have : (0 : ℝ) < Nat.choose n (min d n) := by
    exact_mod_cast Nat.choose_pos (min_le_right _ _)
  exact inv_mul_cancel₀ this.ne'

lemma kernel_row (hlam : 0 < lam) (hd : 1 ≤ d) (hN : 1 ≤ N) (hM : 0 < M N)
    (hne : ∀ w, (nbrW M G N w).Nonempty) (z : Fin N → ℕ) :
    HasSum (jsqdKernel lam d M G N z) 1 := by
  have h := kernel_hasSum lam d M G N (fun _ => 1) z
  simp only [mul_one] at h
  convert h using 1
  simp only [route_sum_eq_one d M G N hd _ (hne _), sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  have : (0 : ℝ) < N := by exact_mod_cast hN
  have : (0 : ℝ) < M N := by exact_mod_cast hM
  field_simp

/-- A nonnegative stationary measure that vanishes at the empty state vanishes everywhere. -/
lemma vanish (hlam : 0 < lam) (hN : 1 ≤ N) (ν : (Fin N → ℕ) → ℝ) (hν0 : ∀ z, 0 ≤ ν z)
    (hνK : ∀ y, HasSum (fun z => ν z * jsqdKernel lam d M G N z y) (ν y)) (h0 : ν 0 = 0) :
    ∀ z, ν z = 0 := by
  have hβ : 0 < 1 / (lam + 1) * (1 / (N : ℝ)) :=
    mul_pos (div_pos one_pos (by linarith)) (div_pos one_pos (by exact_mod_cast hN))
  have key : ∀ n, ∀ z : Fin N → ℕ, tot z = n → ν z = 0 := by
    intro n
    induction n with
    | zero =>
      intro z hz
      have : z = 0 := by
        funext u
        have : z u ≤ tot z := Finset.single_le_sum (f := z) (fun _ _ => Nat.zero_le _) (mem_univ u)
        simp only [Pi.zero_apply]; omega
      rw [this, h0]
    | succ n ih =>
      intro z hz
      have hex : ∃ v, 1 ≤ z v := by
        by_contra hc
        push Not at hc
        have : tot z = 0 := Finset.sum_eq_zero (fun u _ => by have := hc u; omega)
        omega
      obtain ⟨v, hv⟩ := hex
      set y := depart z v
      have hty : tot y = n := by
        have := tot_update z v (z v - 1)
        simp only [y, depart]; omega
      have hy0 := ih y hty
      have hle := le_hasSum (hνK y) z (fun j _ => mul_nonneg (hν0 j) (kernel_nonneg lam d M G N hlam j y))
      rw [hy0] at hle
      have hk := kernel_depart lam d M G N hlam z v
      have : ν z * (1 / (lam + 1) * (1 / (N : ℝ))) ≤ 0 := by
        calc _ ≤ ν z * jsqdKernel lam d M G N z y := mul_le_mul_of_nonneg_left hk (hν0 z)
          _ ≤ 0 := hle
      have := hν0 z
      nlinarith
  intro z
  exact key _ z rfl

end kernel

/-! ### Existence of a stationary distribution from the drift condition -/

section existence
variable (lam : ℝ) (d : ℕ) (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)

/-- States with every coordinate at most `k`. -/
def box (k : ℕ) : Finset (Fin N → ℕ) := Fintype.piFinset (fun _ => Finset.range (k + 1))

lemma mem_box_of_tot {k : ℕ} (y : Fin N → ℕ) (h : tot y ≤ k) : y ∈ box N k := by
  unfold box
  rw [Fintype.mem_piFinset]
  intro u
  have : y u ≤ tot y := Finset.single_le_sum (f := y) (fun _ _ => Nat.zero_le _) (mem_univ u)
  simp only [mem_range]; omega

local notation "Kk" => jsqdKernel lam d M G N

lemma stepProb_nonneg (hlam : 0 < lam) (n : ℕ) (z y : Fin N → ℕ) : 0 ≤ stepProb (Kk) n z y := by
  induction n generalizing y with
  | zero => simp only [stepProb]; split_ifs <;> norm_num
  | succ n ih =>
    simp only [stepProb]
    exact tsum_nonneg (fun w => mul_nonneg (ih w) (kernel_nonneg lam d M G N hlam w y))

lemma stepProb_supp (n : ℕ) (y : Fin N → ℕ) (hy : n < tot y) : stepProb (Kk) n 0 y = 0 := by
  induction n generalizing y with
  | zero =>
    simp only [stepProb]
    rw [if_neg]
    intro h; rw [← h] at hy; simp [tot] at hy
  | succ n ih =>
    simp only [stepProb]
    have : ∀ w, stepProb (Kk) n 0 w * Kk w y = 0 := by
      intro w
      by_cases hw : n < tot w
      · rw [ih w hw, zero_mul]
      · rw [kernel_zero_of_tot lam d M G N y w (by omega), mul_zero]
    simp [this]

lemma stepProb_hasSum (hlam : 0 < lam) (hrow : ∀ z, HasSum (Kk z) 1) (n : ℕ) :
    HasSum (stepProb (Kk) n 0) 1 := by
  induction n with
  | zero =>
    have : stepProb (Kk) 0 0 = fun y => if y = 0 then 1 else 0 := by
      funext y; simp only [stepProb]; split_ifs with h1 h2 h2 <;> simp_all
    rw [this]; exact hasSum_ite_eq 0 1
  | succ n ih =>
    have := push_hasSum (Kk) (kernel_nonneg lam d M G N hlam) hrow (kernel_colfin lam d M G N)
      _ (stepProb_nonneg lam d M G N hlam n 0) ih
    exact this

lemma stepProb_le_one (hlam : 0 < lam) (hrow : ∀ z, HasSum (Kk z) 1) (n : ℕ) (y : Fin N → ℕ) :
    stepProb (Kk) n 0 y ≤ 1 :=
  le_hasSum (stepProb_hasSum lam d M G N hlam hrow n) y
    (fun j _ => stepProb_nonneg lam d M G N hlam n 0 j)

lemma stepProb_sum_box (hlam : 0 < lam) (hrow : ∀ z, HasSum (Kk z) 1) (n : ℕ) :
    ∑ y ∈ box N n, stepProb (Kk) n 0 y = 1 := by
  have h := stepProb_hasSum lam d M G N hlam hrow n
  have h2 : HasSum (stepProb (Kk) n 0) (∑ y ∈ box N n, stepProb (Kk) n 0 y) :=
    hasSum_sum_of_ne_finset_zero (fun y hy => by
    apply stepProb_supp
    by_contra hc; push Not at hc
    exact hy (mem_box_of_tot N y hc))
  exact h2.unique h

/-- The column sum `∑_z p(z) K(z, y)` as a finite sum. -/
lemma col_tsum_eq (p : (Fin N → ℕ) → ℝ) (y : Fin N → ℕ) :
    ∑' z, p z * Kk z y =
      ∑ z ∈ Fintype.piFinset (fun u => Finset.range (y u + 2)), p z * Kk z y :=
  tsum_eq_sum (fun z hz => by rw [kernel_supp lam d M G N y z hz, mul_zero])

/-- The drift step: `E[V(Y_{k+1})] = E[(KV)(Y_k)]`, as finite sums. -/
lemma drift_step (V : (Fin N → ℕ) → ℝ) (k : ℕ) :
    ∑ y ∈ box N (k + 1), stepProb (Kk) (k + 1) 0 y * V y =
      ∑ w ∈ box N k, stepProb (Kk) k 0 w * kexp (Kk) V w := by
  have h1 : ∀ y, stepProb (Kk) (k + 1) 0 y = ∑ w ∈ box N k, stepProb (Kk) k 0 w * Kk w y := by
    intro y
    simp only [stepProb]
    apply tsum_eq_sum
    intro w hw
    rw [stepProb_supp lam d M G N k w (by
      by_contra hc; push Not at hc; exact hw (mem_box_of_tot N w hc)), zero_mul]
  simp only [h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hp : stepProb (Kk) k 0 w = 0
  · simp [hp]
  · have htw : tot w ≤ k := by
      by_contra hc; push Not at hc
      exact hp (stepProb_supp lam d M G N k w hc)
    unfold kexp
    rw [tsum_eq_sum (s := box N (k + 1)) (fun y hy => by
      rw [kernel_zero_of_tot lam d M G N y w (by
        by_contra hc; push Not at hc; exact hy (mem_box_of_tot N y (by omega))), zero_mul])]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro y _; ring

end existence

section existence2
variable (lam : ℝ) (d : ℕ) (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)

local notation "Kk" => jsqdKernel lam d M G N

lemma col_step (y : Fin N → ℕ) (k : ℕ) :
    ∑ z ∈ Fintype.piFinset (fun u => Finset.range (y u + 2)), stepProb (Kk) k 0 z * Kk z y =
      stepProb (Kk) (k + 1) 0 y := by
  rw [← col_tsum_eq lam d M G N]; rfl

theorem exists_stationary (hlam : 0 < lam) (hrow : ∀ z, HasSum (Kk z) 1)
    (C : Set (Fin N → ℕ)) (CB : Finset (Fin N → ℕ)) (hCB : ∀ z ∈ C, z ∈ CB)
    (V : (Fin N → ℕ) → ℝ) (hV0 : ∀ z, 0 ≤ V z) (hV00 : V 0 = 0)
    (hdrift : ∀ z, oneStepDrift (Kk) V z ≤ -1 + 2 * C.indicator (fun _ => (1 : ℝ)) z) :
    ∃ π, IsStationary (Kk) π := by
  classical
  set P : ℕ → (Fin N → ℕ) → ℝ := fun k => stepProb (Kk) k 0 with hP
  have hP0 : ∀ k y, 0 ≤ P k y := fun k y => stepProb_nonneg lam d M G N hlam k 0 y
  have hP1 : ∀ k y, P k y ≤ 1 := fun k y => stepProb_le_one lam d M G N hlam hrow k y
  have hPs : ∀ k, HasSum (P k) 1 := fun k => stepProb_hasSum lam d M G N hlam hrow k
  set m : ℕ → ℝ := fun k => ∑ y ∈ box N k, P k y * V y with hm
  set Q : ℕ → ℝ := fun k => ∑ y ∈ CB, P k y with hQ
  have hstep : ∀ k, m (k + 1) - m k ≤ -1 + 2 * Q k := by
    intro k
    simp only [hm, hQ, hP]
    rw [drift_step lam d M G N V k]
    have e : ∑ w ∈ box N k, stepProb (Kk) k 0 w * kexp (Kk) V w =
        ∑ w ∈ box N k, stepProb (Kk) k 0 w * oneStepDrift (Kk) V w +
          ∑ y ∈ box N k, stepProb (Kk) k 0 y * V y := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro w _
      unfold oneStepDrift; ring
    rw [e, add_sub_cancel_right]
    calc _ ≤ ∑ w ∈ box N k, stepProb (Kk) k 0 w * (-1 + 2 * C.indicator (fun _ => (1 : ℝ)) w) :=
          Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hdrift w) (hP0 k w))
      _ = -(∑ w ∈ box N k, stepProb (Kk) k 0 w) +
            2 * ∑ w ∈ box N k, stepProb (Kk) k 0 w * C.indicator (fun _ => (1 : ℝ)) w := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro w _; ring
      _ ≤ _ := by
          rw [stepProb_sum_box lam d M G N hlam hrow k]
          have : ∑ w ∈ box N k, stepProb (Kk) k 0 w * C.indicator (fun _ => (1 : ℝ)) w ≤
              ∑ y ∈ CB, stepProb (Kk) k 0 y := by
            calc _ ≤ ∑ w ∈ box N k, (if w ∈ CB then stepProb (Kk) k 0 w else 0) := by
                  apply Finset.sum_le_sum; intro w _
                  by_cases hw : w ∈ C
                  · rw [Set.indicator_of_mem hw, if_pos (hCB w hw), mul_one]
                  · rw [Set.indicator_of_notMem hw, mul_zero]
                    split_ifs
                    · exact hP0 k w
                    · exact le_refl _
              _ = ∑ w ∈ box N k ∩ CB, stepProb (Kk) k 0 w := Finset.sum_ite_mem _ _ _
              _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
                  (fun w _ _ => hP0 k w)
          linarith
  have hm0 : m 0 = 0 := by
    simp only [hm]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y = 0
    · rw [hy, hV00, mul_zero]
    · simp only [hP, stepProb]; rw [if_neg (Ne.symm hy), zero_mul]
  have hmn : ∀ n, 0 ≤ m n := fun n =>
    Finset.sum_nonneg (fun y _ => mul_nonneg (hP0 n y) (hV0 y))
  have htel : ∀ n, m n - m 0 ≤ -(n : ℝ) + 2 * ∑ k ∈ range n, Q k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]; push_cast
      have := hstep n
      linarith
  have hQsum : ∀ n : ℕ, (n : ℝ) / 2 ≤ ∑ k ∈ range n, Q k := by
    intro n
    have := htel n; have := hmn n; rw [hm0] at *; linarith
  -- Cesaro averages
  set μ : ℕ → (Fin N → ℕ) → ℝ := fun n y => (∑ k ∈ range (n + 1), P k y) / ((n : ℝ) + 1) with hμ
  have hn1 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hμ0 : ∀ n y, 0 ≤ μ n y := fun n y =>
    div_nonneg (Finset.sum_nonneg (fun k _ => hP0 k y)) (hn1 n).le
  have hμ1 : ∀ n y, μ n y ≤ 1 := by
    intro n y
    simp only [hμ]
    rw [div_le_one (hn1 n)]
    calc _ ≤ ∑ k ∈ range (n + 1), (1 : ℝ) := Finset.sum_le_sum (fun k _ => hP1 k y)
      _ = (n : ℝ) + 1 := by simp
  have hμF : ∀ n (F : Finset (Fin N → ℕ)), ∑ y ∈ F, μ n y ≤ 1 := by
    intro n F
    simp only [hμ]
    rw [← Finset.sum_div, div_le_one (hn1 n), Finset.sum_comm]
    calc _ ≤ ∑ k ∈ range (n + 1), (1 : ℝ) := Finset.sum_le_sum (fun k _ =>
          sum_le_hasSum F (fun i _ => hP0 k i) (hPs k))
      _ = (n : ℝ) + 1 := by simp
  have hμC : ∀ n, (1 : ℝ) / 2 ≤ ∑ y ∈ CB, μ n y := by
    intro n
    simp only [hμ]
    rw [← Finset.sum_div, le_div_iff₀ (hn1 n), Finset.sum_comm]
    have := hQsum (n + 1)
    simp only [hQ] at this
    push_cast at this
    linarith
  have hμK : ∀ n y, ∑ z ∈ Fintype.piFinset (fun u => Finset.range (y u + 2)), μ n z * Kk z y =
      μ n y + (P (n + 1) y - P 0 y) / ((n : ℝ) + 1) := by
    intro n y
    simp only [hμ]
    have e : ∀ z, (∑ k ∈ range (n + 1), P k z) / ((n : ℝ) + 1) * Kk z y =
        (∑ k ∈ range (n + 1), P k z * Kk z y) / ((n : ℝ) + 1) := by
      intro z; rw [div_mul_eq_mul_div, Finset.sum_mul]
    simp only [e]
    rw [← Finset.sum_div, Finset.sum_comm]
    simp only [hP, col_step lam d M G N y]
    rw [← add_div]
    congr 1
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun k => stepProb (Kk) k 0 y)]
    ring
  -- extraction of a convergent subsequence
  have hcpt : IsCompact (Set.pi Set.univ (fun _ : Fin N → ℕ => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨ν, hνmem, φ, hφ, hlim⟩ := hcpt.tendsto_subseq (x := μ) (fun n => by
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
    exact fun y => ⟨hμ0 n y, hμ1 n y⟩)
  have hpt : ∀ y, Tendsto (fun j => μ (φ j) y) atTop (𝓝 (ν y)) := by
    intro y
    exact (tendsto_pi_nhds.mp hlim) y
  have hν0 : ∀ y, 0 ≤ ν y := fun y => by
    have := hνmem y (Set.mem_univ _); exact this.1
  have hνF : ∀ F : Finset (Fin N → ℕ), ∑ y ∈ F, ν y ≤ 1 := by
    intro F
    exact le_of_tendsto' (tendsto_finsetSum F (fun y _ => hpt y)) (fun j => hμF _ F)
  have hνC : (1 : ℝ) / 2 ≤ ∑ y ∈ CB, ν y :=
    ge_of_tendsto' (tendsto_finsetSum CB (fun y _ => hpt y)) (fun j => hμC _)
  have hφt : Tendsto (fun j => ((φ j : ℕ) : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  have hνK : ∀ y, ∑ z ∈ Fintype.piFinset (fun u => Finset.range (y u + 2)), ν z * Kk z y = ν y := by
    intro y
    set T := Fintype.piFinset (fun u => Finset.range (y u + 2))
    have hA : Tendsto (fun j => ∑ z ∈ T, μ (φ j) z * Kk z y) atTop (𝓝 (∑ z ∈ T, ν z * Kk z y)) :=
      tendsto_finsetSum T (fun z _ => (hpt z).mul_const _)
    have hrem : Tendsto (fun j => (P (φ j + 1) y - P 0 y) / ((φ j : ℝ) + 1)) atTop (𝓝 0) := by
      apply squeeze_zero_norm (a := fun j => 1 / ((φ j : ℝ) + 1))
      · intro j
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (hn1 _)]
        apply div_le_div_of_nonneg_right _ (hn1 _).le
        rw [abs_le]
        constructor <;> linarith [hP0 (φ j + 1) y, hP1 (φ j + 1) y, hP0 0 y, hP1 0 y]
      · exact (hφt.inv_tendsto_atTop).congr (fun j => by rw [Pi.inv_apply, one_div])
    have hB : Tendsto (fun j => μ (φ j) y + (P (φ j + 1) y - P 0 y) / ((φ j : ℝ) + 1)) atTop
        (𝓝 (ν y + 0)) := (hpt y).add hrem
    simp only [← hμK] at hB
    rw [add_zero] at hB
    exact tendsto_nhds_unique hA hB
  -- normalisation
  have hνs : Summable ν := summable_of_sum_le hν0 hνF
  set c := ∑' y, ν y with hc
  have hc2 : (1 : ℝ) / 2 ≤ c := le_trans hνC (hνs.sum_le_tsum CB (fun y _ => hν0 y))
  have hcpos : 0 < c := by linarith
  refine ⟨fun y => ν y / c, ⟨fun y => div_nonneg (hν0 y) hcpos.le, ?_⟩, ?_⟩
  · have := hνs.hasSum.div_const c
    rwa [div_self hcpos.ne'] at this
  · intro y
    have h1 : HasSum (fun z => ν z * Kk z y)
        (∑ z ∈ Fintype.piFinset (fun u => Finset.range (y u + 2)), ν z * Kk z y) :=
      hasSum_sum_of_ne_finset_zero (fun z hz => by rw [kernel_supp lam d M G N y z hz, mul_zero])
    rw [hνK y] at h1
    have := h1.div_const c
    show HasSum (fun z => ν z / c * Kk z y) (ν y / c)
    have e : (fun z => ν z / c * Kk z y) = fun z => ν z * Kk z y / c := by funext z; ring
    rw [e]; exact this

theorem unique_stationary (hlam : 0 < lam) (hN : 1 ≤ N) (hrow : ∀ z, HasSum (Kk z) 1)
    (π₁ π₂ : (Fin N → ℕ) → ℝ) (h₁ : IsStationary (Kk) π₁) (h₂ : IsStationary (Kk) π₂) :
    π₁ = π₂ := by
  have hK0 := kernel_nonneg lam d M G N hlam
  have hc := kernel_colfin lam d M G N
  have hpos : ∀ π, IsStationary (Kk) π → 0 < π 0 := by
    intro π hπ
    rcases (hπ.1.1 0).lt_or_eq with h | h
    · exact h
    · exfalso
      have := vanish lam d M G N hlam hN π hπ.1.1 hπ.2 h.symm
      have hz : π = 0 := funext this
      have := hπ.1.2
      rw [hz] at this
      have := this.unique hasSum_zero
      norm_num at this
  have p2 := hpos π₂ h₂
  set c := π₁ 0 / π₂ 0 with hcdef
  set ν : (Fin N → ℕ) → ℝ := fun z => π₁ z - c * π₂ z with hν
  have hνs : Summable ν := h₁.1.2.summable.sub (h₂.1.2.summable.mul_left c)
  have hνK : ∀ y, HasSum (fun z => ν z * Kk z y) (ν y) := by
    intro y
    have := (h₁.2 y).sub ((h₂.2 y).mul_left c)
    have e : (fun z => ν z * Kk z y) = fun z => π₁ z * Kk z y - c * (π₂ z * Kk z y) := by
      funext z; simp only [hν]; ring
    rw [e]; exact this
  have hν00 : ν 0 = 0 := by simp only [hν, hcdef]; field_simp; ring
  have hνneg : Summable (fun z => -ν z) := hνs.neg
  have hνKneg : ∀ y, HasSum (fun z => (-ν z) * Kk z y) (-ν y) := by
    intro y
    have := (hνK y).neg
    have e : (fun z => (-ν z) * Kk z y) = fun z => -(ν z * Kk z y) := by funext z; ring
    rw [e]; exact this
  have hp := pos_part_stat (Kk) hK0 hrow hc ν hνs hνK
  have hn := pos_part_stat (Kk) hK0 hrow hc (fun z => -ν z) hνneg hνKneg
  have vp := vanish lam d M G N hlam hN (fun z => max (ν z) 0) (fun z => le_max_right _ _) hp
    (by simp [hν00])
  have vn := vanish lam d M G N hlam hN (fun z => max (-ν z) 0) (fun z => le_max_right _ _) hn
    (by simp [hν00])
  have hν0 : ∀ z, ν z = 0 := by
    intro z
    have a := vp z; have b := vn z
    have h1 : ν z ≤ 0 := by have := le_max_left (ν z) 0; linarith
    have h2 : -ν z ≤ 0 := by have := le_max_left (-ν z) 0; linarith
    linarith
  have heq : ∀ z, π₁ z = c * π₂ z := by
    intro z; have := hν0 z; simp only [hν] at this; linarith
  have hc1 : c = 1 := by
    have hs1 := h₁.1.2
    have hs2 := h₂.1.2.mul_left c
    rw [mul_one] at hs2
    have : π₁ = fun z => c * π₂ z := funext heq
    rw [this] at hs1
    exact (hs2.unique hs1)
  funext z
  rw [heq z, hc1, one_mul]

lemma nbr_nonempty (hN : 1 ≤ N) (hconn : (compatGraph M G N).Connected) (w : Fin (M N)) :
    (nbrW M G N w).Nonempty := by
  obtain ⟨p⟩ := hconn.preconnected (Sum.inr w) (Sum.inl ⟨0, hN⟩)
  match p with
  | SimpleGraph.Walk.cons h _ =>
    rename_i x
    unfold compatGraph at h
    rw [SimpleGraph.fromRel_adj] at h
    obtain ⟨_, h | h⟩ := h
    · obtain ⟨v, w', h1, _, _⟩ := h
      exact absurd h1 (by simp)
    · obtain ⟨v, w', _, h2, h3⟩ := h
      have : w = w' := Sum.inr.inj h2
      subst this
      exact ⟨v, by simp [nbrW, h3]⟩

end existence2

end StrictCompatLB.MeanField.T48

open StrictCompatLB.MeanField StrictCompatLB.MeanField.T48 in
theorem solution (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (d : ℕ) (hd : 1 ≤ d)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsub : IsSubcritical d M G) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∃! π : (Fin N → ℕ) → ℝ,
      IsStationary (jsqdKernel lam d M G N) π := by
  obtain ⟨N₀, hN₀, h5⟩ := lemma_H_5 lam hlam0 hlam1 d hd M hM G hconn hsub
  refine ⟨N₀, hN₀, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans hN₀ hN
  have hne := nbr_nonempty M G N hN1 (hconn N hN1)
  have hrow := kernel_row lam d M G N hlam0 hd hN1 (hM N) hne
  set Γ := 3 * ((1 + lam) / (1 - lam)) * (N : ℝ)
  have hCB : ∀ z ∈ CGamma N Γ, z ∈ box N ⌊Γ⌋₊ := by
    intro z hz
    apply mem_box_of_tot
    unfold CGamma at hz
    simp only [Set.mem_setOf_eq] at hz
    apply Nat.le_floor
    have e : ∑ i ∈ Ico 1 (maxLen z + 1), (Qcount z i : ℝ) = ((tot z : ℕ) : ℝ) := by
      have : ∑ i ∈ Ico 1 (maxLen z + 1), Qcount z i = tot z := by
        unfold Qcount tot
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
    rw [← e]; exact hz
  have hV0 : ∀ z : Fin N → ℕ, 0 ≤ lyap 1 z := fun z => by
    unfold lyap
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  have hV00 : lyap 1 (0 : Fin N → ℕ) = 0 := by
    unfold lyap maxLen
    simp
  obtain ⟨π, hπ⟩ := exists_stationary lam d M G N hlam0 hrow (CGamma N Γ) (box N ⌊Γ⌋₊) hCB
    (lyap 1) hV0 hV00 (h5 N hN)
  exact ⟨π, hπ, fun π' hπ' => unique_stationary lam d M G N hlam0 hN1 hrow π' π hπ' hπ⟩
