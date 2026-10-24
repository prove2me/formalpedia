-- Prove2me | solution 1 for StrictCompatLB.MeanField.lemma_4_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T15:00:48.661768+00:00
-- url     : https://prove2.me/submissions/77c57158-0297-432f-a2dd-99c6c5877cb4

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model
import Theorems.Thm_StrictCompatLB_MeanField_lemma_H_2

open Filter Topology MeasureTheory Finset
open scoped ENNReal

namespace StrictCompatLB.MeanField.L49

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

section extra
variable (lam : ℝ) (d : ℕ) (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)

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


lemma row_summable (z : Fin N → ℕ) (h : (Fin N → ℕ) → ℝ) :
    Summable (fun z' => jsqdKernel lam d M G N z z' * h z') :=
  summable_of_ne_finset_zero (s := Fintype.piFinset (fun _ => Finset.range (tot z + 2)))
    (fun z' hz' => by
      rw [kernel_zero_of_tot lam d M G N z' z ?_, zero_mul]
      by_contra hc; push Not at hc
      apply hz'
      rw [Fintype.mem_piFinset]; intro u
      have : z' u ≤ tot z' := Finset.single_le_sum (f := z') (fun _ _ => Nat.zero_le _) (mem_univ u)
      simp only [mem_range]; omega)

end extra

section stat
variable {S : Type*} (K : S → S → ℝ)

lemma summable_bdd (π : S → ℝ) (hπ : IsProbVec π) (h : S → ℝ) (B : ℝ) (hB : ∀ z, |h z| ≤ B) :
    Summable (fun z => π z * h z) :=
  Summable.of_norm_bounded (g := fun z => B * π z) (hπ.2.summable.mul_left B) (fun z => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ.1 z), mul_comm]
    exact mul_le_mul_of_nonneg_right (hB z) (hπ.1 z))

/-- Stationarity tested against a bounded function. -/
lemma stat_bounded (hK0 : ∀ z y, 0 ≤ K z y) (hrow : ∀ z, HasSum (K z) 1) (hc : ColFin K)
    (π : S → ℝ) (hπ : IsStationary K π) (h : S → ℝ) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ z, |h z| ≤ B) :
    ∑' z, π z * kexp K h z = ∑' z, π z * h z := by
  set f : S → S → ℝ := fun z z' => π z * (K z z' * h z') with hf
  set g : S × S → ℝ := fun x => B * (π x.1 * K x.1 x.2) with hg
  have hg0 : 0 ≤ g := fun x => mul_nonneg hB0 (mul_nonneg (hπ.1.1 _) (hK0 _ _))
  have hgrow : ∀ z, HasSum (fun z' => g (z, z')) (B * π z) := by
    intro z
    have := ((hrow z).mul_left (π z)).mul_left B
    simpa [g] using this
  have hgs : Summable g := (summable_prod_of_nonneg hg0).mpr
    ⟨fun z => (hgrow z).summable, by
      have e : (fun z => ∑' z', g (z, z')) = fun z => B * π z := funext (fun z => (hgrow z).tsum_eq)
      rw [e]; exact hπ.1.2.summable.mul_left B⟩
  have hfs : Summable (Function.uncurry f) := Summable.of_norm_bounded hgs (fun x => by
    simp only [Function.uncurry, hf, hg, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg (hπ.1.1 _), abs_of_nonneg (hK0 _ _)]
    have := hB x.2
    have h1 : 0 ≤ π x.1 * K x.1 x.2 := mul_nonneg (hπ.1.1 _) (hK0 _ _)
    nlinarith)
  have hrowf : ∀ z, Summable (f z) := fun z => hfs.prod_factor z
  have hcolf : ∀ z', Summable (fun z => f z z') := by
    intro z'
    obtain ⟨s, hs⟩ := hc z'
    exact summable_of_ne_finset_zero (s := s) (fun z hz => by simp [hf, hs z hz])
  have e1 : ∑' z, π z * kexp K h z = ∑' z, ∑' z', f z z' := by
    congr 1; funext z
    unfold kexp
    rw [← tsum_mul_left]
  rw [e1, ← hfs.tsum_comm' hrowf hcolf]
  congr 1; funext z'
  have : ∑' z, f z z' = (∑' z, π z * K z z') * h z' := by
    rw [← tsum_mul_right]; congr 1; funext z; simp only [hf]; ring
  rw [this, (hπ.2 z').tsum_eq]

end stat

end StrictCompatLB.MeanField.L49

open StrictCompatLB.MeanField StrictCompatLB.MeanField.L49 in
theorem solution (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (d : ℕ) (hd : 1 ≤ d)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsub : IsSubcritical d M G) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ π : (Fin N → ℕ) → ℝ,
      IsStationary (jsqdKernel lam d M G N) π → ∀ k : ℕ, 1 ≤ k →
        (∑' i : ℕ, if k ≤ i then expectENN π (fun z => occ z i) else 0) ≤
          ENNReal.ofReal (((1 + lam) / 2) / (1 - (1 + lam) / 2)) *
            expectENN π (fun z => occ z (k - 1)) := by
  set ε := (1 - lam) / (2 * lam) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  obtain ⟨N₀, hN₀, h2⟩ := lemma_H_2 lam hlam0 hlam1 d hd M hM G hconn hsub ε hε0
  refine ⟨N₀, hN₀, fun N hN π hπ k hk => ?_⟩
  have hN1 : 1 ≤ N := le_trans hN₀ hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set K := jsqdKernel lam d M G N with hKdef
  have hK0 : ∀ z y, 0 ≤ K z y := kernel_nonneg lam d M G N hlam0
  have hne := nbr_nonempty M G N hN1 (hconn N hN1)
  have hrow : ∀ z, HasSum (K z) 1 := kernel_row lam d M G N hlam0 hd hN1 (hM N) hne
  have hc : ColFin K := kernel_colfin lam d M G N
  have hρ : (1 + ε) * lam = (1 + lam) / 2 := by rw [hε]; field_simp; ring
  set ρ := (1 + lam) / 2 with hρdef
  have hl1 : 0 < lam + 1 := by linarith
  set c1 := ρ / (lam + 1) with hc1
  set c2 := (1 - ρ) / (lam + 1) with hc2
  have hc1p : 0 < c1 := div_pos (by rw [hρdef]; linarith) hl1
  have hc2p : 0 < c2 := div_pos (by rw [hρdef]; linarith) hl1
  set V : (Fin N → ℕ) → ℝ := lyap k with hV
  set q : (Fin N → ℕ) → ℝ := fun z => occ z (k - 1) with hq
  set T : (Fin N → ℕ) → ℝ := fun z => tailSum k z with hT
  set D : (Fin N → ℕ) → ℝ := fun z => c1 * q z - c2 * T z with hD
  -- basic bounds
  have hocc0 : ∀ (z : Fin N → ℕ) i, 0 ≤ occ z i := fun z i => div_nonneg (Nat.cast_nonneg _) hNpos.le
  have hocc1 : ∀ (z : Fin N → ℕ) i, occ z i ≤ 1 := by
    intro z i
    unfold occ
    rw [div_le_one hNpos]
    have : Qcount z i ≤ N := by
      unfold Qcount
      calc _ ≤ (univ : Finset (Fin N)).card := Finset.card_filter_le _ _
        _ = N := by simp
    exact_mod_cast this
  have hT0 : ∀ z, 0 ≤ T z := fun z => Finset.sum_nonneg (fun i _ => hocc0 z i)
  have hV0 : ∀ z, 0 ≤ V z := fun z => by
    simp only [hV]; unfold lyap
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  have hdrift : ∀ z, kexp K V z ≤ V z + D z := by
    intro z
    have := h2 N hN k hk z
    unfold oneStepDrift at this
    have e : 1 / (lam + 1) * ((1 + ε) * lam * occ z (k - 1) - (1 - (1 + ε) * lam) * tailSum k z) =
        D z := by
      simp only [hD, hq, hT, hc1, hc2]; rw [hρ]; field_simp
    rw [e] at this
    linarith
  have hkV0 : ∀ z, 0 ≤ kexp K V z := fun z =>
    tsum_nonneg (fun z' => mul_nonneg (hK0 z z') (hV0 z'))
  -- truncation
  have hJ : ∀ m : ℝ, 0 ≤ m → ∀ z, kexp K (fun z' => min (V z') m) z ≤ min (V z + D z) m := by
    intro m hm z
    apply le_min
    · calc _ ≤ kexp K V z := by
            unfold kexp
            exact Summable.tsum_le_tsum (fun z' => mul_le_mul_of_nonneg_left (min_le_left _ _) (hK0 z z'))
              (row_summable lam d M G N z _) (row_summable lam d M G N z _)
        _ ≤ _ := hdrift z
    · calc _ ≤ ∑' z', K z z' * m := by
            unfold kexp
            exact Summable.tsum_le_tsum (fun z' => mul_le_mul_of_nonneg_left (min_le_right _ _) (hK0 z z'))
              (row_summable lam d M G N z _) ((hrow z).summable.mul_right m)
        _ = m := by rw [tsum_mul_right, (hrow z).tsum_eq, one_mul]
  have hgm : ∀ m : ℝ, 0 ≤ m →
      ∑' z, π z * (min (V z) m - min (V z + D z) m) ≤ 0 := by
    intro m hm
    have hb1 : ∀ z, |min (V z) m| ≤ m := fun z => by
      rw [abs_of_nonneg (le_min (hV0 z) hm)]; exact min_le_right _ _
    have hb2 : ∀ z, |min (V z + D z) m| ≤ m := fun z => by
      rw [abs_of_nonneg (le_min (le_trans (hkV0 z) (hdrift z)) hm)]; exact min_le_right _ _
    have hs1 := summable_bdd π hπ.1 _ m hb1
    have hs2 := summable_bdd π hπ.1 _ m hb2
    have hst := stat_bounded K hK0 hrow hc π hπ (fun z => min (V z) m) m hm hb1
    have hle : ∑' z, π z * kexp K (fun z' => min (V z') m) z ≤ ∑' z, π z * min (V z + D z) m := by
      apply Summable.tsum_le_tsum (fun z => mul_le_mul_of_nonneg_left (hJ m hm z) (hπ.1.1 z))
      · apply summable_bdd π hπ.1 _ m
        intro z
        rw [abs_of_nonneg (show 0 ≤ kexp K (fun z' => min (V z') m) z from
          tsum_nonneg (fun z' => mul_nonneg (hK0 z z') (le_min (hV0 z') hm)))]
        exact le_trans (hJ m hm z) (min_le_right _ _)
      · exact hs2
    rw [hst] at hle
    have : ∑' z, π z * (min (V z) m - min (V z + D z) m) =
        ∑' z, π z * min (V z) m - ∑' z, π z * min (V z + D z) m := by
      rw [← Summable.tsum_sub hs1 hs2]; congr 1; funext z; ring
    rw [this]; linarith
  -- positive and negative parts of D
  set Dp : (Fin N → ℕ) → ℝ := fun z => max (D z) 0 with hDp
  set Dn : (Fin N → ℕ) → ℝ := fun z => max (-D z) 0 with hDn
  have hDpb : ∀ z, |Dp z| ≤ c1 := by
    intro z
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le _ hc1p.le
    simp only [hD]
    have := hocc1 z (k - 1); have := hT0 z
    have : c1 * q z ≤ c1 := by
      calc c1 * q z ≤ c1 * 1 := mul_le_mul_of_nonneg_left (hocc1 z (k - 1)) hc1p.le
        _ = c1 := mul_one _
    nlinarith
  have hDps := summable_bdd π hπ.1 Dp c1 hDpb
  have hF : ∀ F : Finset (Fin N → ℕ), ∑ z ∈ F, π z * Dn z ≤ ∑' z, π z * Dp z := by
    intro F
    set m : ℝ := ∑ z ∈ F, (|V z| + |V z + D z|) with hm
    have hm0 : 0 ≤ m := Finset.sum_nonneg (fun z _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
    have hmF : ∀ z ∈ F, V z ≤ m ∧ V z + D z ≤ m := by
      intro z hz
      have h1 : |V z| + |V z + D z| ≤ m :=
        Finset.single_le_sum (f := fun z => |V z| + |V z + D z|)
          (fun z _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hz
      constructor
      · linarith [le_abs_self (V z), abs_nonneg (V z + D z)]
      · linarith [le_abs_self (V z + D z), abs_nonneg (V z)]
    set gm : (Fin N → ℕ) → ℝ := fun z => min (V z) m - min (V z + D z) m with hgmdef
    have hgD : ∀ z, 0 ≤ gm z + Dp z := by
      intro z
      simp only [hgmdef, hDp]
      rcases le_total (D z) 0 with h | h
      · have : min (V z + D z) m ≤ min (V z) m := min_le_min_right _ (by linarith)
        have := le_max_right (D z) 0
        linarith
      · have : min (V z + D z) m ≤ min (V z) m + D z := by
          rcases le_total (V z) m with h' | h'
          · rw [min_eq_left h']; exact min_le_left _ _
          · rw [min_eq_right h']; have := min_le_right (V z + D z) m; linarith
        have := le_max_left (D z) 0
        linarith
    have hgb : ∀ z, |gm z + Dp z| ≤ 2 * m + c1 := by
      intro z
      have a1 : |min (V z) m| ≤ m := by
        rw [abs_of_nonneg (le_min (hV0 z) hm0)]; exact min_le_right _ _
      have a2 : |min (V z + D z) m| ≤ m := by
        rw [abs_of_nonneg (le_min (le_trans (hkV0 z) (hdrift z)) hm0)]; exact min_le_right _ _
      calc |gm z + Dp z| ≤ |min (V z) m| + |min (V z + D z) m| + |Dp z| := by
            simp only [hgmdef]
            calc _ ≤ |min (V z) m - min (V z + D z) m| + |Dp z| := abs_add_le _ _
              _ ≤ _ := by gcongr; exact abs_sub _ _
        _ ≤ _ := by linarith [hDpb z]
    have hsg := summable_bdd π hπ.1 (fun z => gm z + Dp z) _ hgb
    calc ∑ z ∈ F, π z * Dn z = ∑ z ∈ F, π z * (gm z + Dp z) := by
          apply Finset.sum_congr rfl; intro z hz
          obtain ⟨h1, h2⟩ := hmF z hz
          congr 1
          simp only [hgmdef, hDn, hDp, min_eq_left h1, min_eq_left h2]
          rcases le_total (D z) 0 with h | h
          · rw [max_eq_left (by linarith), max_eq_right h]; ring
          · rw [max_eq_right (by linarith), max_eq_left h]; ring
      _ ≤ ∑' z, π z * (gm z + Dp z) :=
          hsg.sum_le_tsum F (fun z _ => mul_nonneg (hπ.1.1 z) (hgD z))
      _ = ∑' z, π z * gm z + ∑' z, π z * Dp z := by
          have hs1 : Summable (fun z => π z * gm z) := by
            have := hsg.sub hDps
            refine this.congr (fun z => ?_); ring
          rw [← Summable.tsum_add hs1 hDps]; congr 1; funext z; ring
      _ ≤ _ := by have := hgm m hm0; simp only [hgmdef] at *; linarith
  have hDn0 : ∀ z, 0 ≤ π z * Dn z := fun z => mul_nonneg (hπ.1.1 z) (le_max_right _ _)
  have hDns : Summable (fun z => π z * Dn z) := summable_of_sum_le hDn0 hF
  have hDnle : ∑' z, π z * Dn z ≤ ∑' z, π z * Dp z := by
    exact Summable.tsum_le_of_sum_le hDns hF
  -- summability of π T and π q
  have hqs : Summable (fun z => π z * q z) :=
    summable_bdd π hπ.1 q 1 (fun z => by rw [abs_of_nonneg (hocc0 _ _)]; exact hocc1 _ _)
  have hTs : Summable (fun z => π z * T z) := by
    apply Summable.of_nonneg_of_le (fun z => mul_nonneg (hπ.1.1 z) (hT0 z))
      (f := fun z => (π z * Dn z + c1 * (π z * q z)) / c2)
    · intro z
      rw [le_div_iff₀ hc2p]
      have : -D z ≤ Dn z := le_max_left _ _
      simp only [hD] at this
      have hp := hπ.1.1 z
      nlinarith
    · exact (hDns.add (hqs.mul_left c1)).div_const c2
  have hineq : c2 * ∑' z, π z * T z ≤ c1 * ∑' z, π z * q z := by
    have e : ∀ z, π z * Dp z - π z * Dn z = c1 * (π z * q z) - c2 * (π z * T z) := by
      intro z
      simp only [hDp, hDn, hD]
      rcases le_total (c1 * q z - c2 * T z) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    have h1 : ∑' z, (π z * Dp z - π z * Dn z) = ∑' z, (c1 * (π z * q z) - c2 * (π z * T z)) := by
      congr 1; funext z; exact e z
    rw [Summable.tsum_sub hDps hDns, Summable.tsum_sub (hqs.mul_left _) (hTs.mul_left _),
      Summable.tsum_mul_left _ hqs, Summable.tsum_mul_left _ hTs] at h1
    linarith
  -- conversion to the `[0, ∞]`-valued statement
  have hTail : ∀ z : Fin N → ℕ, (∑' i : ℕ, if k ≤ i then ENNReal.ofReal (occ z i) else 0) =
      ENNReal.ofReal (T z) := by
    intro z
    simp only [hT]
    unfold tailSum
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hocc0 z i)]
    rw [show (∑ i ∈ Ico k (maxLen z + 1), ENNReal.ofReal (occ z i)) =
        ∑ i ∈ Ico k (maxLen z + 1), (if k ≤ i then ENNReal.ofReal (occ z i) else 0) from
      Finset.sum_congr rfl (fun i hi => by rw [if_pos (mem_Ico.mp hi).1])]
    apply tsum_eq_sum
    intro i hi
    simp only [mem_Ico, not_and_or, not_le, not_lt] at hi
    split_ifs with hki
    · rcases hi with h | h
      · omega
      · have : Qcount z i = 0 := by
          unfold Qcount
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro u _ hu
          have : z u ≤ maxLen z := Finset.le_sup (f := z) (mem_univ u)
          omega
        simp [occ, this]
    · rfl
  have hL : (∑' i : ℕ, if k ≤ i then expectENN π (fun z => occ z i) else 0) =
      ENNReal.ofReal (∑' z, π z * T z) := by
    unfold expectENN
    have e1 : ∀ i : ℕ, (if k ≤ i then ∑' z, ENNReal.ofReal (π z) * ENNReal.ofReal (occ z i) else 0) =
        ∑' z, ENNReal.ofReal (π z) * (if k ≤ i then ENNReal.ofReal (occ z i) else 0) := by
      intro i; split_ifs <;> simp
    simp only [e1]
    rw [ENNReal.tsum_comm]
    simp only [ENNReal.tsum_mul_left, hTail]
    rw [ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg (hπ.1.1 z) (hT0 z)) hTs]
    congr 1; funext z
    rw [ENNReal.ofReal_mul (hπ.1.1 z)]
  have hR : expectENN π (fun z => occ z (k - 1)) = ENNReal.ofReal (∑' z, π z * q z) := by
    unfold expectENN
    rw [ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg (hπ.1.1 z) (hocc0 z _)) hqs]
    congr 1; funext z
    rw [ENNReal.ofReal_mul (hπ.1.1 z)]
  rw [hL, hR, ← ENNReal.ofReal_mul (div_nonneg (by rw [hρdef]; linarith) (by rw [hρdef]; linarith))]
  apply ENNReal.ofReal_le_ofReal
  have hratio : ρ / (1 - ρ) = c1 / c2 := by
    rw [hc1, hc2]; field_simp
  rw [hratio, div_mul_eq_mul_div, le_div_iff₀ hc2p]
  linarith
