-- Prove2me | solution 1 for StrictCompatLB.FullInhomogeneous.pure_departure_fluid_limit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-18T21:43:03.852916+00:00
-- url     : https://prove2.me/submissions/d7b90823-2c93-469c-92f7-cc5dceec6658

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_CountableChain
import Definitions.Def_StrictCompatLB_MeanField_Model
import Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem

set_option autoImplicit false
set_option linter.unusedSectionVars false
section
open Filter Topology MeasureTheory Finset
open scoped ENNReal

namespace SC66D

open StrictCompatLB.MeanField

/-! PLLN piece (3): one-step drift identities of the uniformised LB chain `lbKernel` for the
occupancy coordinates `occ · i` and for the occupancy tail `tl k = ∑_{i ≥ k} occ · i`, plus
row sums, support and bounded increments (the hypotheses of `SC66A.az`). -/

section Kernel

variable (lam : ℝ) (M : ℕ → ℕ) (N : ℕ) (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)

/-- Expectation of `g` under one step of `lbKernel`. -/
theorem kexp (g : (Fin N → ℕ) → ℝ) (z : Fin N → ℕ) :
    HasSum (fun x => lbKernel lam M N route z x * g x)
      (lam / (lam + 1) * (1 / (M N : ℝ)) * ∑ w, ∑ v, route w z v * g (arrive z v) +
        1 / (lam + 1) * (1 / (N : ℝ)) * ∑ v, g (depart z v)) := by
  have hA : HasSum (fun x : Fin N → ℕ => ∑ w : Fin (M N), ∑ v : Fin N,
      route w z v * ((if x = arrive z v then (1 : ℝ) else 0) * g x))
      (∑ w, ∑ v, route w z v * g (arrive z v)) := by
    apply hasSum_sum; intro w _; apply hasSum_sum; intro v _
    convert hasSum_ite_eq (arrive z v) (route w z v * g (arrive z v)) using 1
    funext x; split_ifs with h <;> simp [h]
  have hB : HasSum (fun x : Fin N → ℕ => ∑ v : Fin N,
      (if x = depart z v then (1 : ℝ) else 0) * g x) (∑ v, g (depart z v)) := by
    apply hasSum_sum; intro v _
    convert hasSum_ite_eq (depart z v) (g (depart z v)) using 1
    funext x; split_ifs with h <;> simp [h]
  refine ((hA.mul_left (lam / (lam + 1) * (1 / (M N : ℝ)))).add
    (hB.mul_left (1 / (lam + 1) * (1 / (N : ℝ))))).congr_fun (fun x => ?_)
  simp only [lbKernel, add_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]

theorem lb_nonneg (hlam : 0 ≤ lam) (hr : ∀ w z v, 0 ≤ route w z v) (z x : Fin N → ℕ) :
    0 ≤ lbKernel lam M N route z x := by
  unfold lbKernel
  apply add_nonneg
  · apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg; intro w _; apply Finset.sum_nonneg; intro v _
    apply mul_nonneg (hr w z v); split_ifs <;> norm_num
  · apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg; intro v _; split_ifs <;> norm_num

theorem lb_hasSum_one (hlam : 0 ≤ lam) (hM : 0 < M N) (hN : 1 ≤ N)
    (hs : ∀ w z, ∑ v, route w z v = 1) (z : Fin N → ℕ) :
    HasSum (fun x => lbKernel lam M N route z x) 1 := by
  have h := kexp lam M N route (fun _ => 1) z
  simp only [mul_one] at h
  convert h using 1
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hM' : (M N : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hl : lam + 1 ≠ 0 := by linarith
  field_simp
  try ring

theorem lb_support (z x : Fin N → ℕ) (h : lbKernel lam M N route z x ≠ 0) :
    ∃ v, x = arrive z v ∨ x = depart z v := by
  by_contra hc
  push Not at hc
  apply h
  have h1 : ∀ v, x ≠ arrive z v := fun v => (hc v).1
  have h2 : ∀ v, x ≠ depart z v := fun v => (hc v).2
  simp [lbKernel, h1, h2]

end Kernel

section Occ

lemma sum_upd {N : ℕ} (F : ℕ → ℝ) (z : Fin N → ℕ) (v : Fin N) (a : ℕ) :
    ∑ u, F (Function.update z v a u) = ∑ u, F (z u) + (F a - F (z v)) := by
  rw [← Finset.add_sum_erase _ _ (mem_univ v),
    ← Finset.add_sum_erase _ (fun u => F (z u)) (mem_univ v)]
  have : ∑ u ∈ univ.erase v, F (Function.update z v a u) = ∑ u ∈ univ.erase v, F (z u) :=
    Finset.sum_congr rfl (fun u hu => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)])
  rw [this, Function.update_self]
  ring

lemma occ_eq {N : ℕ} (z : Fin N → ℕ) (i : ℕ) :
    occ z i = (∑ u, (if i ≤ z u then (1 : ℝ) else 0)) / (N : ℝ) := by
  unfold occ Qcount
  rw [Finset.natCast_card_filter]

lemma geqd_eq' {N : ℕ} (z : Fin N → ℕ) (i : ℕ) :
    geqd z i = (∑ u, (if z u = i then (1 : ℝ) else 0)) / (N : ℝ) := by
  unfold geqd
  rw [Finset.natCast_card_filter]

lemma occ_arr {N : ℕ} (z : Fin N → ℕ) (v : Fin N) (i : ℕ) :
    occ (arrive z v) i - occ z i =
      ((if i ≤ z v + 1 then (1 : ℝ) else 0) - (if i ≤ z v then (1 : ℝ) else 0)) / (N : ℝ) := by
  rw [occ_eq, occ_eq, ← sub_div]
  unfold arrive
  rw [sum_upd (fun a => if i ≤ a then (1 : ℝ) else 0)]
  ring

lemma occ_dep {N : ℕ} (z : Fin N → ℕ) (v : Fin N) (i : ℕ) :
    occ (depart z v) i - occ z i =
      ((if i ≤ z v - 1 then (1 : ℝ) else 0) - (if i ≤ z v then (1 : ℝ) else 0)) / (N : ℝ) := by
  rw [occ_eq, occ_eq, ← sub_div]
  unfold depart
  rw [sum_upd (fun a => if i ≤ a then (1 : ℝ) else 0)]
  ring

/-- The occupancy tail `∑_{i ≥ k} q_i(z) = (1/N) ∑_v (z_v + 1 - k)`. -/
noncomputable def tl {N : ℕ} (k : ℕ) (z : Fin N → ℕ) : ℝ :=
  (∑ u, (((z u + 1 - k : ℕ)) : ℝ)) / (N : ℝ)

lemma occ_tail_hasSum {N : ℕ} (z : Fin N → ℕ) (k : ℕ) :
    HasSum (fun j => occ z (k + j)) (tl k z) := by
  have h : ∀ j, occ z (k + j) = ∑ u, (if k + j ≤ z u then (1 : ℝ) else 0) / (N : ℝ) := by
    intro j; rw [occ_eq, Finset.sum_div]
  simp_rw [h]
  unfold tl
  rw [Finset.sum_div]
  apply hasSum_sum; intro u _
  apply HasSum.div_const
  have h2 : HasSum (fun j => if k + j ≤ z u then (1 : ℝ) else 0)
      (∑ j ∈ range (z u + 1 - k), if k + j ≤ z u then (1 : ℝ) else 0) := by
    apply hasSum_sum_of_ne_finset_zero
    intro j hj
    rw [Finset.mem_range] at hj
    rw [if_neg (by omega)]
  have h3 : (((z u + 1 - k : ℕ)) : ℝ) =
      ∑ j ∈ range (z u + 1 - k), if k + j ≤ z u then (1 : ℝ) else 0 := by
    rw [Finset.sum_congr rfl (fun j hj => if_pos (by rw [Finset.mem_range] at hj; omega))]
    simp
  rw [h3]; exact h2

lemma tl_arr {N : ℕ} (k : ℕ) (z : Fin N → ℕ) (v : Fin N) :
    tl k (arrive z v) - tl k z = (if k ≤ z v + 1 then (1 : ℝ) else 0) / (N : ℝ) := by
  unfold tl arrive
  rw [← sub_div, sum_upd (fun a => (((a + 1 - k : ℕ)) : ℝ))]
  congr 1
  have : (z v + 1 + 1 - k : ℕ) = (z v + 1 - k) + (if k ≤ z v + 1 then 1 else 0) := by
    split_ifs <;> omega
  rw [this]; push_cast; split_ifs <;> simp

lemma tl_dep {N : ℕ} (k : ℕ) (hk : 1 ≤ k) (z : Fin N → ℕ) (v : Fin N) :
    tl k (depart z v) - tl k z = -((if k ≤ z v then (1 : ℝ) else 0) / (N : ℝ)) := by
  unfold tl depart
  rw [← sub_div, sum_upd (fun a => (((a + 1 - k : ℕ)) : ℝ)), ← neg_div]
  congr 1
  have : (z v + 1 - k : ℕ) = (z v - 1 + 1 - k) + (if k ≤ z v then 1 else 0) := by
    split_ifs <;> omega
  rw [this]; push_cast; split_ifs <;> simp

end Occ

section Drift

variable (lam : ℝ) (M : ℕ → ℕ) (N : ℕ) (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)

/-- Level-aggregated arrival law (as in `SC66L.levA`). -/
noncomputable def levA (z : Fin N → ℕ) (i : ℕ) : ℝ :=
  (1 / (M N : ℝ)) * ∑ w : Fin (M N), ∑ v ∈ univ.filter (fun v => z v = i), route w z v

/-- Arrival mass at levels `≥ k - 1` (the tail of `levA`). -/
noncomputable def levT (z : Fin N → ℕ) (k : ℕ) : ℝ :=
  (1 / (M N : ℝ)) * ∑ w : Fin (M N), ∑ v ∈ univ.filter (fun v => k ≤ z v + 1), route w z v

/-- Drift identity for `occ · i`, `i ≥ 1`: `h (λ A_{i-1}(z) - x_i(z))`, `h = 1/((λ+1)N)`. -/
theorem drift_occ (z : Fin N → ℕ) (i : ℕ) (hi : 1 ≤ i) :
    HasSum (fun x => lbKernel lam M N route z x * (occ x i - occ z i))
      (1 / ((lam + 1) * (N : ℝ)) * (lam * levA M N route z (i - 1) - geqd z i)) := by
  convert kexp lam M N route (fun x => occ x i - occ z i) z using 1
  simp only [occ_arr, occ_dep]
  have hA : ∀ w, ∑ v, route w z v * (((if i ≤ z v + 1 then (1 : ℝ) else 0) -
      (if i ≤ z v then (1 : ℝ) else 0)) / (N : ℝ)) =
      (∑ v ∈ univ.filter (fun v => z v = i - 1), route w z v) / (N : ℝ) := by
    intro w
    rw [Finset.sum_filter, Finset.sum_div]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    split_ifs <;> first | (exfalso; omega) | ring
  have hD : ∑ v, ((if i ≤ z v - 1 then (1 : ℝ) else 0) - (if i ≤ z v then (1 : ℝ) else 0)) /
      (N : ℝ) = -geqd z i := by
    rw [geqd_eq', ← Finset.sum_div, ← neg_div, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun v _ => ?_)
    split_ifs <;> first | (exfalso; omega) | ring
  rw [Finset.sum_congr rfl (fun w _ => hA w), hD, ← Finset.sum_div]
  unfold levA
  rw [← one_div_mul_one_div]
  ring

/-- Drift identity for the tail `tl k`, `k ≥ 1`: `h (λ T_k(z) - q_k(z))`. -/
theorem drift_tl (z : Fin N → ℕ) (k : ℕ) (hk : 1 ≤ k) :
    HasSum (fun x => lbKernel lam M N route z x * (tl k x - tl k z))
      (1 / ((lam + 1) * (N : ℝ)) * (lam * levT M N route z k - occ z k)) := by
  convert kexp lam M N route (fun x => tl k x - tl k z) z using 1
  simp only [tl_arr, tl_dep k hk]
  have hA : ∀ w, ∑ v, route w z v * ((if k ≤ z v + 1 then (1 : ℝ) else 0) / (N : ℝ)) =
      (∑ v ∈ univ.filter (fun v => k ≤ z v + 1), route w z v) / (N : ℝ) := by
    intro w
    rw [Finset.sum_filter, Finset.sum_div]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    split_ifs <;> ring
  have hD : ∑ v, -((if k ≤ z v then (1 : ℝ) else 0) / (N : ℝ)) = -occ z k := by
    rw [occ_eq, Finset.sum_neg_distrib, Finset.sum_div]
  rw [Finset.sum_congr rfl (fun w _ => hA w), hD, ← Finset.sum_div]
  unfold levT
  rw [← one_div_mul_one_div]
  ring

/-- Bounded increments of `occ · i` along the support of the kernel. -/
theorem inc_occ (z x : Fin N → ℕ) (hx : lbKernel lam M N route z x ≠ 0) (i : ℕ) :
    |occ x i - occ z i| ≤ 1 / (N : ℝ) := by
  obtain ⟨v, hv | hv⟩ := lb_support lam M N route z x hx <;> subst hv
  · rw [occ_arr, abs_div, Nat.abs_cast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    split_ifs <;> first | (exfalso; omega) | norm_num
  · rw [occ_dep, abs_div, Nat.abs_cast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    split_ifs <;> first | (exfalso; omega) | norm_num

/-- Bounded increments of the tail `tl k` along the support of the kernel. -/
theorem inc_tl (k : ℕ) (hk : 1 ≤ k) (z x : Fin N → ℕ) (hx : lbKernel lam M N route z x ≠ 0) :
    |tl k x - tl k z| ≤ 1 / (N : ℝ) := by
  obtain ⟨v, hv | hv⟩ := lb_support lam M N route z x hx <;> subst hv
  · rw [tl_arr, abs_div, Nat.abs_cast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    split_ifs <;> norm_num
  · rw [tl_dep k hk, abs_neg, abs_div, Nat.abs_cast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    split_ifs <;> norm_num

end Drift

end SC66D

namespace SC66V

open StrictCompatLB.MeanField PowerOfDUniversality.Fluid

/-! PLLN CHAIN conversions: l1dist (ENNReal) bounds to finite real sums. -/

theorem fin_le_l1 (f g : ℕ → ℝ) (I : Finset ℕ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : l1dist f g ≤ ENNReal.ofReal B) : ∑ i ∈ I, |f i - g i| ≤ B := by
  have h1 : ENNReal.ofReal (∑ i ∈ I, |f i - g i|) ≤ ENNReal.ofReal B := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
    exact (ENNReal.sum_le_tsum I).trans hB
  exact (ENNReal.ofReal_le_ofReal_iff hB0).mp h1

theorem xOf_l1 (q q' : ℕ → ℝ) :
    l1dist (fun j => q j - q (j + 1)) (fun j => q' j - q' (j + 1)) ≤ 2 * l1dist q q' := by
  unfold l1dist
  calc ∑' j, ENNReal.ofReal |q j - q (j + 1) - (q' j - q' (j + 1))|
      ≤ ∑' j, (ENNReal.ofReal |q j - q' j| + ENNReal.ofReal |q (j + 1) - q' (j + 1)|) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        rw [show q j - q (j + 1) - (q' j - q' (j + 1)) =
          (q j - q' j) - (q (j + 1) - q' (j + 1)) by ring]
        exact abs_sub _ _
    _ = ∑' j, ENNReal.ofReal |q j - q' j| + ∑' j, ENNReal.ofReal |q (j + 1) - q' (j + 1)| :=
        ENNReal.tsum_add
    _ ≤ ∑' j, ENNReal.ofReal |q j - q' j| + ∑' j, ENNReal.ofReal |q j - q' j| := by
        exact add_le_add le_rfl (ENNReal.tsum_comp_le_tsum_of_injective (f := fun j : ℕ => j + 1)
          (add_left_injective 1) (fun i => ENNReal.ofReal |q i - q' i|))
    _ = 2 * ∑' j, ENNReal.ofReal |q j - q' j| := (two_mul _).symm

lemma occ_eq {N : ℕ} (z : Fin N → ℕ) (i : ℕ) :
    occ z i = (∑ u, (if i ≤ z u then (1 : ℝ) else 0)) / (N : ℝ) := by
  unfold occ Qcount
  rw [Finset.natCast_card_filter]

lemma geqd_eq' {N : ℕ} (z : Fin N → ℕ) (i : ℕ) :
    geqd z i = (∑ u, (if z u = i then (1 : ℝ) else 0)) / (N : ℝ) := by
  unfold geqd
  rw [Finset.natCast_card_filter]

theorem geqd_xOf {N : ℕ} (z : Fin N → ℕ) : geqd z = fun j => occ z j - occ z (j + 1) := by
  funext i
  rw [geqd_eq', occ_eq, occ_eq, ← sub_div, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun u _ => ?_
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- `l1dist q S` is bounded by the head `1..L` plus both tails beyond `L`. -/
theorem l1_le_E (q S : ℕ → ℝ) (hq0 : q 0 = S 0) (hqn : ∀ i, 0 ≤ q i) (hSn : ∀ i, 0 ≤ S i)
    (L : ℕ) (Tq TS : ℝ) (hTq : HasSum (fun j => q (L + 1 + j)) Tq)
    (hTS : HasSum (fun j => S (L + 1 + j)) TS) :
    l1dist q S ≤ ENNReal.ofReal (∑ i ∈ Icc 1 L, |q i - S i| + Tq + TS) := by
  unfold l1dist
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hsub : ∑ i ∈ range n, |q i - S i| ≤ ∑ i ∈ range (n + L + 1), |q i - S i| :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun _ _ _ => abs_nonneg _)
  refine hsub.trans ?_
  rw [← sum_range_add_sum_Ico _ (show L + 1 ≤ n + L + 1 by omega), range_eq_Ico,
    sum_eq_sum_Ico_succ_bot (show 0 < L + 1 by omega), hq0, sub_self, abs_zero, zero_add]
  have hI : Ico (0 + 1) (L + 1) = Icc 1 L := by ext i; simp only [mem_Ico, mem_Icc]; omega
  rw [hI]
  have htail : ∑ i ∈ Ico (L + 1) (n + L + 1), |q i - S i| ≤ Tq + TS := by
    have e1 : ∑ i ∈ Ico (L + 1) (n + L + 1), |q i - S i| ≤
        ∑ i ∈ Ico (L + 1) (n + L + 1), (q i + S i) := by
      refine sum_le_sum fun i _ => ?_
      have := hqn i; have := hSn i
      rw [abs_le]; constructor <;> linarith
    refine e1.trans ?_
    rw [sum_add_distrib, sum_Ico_eq_sum_range, sum_Ico_eq_sum_range]
    exact add_le_add (sum_le_hasSum _ (fun j _ => hqn _) hTq)
      (sum_le_hasSum _ (fun j _ => hSn _) hTS)
  linarith

/-- A tail sum bounded by its finite pieces. -/
theorem tail_le (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (L : ℕ) (T τ : ℝ)
    (hT : HasSum (fun j => f (L + j)) T) (hfin : ∀ n, ∑ i ∈ Ico L n, f i ≤ τ) : T ≤ τ := by
  rw [← hT.tsum_eq]
  refine Real.tsum_le_of_sum_range_le (fun j => hf _) fun n => ?_
  have := hfin (L + n)
  rwa [sum_Ico_eq_sum_range, show L + n - L = n by omega] at this

/-- `levT z (L+1)` is the tail `∑_{j ≥ L} levA z j`. -/
theorem levT_hasSum (M : ℕ → ℕ) (N : ℕ) (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (z : Fin N → ℕ) (L : ℕ) :
    HasSum (fun j => SC66D.levA M N route z (L + j)) (SC66D.levT M N route z (L + 1)) := by
  set B := univ.sup z + 1 with hB
  have hz : ∀ v, z v < B := fun v => Nat.lt_succ_of_le (le_sup (mem_univ v))
  have hzero : ∀ j ∉ range B, SC66D.levA M N route z (L + j) = 0 := by
    intro j hj
    rw [mem_range, not_lt] at hj
    unfold SC66D.levA
    rw [Finset.sum_eq_zero (fun w _ => ?_), mul_zero]
    exact sum_eq_zero fun v hv => absurd (mem_filter.mp hv).2 (by have := hz v; omega)
  have hS : HasSum (fun j => SC66D.levA M N route z (L + j))
      (∑ j ∈ range B, SC66D.levA M N route z (L + j)) := hasSum_sum_of_ne_finset_zero hzero
  convert hS using 1
  unfold SC66D.levA SC66D.levT
  rw [← mul_sum]
  congr 1
  symm
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  simp only [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  by_cases hv : L + 1 ≤ z v + 1
  · rw [if_pos hv, sum_eq_single (z v - L)]
    · rw [if_pos (by omega)]
    · intro j _ hj; rw [if_neg (by omega)]
    · intro hj; rw [mem_range] at hj; have := hz v; omega
  · rw [if_neg hv, sum_eq_zero]
    intro j _; rw [if_neg (by omega)]

end SC66V


namespace SC66H

/-! PLLN CHAIN, deterministic part: pathwise l1 Gronwall comparison and the Euler step error. -/

theorem gronwall (e : ℕ → ℝ) (A c : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (m : ℕ)
    (h : ∀ n ≤ m, e n ≤ A + c * ∑ k ∈ range n, e k) :
    ∀ n ≤ m, e n ≤ A * Real.exp (c * n) := by
  have hS : ∀ n ≤ m, A + c * ∑ k ∈ range n, e k ≤ A * (1 + c) ^ n := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have hen := h n (by omega)
      rw [Finset.sum_range_succ, pow_succ]
      have : c * e n ≤ c * (A + c * ∑ k ∈ range n, e k) := mul_le_mul_of_nonneg_left hen hc
      nlinarith
  intro n hn
  refine (h n hn).trans ((hS n hn).trans ?_)
  apply mul_le_mul_of_nonneg_left _ hA
  calc (1 + c) ^ n ≤ (Real.exp c) ^ n := by
        gcongr
        linarith [Real.add_one_le_exp c]
    _ = Real.exp (c * n) := by rw [← Real.exp_nat_mul]; ring_nf

/-- One Euler step of a trajectory whose derivative is Lipschitz in time. -/
theorem riem (s : ℝ → ℕ → ℝ) (i : ℕ) (Fv : ℝ → ℝ)
    (hder : ∀ u : ℝ, 0 ≤ u → HasDerivWithinAt (fun v => s v i) (Fv u) (Set.Ici 0) u)
    (C1 t h : ℝ) (ht : 0 ≤ t) (hh : 0 ≤ h)
    (hFl : ∀ u : ℝ, t ≤ u → u ≤ t + h → |Fv u - Fv t| ≤ C1 * h) :
    |s (t + h) i - s t i - h * Fv t| ≤ C1 * h * h := by
  let g : ℝ → ℝ := fun v => s v i - v * Fv t
  have hd : ∀ u ∈ Set.Icc t (t + h),
      HasDerivWithinAt g (Fv u - Fv t) (Set.Icc t (t + h)) u := by
    intro u hu
    have h1 := (hder u (ht.trans hu.1)).mono (fun v (hv : v ∈ Set.Icc t (t + h)) => Set.mem_Ici.mpr (ht.trans hv.1))
    have h2 := h1.fun_sub ((hasDerivWithinAt_id u (Set.Icc t (t + h))).mul_const (Fv t))
    simpa [g] using h2
  have hb : ∀ u ∈ Set.Icc t (t + h), ‖Fv u - Fv t‖ ≤ C1 * h := fun u hu => by
    rw [Real.norm_eq_abs]; exact hFl u hu.1 hu.2
  have key := (convex_Icc t (t + h)).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
  simp only [g, Real.norm_eq_abs] at key
  have e1 : t + h - t = h := by ring
  rw [e1, abs_of_nonneg hh] at key
  convert key using 2; ring

/-- Pathwise comparison: coordinates `1..L` plus tails, closed by Gronwall. -/
theorem pathbound (q S A Pq P : ℕ → ℕ → ℝ) (Tq TS E : ℕ → ℝ)
    (h lam K a r η τp τs e0 T2 : ℝ) (L m : ℕ)
    (hh : 0 ≤ h) (hlam : 0 ≤ lam) (hK : 0 ≤ K) (ha : 0 ≤ a) (hr : 0 ≤ r) (hη : 0 ≤ η)
    (hτp : 0 ≤ τp) (hτs : 0 ≤ τs) (hT2 : (m : ℝ) * h ≤ T2)
    (hE : ∀ n, E n = ∑ i ∈ Icc 1 L, |q n i - S n i| + Tq n + TS n)
    (hTS : ∀ n, 0 ≤ TS n) (hTq : ∀ n, 0 ≤ Tq n)
    (H1 : ∀ n ≤ m, ∀ i ∈ Icc 1 L, |q n i - q 0 i -
        ∑ k ∈ range n, h * (lam * A k (i - 1) - (q k i - q k (i + 1)))| ≤ a)
    (H2 : ∀ n ≤ m, ∀ i ∈ Icc 1 L, |S n i - S 0 i -
        ∑ k ∈ range n, h * (lam * P k (i - 1) - (S k i - S k (i + 1)))| ≤ r)
    (H3 : ∀ k < m, ∑ i ∈ Icc 1 L, |A k (i - 1) - Pq k (i - 1)| ≤ η)
    (H4 : ∀ k < m, ∑ i ∈ Icc 1 L, |Pq k (i - 1) - P k (i - 1)| ≤ 2 * K * E k)
    (H5 : ∀ k < m, ∑ i ∈ Icc 1 L,
        |(q k i - q k (i + 1)) - (S k i - S k (i + 1))| ≤ 2 * E k)
    (H6 : ∀ n ≤ m, Tq n ≤ Tq 0 + a + ∑ k ∈ range n, h * (lam * (η + τp + 2 * K * E k)))
    (H7 : ∀ n ≤ m, TS n ≤ τs)
    (H8 : E 0 ≤ e0) :
    ∀ n ≤ m, E n ≤ (e0 + (L + 1) * a + L * r + τs + T2 * (lam * (2 * η + τp))) *
      Real.exp ((4 * lam * K + 2) * T2) := by
  have hE0 : ∀ n, 0 ≤ E n := fun n => by
    rw [hE]
    exact add_nonneg (add_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (hTq n)) (hTS n)
  have hT20 : 0 ≤ T2 := le_trans (by positivity) hT2
  set A0 := e0 + (L + 1) * a + L * r + τs + T2 * (lam * (2 * η + τp)) with hA0
  set c := h * (4 * lam * K + 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have he00 : 0 ≤ e0 := (hE0 0).trans H8
  have hA00 : 0 ≤ A0 := by positivity
  have step : ∀ n ≤ m, E n ≤ A0 + c * ∑ k ∈ range n, E k := by
    intro n hn
    -- coordinatewise bound
    have hi : ∀ i ∈ Icc 1 L, |q n i - S n i| ≤ |q 0 i - S 0 i| + a + r +
        ∑ k ∈ range n, h * (lam * |A k (i - 1) - Pq k (i - 1)| +
          lam * |Pq k (i - 1) - P k (i - 1)| +
          |(q k i - q k (i + 1)) - (S k i - S k (i + 1))|) := by
      intro i hi
      have h1 := abs_le.mp (H1 n hn i hi)
      have h2 := abs_le.mp (H2 n hn i hi)
      have hd : |∑ k ∈ range n, h * (lam * A k (i - 1) - (q k i - q k (i + 1))) -
          ∑ k ∈ range n, h * (lam * P k (i - 1) - (S k i - S k (i + 1)))| ≤
          ∑ k ∈ range n, h * (lam * |A k (i - 1) - Pq k (i - 1)| +
            lam * |Pq k (i - 1) - P k (i - 1)| +
            |(q k i - q k (i + 1)) - (S k i - S k (i + 1))|) := by
        rw [← sum_sub_distrib]
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
        rw [show h * (lam * A k (i - 1) - (q k i - q k (i + 1))) -
            h * (lam * P k (i - 1) - (S k i - S k (i + 1))) =
            h * (lam * (A k (i - 1) - Pq k (i - 1)) + lam * (Pq k (i - 1) - P k (i - 1)) -
              ((q k i - q k (i + 1)) - (S k i - S k (i + 1)))) by ring,
          abs_mul, abs_of_nonneg hh]
        apply mul_le_mul_of_nonneg_left _ hh
        have a1 := mul_le_mul_of_nonneg_left (le_abs_self (A k (i - 1) - Pq k (i - 1))) hlam
        have a2 := mul_le_mul_of_nonneg_left (neg_abs_le (A k (i - 1) - Pq k (i - 1))) hlam
        have a3 := mul_le_mul_of_nonneg_left (le_abs_self (Pq k (i - 1) - P k (i - 1))) hlam
        have a4 := mul_le_mul_of_nonneg_left (neg_abs_le (Pq k (i - 1) - P k (i - 1))) hlam
        have a5 := le_abs_self ((q k i - q k (i + 1)) - (S k i - S k (i + 1)))
        have a6 := neg_abs_le ((q k i - q k (i + 1)) - (S k i - S k (i + 1)))
        rw [abs_le]; constructor <;> nlinarith
      have hd' := abs_le.mp hd
      have b1 := le_abs_self (q 0 i - S 0 i)
      have b2 := neg_abs_le (q 0 i - S 0 i)
      rw [abs_le]; constructor <;> linarith
    have hsumi : ∑ i ∈ Icc 1 L, |q n i - S n i| ≤ ∑ i ∈ Icc 1 L, |q 0 i - S 0 i| +
        (L : ℝ) * (a + r) + ∑ k ∈ range n, h * (lam * η + lam * (2 * K * E k) + 2 * E k) := by
      refine (sum_le_sum hi).trans ?_
      rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_const, sum_const,
        Nat.card_Icc, sum_comm, nsmul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
      have : ∑ k ∈ range n, ∑ i ∈ Icc 1 L, h * (lam * |A k (i - 1) - Pq k (i - 1)| +
            lam * |Pq k (i - 1) - P k (i - 1)| +
            |(q k i - q k (i + 1)) - (S k i - S k (i + 1))|) ≤
          ∑ k ∈ range n, h * (lam * η + lam * (2 * K * E k) + 2 * E k) := by
        refine sum_le_sum fun k hk => ?_
        have hkm : k < m := lt_of_lt_of_le (mem_range.mp hk) hn
        rw [← mul_sum, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]
        apply mul_le_mul_of_nonneg_left _ hh
        have := H3 k hkm; have := H4 k hkm; have := H5 k hkm
        have := mul_le_mul_of_nonneg_left (H3 k hkm) hlam
        have := mul_le_mul_of_nonneg_left (H4 k hkm) hlam
        linarith
      linarith
    have hT6 := H6 n hn
    have hT7 := H7 n hn
    have hE0' := hE 0
    have hTS0 := hTS 0
    have hcomb : ∑ k ∈ range n, h * (lam * η + lam * (2 * K * E k) + 2 * E k) +
        ∑ k ∈ range n, h * (lam * (η + τp + 2 * K * E k)) =
        (n : ℝ) * h * (lam * (2 * η + τp)) + c * ∑ k ∈ range n, E k := by
      rw [← sum_add_distrib, hc, mul_sum]
      rw [show (n : ℝ) * h * (lam * (2 * η + τp)) = ∑ k ∈ range n, h * (lam * (2 * η + τp)) by
        rw [sum_const, card_range, nsmul_eq_mul]; ring, ← sum_add_distrib]
      exact sum_congr rfl fun k _ => by ring
    have hnT : (n : ℝ) * h * (lam * (2 * η + τp)) ≤ T2 * (lam * (2 * η + τp)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hh) hT2
    rw [hE n]
    linarith
  intro n hn
  refine (gronwall E A0 c hA00 hc0 m step n hn).trans ?_
  apply mul_le_mul_of_nonneg_left _ hA00
  apply Real.exp_le_exp.mpr
  rw [hc]
  have : (n : ℝ) * h ≤ T2 := le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hh) hT2
  have h42 : 0 ≤ 4 * lam * K + 2 := by positivity
  nlinarith

end SC66H

namespace SC66J

open StrictCompatLB.MeanField PowerOfDUniversality.Fluid

theorem reidx (f : ℕ → ℝ) (L : ℕ) : ∑ i ∈ Icc 1 L, f (i - 1) = ∑ j ∈ range L, f j := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]
    simp

/-- Euler sums along the grid `k * h`. -/
theorem euler (s : ℝ → ℕ → ℝ) (i : ℕ) (Fv : ℝ → ℝ)
    (hder : ∀ u : ℝ, 0 ≤ u → HasDerivWithinAt (fun v => s v i) (Fv u) (Set.Ici 0) u)
    (C1 h : ℝ) (hh : 0 ≤ h)
    (hFl : ∀ t u : ℝ, 0 ≤ t → t ≤ u → u ≤ t + h → |Fv u - Fv t| ≤ C1 * h) (n : ℕ) :
    |s (n * h) i - s 0 i - ∑ k ∈ range n, h * Fv (k * h)| ≤ n * (C1 * h * h) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hk : 0 ≤ (n : ℝ) * h := by positivity
    have hr := SC66H.riem s i Fv hder C1 (n * h) h hk hh (fun u h1 h2 => hFl _ u hk h1 h2)
    have e : ((n + 1 : ℕ) : ℝ) * h = n * h + h := by push_cast; ring
    rw [e, sum_range_succ]
    have e2 : s (↑n * h + h) i - s 0 i - (∑ k ∈ range n, h * Fv (↑k * h) + h * Fv (↑n * h)) =
        (s (n * h) i - s 0 i - ∑ k ∈ range n, h * Fv (k * h)) +
          (s (n * h + h) i - s (n * h) i - h * Fv (n * h)) := by ring
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    have e3 : ((n + 1 : ℕ) : ℝ) * (C1 * h * h) = n * (C1 * h * h) + C1 * h * h := by push_cast; ring
    rw [e3]; exact add_le_add ih hr

/-- PLLN CHAIN, deterministic instantiation for one sample path. -/
theorem chain_det (lam K h T2 a η τp τs e0 : ℝ) (L m : ℕ)
    (hlam : 0 ≤ lam) (hK : 0 ≤ K) (hh : 0 ≤ h) (ha : 0 ≤ a) (hη : 0 ≤ η) (hτp : 0 ≤ τp)
    (hτs : 0 ≤ τs) (hT2 : (m : ℝ) * h ≤ T2)
    (p : (ℕ → ℝ) → ℕ → ℝ) (hpK : IsLipschitzPolicyWith p K)
    (s : ℝ → ℕ → ℝ) (hs : IsPiTrajectory lam p s)
    (hsn : ∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ s t i) (hs0 : ∀ t : ℝ, 0 ≤ t → s t 0 = 1)
    (hsX : ∀ t : ℝ, 0 ≤ t → InX (fun j => s t j - s t (j + 1)))
    (hlip : ∀ t u : ℝ, 0 ≤ t → 0 ≤ u →
      l1dist (s u) (s t) ≤ ENNReal.ofReal ((lam + 1) * |u - t|))
    (TS : ℕ → ℝ) (hTS : ∀ n : ℕ, HasSum (fun j => s (n * h) (L + 1 + j)) (TS n))
    (hτsb : ∀ n ≤ m, ∀ n', ∑ i ∈ Ico (L + 1) n', s (n * h) i ≤ τs)
    (hτpb : ∀ k < m, ∀ n', ∑ i ∈ Ico L n', p (fun j => s (k * h) j - s (k * h) (j + 1)) i ≤ τp)
    (q A : ℕ → ℕ → ℝ) (Tq AT : ℕ → ℝ)
    (hqn : ∀ n i, 0 ≤ q n i) (hq0 : ∀ n, q n 0 = 1)
    (hqX : ∀ n, InX (fun j => q n j - q n (j + 1)))
    (hTq : ∀ n, HasSum (fun j => q n (L + 1 + j)) (Tq n))
    (hA0 : ∀ k j, 0 ≤ A k j)
    (hAT : ∀ k, HasSum (fun j => A k (L + j)) (AT k))
    (hgood : ∀ k < m, l1dist (A k) (p (fun j => q k j - q k (j + 1))) ≤ ENNReal.ofReal η)
    (H1 : ∀ n ≤ m, ∀ i ∈ Icc 1 L, |q n i - q 0 i -
        ∑ k ∈ range n, h * (lam * A k (i - 1) - (q k i - q k (i + 1)))| ≤ a)
    (Ht : ∀ n ≤ m, |Tq n - Tq 0 - ∑ k ∈ range n, h * (lam * AT k - q k (L + 1))| ≤ a)
    (H8 : ∑ i ∈ Icc 1 L, |q 0 i - s 0 i| + Tq 0 + TS 0 ≤ e0) :
    ∀ n ≤ m, l1dist (q n) (s (n * h)) ≤ ENNReal.ofReal
      ((e0 + (L + 1) * a + L * (m * (2 * (lam + 1) * (lam * K + 1) * h * h)) + τs +
        T2 * (lam * (2 * η + τp))) * Real.exp ((4 * lam * K + 2) * T2)) := by
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℝ, ∀ n, E n =
      ∑ i ∈ Icc 1 L, |q n i - s (n * h) i| + Tq n + TS n := ⟨_, fun n => rfl⟩
  have hkh : ∀ k : ℕ, 0 ≤ (k : ℝ) * h := fun k => mul_nonneg (Nat.cast_nonneg _) hh
  have hTq0 : ∀ n, 0 ≤ Tq n := fun n => (hTq n).nonneg fun j => hqn _ _
  have hTS0 : ∀ n, 0 ≤ TS n := fun n => (hTS n).nonneg fun j => hsn _ (hkh n) _
  have hE0 : ∀ n, 0 ≤ E n := fun n => by
    rw [hE]; exact add_nonneg (add_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (hTq0 n)) (hTS0 n)
  have lipP : ∀ x y, InX x → InX y → ∀ B, 0 ≤ B → l1dist x y ≤ ENNReal.ofReal B →
      l1dist (p x) (p y) ≤ ENNReal.ofReal (K * B) := by
    intro x y hx hy B _ hxy
    refine (hpK x y hx hy).trans ?_
    rw [ENNReal.ofReal_mul hK]; gcongr
  have lipX : ∀ f g : ℕ → ℝ, ∀ B, 0 ≤ B → l1dist f g ≤ ENNReal.ofReal B →
      l1dist (fun j => f j - f (j + 1)) (fun j => g j - g (j + 1)) ≤ ENNReal.ofReal (2 * B) := by
    intro f g B _ hfg
    refine (SC66V.xOf_l1 f g).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]; gcongr
  have hqS : ∀ k : ℕ, l1dist (q k) (s (k * h)) ≤ ENNReal.ofReal (E k) := fun k => by
    rw [hE]
    exact SC66V.l1_le_E (q k) (s (k * h)) (by rw [hq0, hs0 _ (hkh k)]) (hqn k) (hsn _ (hkh k))
      L (Tq k) (TS k) (hTq k) (hTS k)
  have hPP : ∀ k : ℕ, l1dist (p (fun j => q k j - q k (j + 1)))
      (p (fun j => s (k * h) j - s (k * h) (j + 1))) ≤ ENNReal.ofReal (K * (2 * E k)) := fun k =>
    lipP _ _ (hqX k) (hsX _ (hkh k)) _ (by linarith [hE0 k]) (lipX _ _ _ (hE0 k) (hqS k))
  -- Euler step error
  have hFl : ∀ i : ℕ, ∀ t u : ℝ, 0 ≤ t → t ≤ u → u ≤ t + h →
      |(lam * p (fun j => s u j - s u (j + 1)) (i - 1) - (s u i - s u (i + 1))) -
        (lam * p (fun j => s t j - s t (j + 1)) (i - 1) - (s t i - s t (i + 1)))| ≤
        2 * (lam + 1) * (lam * K + 1) * h := by
    intro i t u ht htu hu
    have hu0 : 0 ≤ u := ht.trans htu
    have hB0 : 0 ≤ (lam + 1) * h := mul_nonneg (by linarith) hh
    have hd : l1dist (s u) (s t) ≤ ENNReal.ofReal ((lam + 1) * h) := by
      refine (hlip t u ht hu0).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [abs_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e1 := SC66V.fin_le_l1 _ _ {i} _ hB0 hd
    have e2 := SC66V.fin_le_l1 _ _ {i + 1} _ hB0 hd
    have e3 := SC66V.fin_le_l1 _ _ {i - 1} _ (mul_nonneg hK (by linarith))
      (lipP _ _ (hsX u hu0) (hsX t ht) _ (by linarith) (lipX _ _ _ hB0 hd))
    simp only [sum_singleton] at e1 e2 e3
    have e4 := mul_le_mul_of_nonneg_left e3 hlam
    have a1 := le_abs_self (p (fun j => s u j - s u (j + 1)) (i - 1) - p (fun j => s t j - s t (j + 1)) (i - 1))
    have a2 := neg_abs_le (p (fun j => s u j - s u (j + 1)) (i - 1) - p (fun j => s t j - s t (j + 1)) (i - 1))
    have a3 := le_abs_self (s u i - s t i)
    have a4 := neg_abs_le (s u i - s t i)
    have a5 := le_abs_self (s u (i + 1) - s t (i + 1))
    have a6 := neg_abs_le (s u (i + 1) - s t (i + 1))
    have m1 := mul_le_mul_of_nonneg_left a1 hlam
    have m2 := mul_le_mul_of_nonneg_left a2 hlam
    rw [abs_le]; constructor <;> nlinarith
  have hl1 : 0 ≤ lam + 1 := by linarith
  have hlK : 0 ≤ lam * K + 1 := by nlinarith [mul_nonneg hlam hK]
  have hC0 : 0 ≤ 2 * (lam + 1) * (lam * K + 1) * h * h :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hl1) hlK) hh) hh
  have H2 : ∀ n ≤ m, ∀ i ∈ Icc 1 L, |s (n * h) i - s (((0 : ℕ) : ℝ) * h) i -
      ∑ k ∈ range n, h * (lam * p (fun j => s (k * h) j - s (k * h) (j + 1)) (i - 1) -
        (s (k * h) i - s (k * h) (i + 1)))| ≤ m * (2 * (lam + 1) * (lam * K + 1) * h * h) := by
    intro n hn i hi
    rw [Nat.cast_zero, zero_mul]
    have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
    refine (euler s i (fun u => lam * p (fun j => s u j - s u (j + 1)) (i - 1) - (s u i - s u (i + 1)))
      (fun u hu => hs.2 i hi1 u hu) (2 * (lam + 1) * (lam * K + 1)) h hh (hFl i) n).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hC0
  have H3 : ∀ k < m, ∑ i ∈ Icc 1 L, |A k (i - 1) - p (fun j => q k j - q k (j + 1)) (i - 1)| ≤ η := by
    intro k hk
    have r := reidx (fun j => |A k j - p (fun j => q k j - q k (j + 1)) j|) L
    beta_reduce at r
    rw [r]
    exact SC66V.fin_le_l1 _ _ _ _ hη (hgood k hk)
  have H4 : ∀ k < m, ∑ i ∈ Icc 1 L, |p (fun j => q k j - q k (j + 1)) (i - 1) -
      p (fun j => s (k * h) j - s (k * h) (j + 1)) (i - 1)| ≤ 2 * K * E k := by
    intro k _
    have r := reidx (fun j => |p (fun j => q k j - q k (j + 1)) j -
      p (fun j => s (k * h) j - s (k * h) (j + 1)) j|) L
    beta_reduce at r
    rw [r, show 2 * K * E k = K * (2 * E k) by ring]
    exact SC66V.fin_le_l1 _ _ _ _ (mul_nonneg hK (by linarith [hE0 k])) (hPP k)
  have H5 : ∀ k < m, ∑ i ∈ Icc 1 L,
      |(q k i - q k (i + 1)) - (s (k * h) i - s (k * h) (i + 1))| ≤ 2 * E k := by
    intro k _
    exact SC66V.fin_le_l1 _ _ _ _ (by linarith [hE0 k]) (lipX _ _ _ (hE0 k) (hqS k))
  have hATb : ∀ k < m, AT k ≤ η + τp + 2 * K * E k := by
    intro k hk
    refine SC66V.tail_le (A k) (hA0 k) L _ _ (hAT k) fun n' => ?_
    have g1 := SC66V.fin_le_l1 _ _ (Ico L n') η hη (hgood k hk)
    have g2 := SC66V.fin_le_l1 _ _ (Ico L n') _ (mul_nonneg hK (by linarith [hE0 k])) (hPP k)
    have g3 := hτpb k hk n'
    have g4 : ∑ i ∈ Ico L n', A k i ≤ ∑ i ∈ Ico L n', (|A k i - p (fun j => q k j - q k (j + 1)) i| +
        |p (fun j => q k j - q k (j + 1)) i - p (fun j => s (k * h) j - s (k * h) (j + 1)) i| +
        p (fun j => s (k * h) j - s (k * h) (j + 1)) i) := sum_le_sum fun i _ => by
      have := le_abs_self (A k i - p (fun j => q k j - q k (j + 1)) i)
      have := le_abs_self (p (fun j => q k j - q k (j + 1)) i -
        p (fun j => s (k * h) j - s (k * h) (j + 1)) i)
      linarith
    rw [sum_add_distrib, sum_add_distrib] at g4
    linarith
  have H6 : ∀ n ≤ m, Tq n ≤ Tq 0 + a + ∑ k ∈ range n, h * (lam * (η + τp + 2 * K * E k)) := by
    intro n hn
    have h1 := (abs_le.mp (Ht n hn)).2
    have h2 : ∑ k ∈ range n, h * (lam * AT k - q k (L + 1)) ≤
        ∑ k ∈ range n, h * (lam * (η + τp + 2 * K * E k)) := by
      refine sum_le_sum fun k hk => ?_
      have hkm : k < m := lt_of_lt_of_le (mem_range.mp hk) hn
      apply mul_le_mul_of_nonneg_left _ hh
      have := mul_le_mul_of_nonneg_left (hATb k hkm) hlam
      have := hqn k (L + 1)
      nlinarith
    linarith
  have H7 : ∀ n ≤ m, TS n ≤ τs := fun n hn =>
    SC66V.tail_le (s (n * h)) (hsn _ (hkh n)) (L + 1) _ _ (hTS n) (hτsb n hn)
  have H8' : E 0 ≤ e0 := by rw [hE, Nat.cast_zero, zero_mul]; exact H8
  intro n hn
  refine (hqS n).trans (ENNReal.ofReal_le_ofReal ?_)
  exact SC66H.pathbound q (fun n => s (n * h)) A (fun k => p (fun j => q k j - q k (j + 1)))
    (fun k => p (fun j => s (k * h) j - s (k * h) (j + 1))) Tq TS E h lam K a
    (m * (2 * (lam + 1) * (lam * K + 1) * h * h)) η τp τs e0 T2 L m hh hlam hK ha
    (mul_nonneg (Nat.cast_nonneg _) hC0) hη hτp hτs hT2 hE hTS0 hTq0 H1 H2 H3 H4 H5 H6 H7 H8' n hn

end SC66J


namespace SC66P

open StrictCompatLB.MeanField PowerOfDUniversality.Fluid

lemma occ_zero {N : ℕ} (hN : 1 ≤ N) (z : Fin N → ℕ) : occ z 0 = 1 := by
  classical
  have h : Qcount z 0 = N := by unfold Qcount; simp
  unfold occ
  rw [h]
  exact div_self (Nat.cast_ne_zero.mpr (by omega))

lemma occ_nonneg' {N : ℕ} (z : Fin N → ℕ) (i : ℕ) : 0 ≤ occ z i := by
  unfold occ; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma levA_nonneg (M : ℕ → ℕ) (N : ℕ) (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (hr : ∀ w z v, 0 ≤ route w z v) (z : Fin N → ℕ) (i : ℕ) : 0 ≤ SC66D.levA M N route z i := by
  unfold SC66D.levA
  exact mul_nonneg (by positivity) (sum_nonneg fun w _ => sum_nonneg fun v _ => hr w z v)

/-- PLLN CHAIN for one sample path of the LB chain, at a step `n` before which the routing law
stayed `η`-good. -/
theorem chain_path (lam K T2 a η τp τs e0 : ℝ) (L N n : ℕ) (hN : 1 ≤ N)
    (hlam : 0 ≤ lam) (hK : 0 ≤ K) (ha : 0 ≤ a) (hη : 0 ≤ η) (hτp : 0 ≤ τp) (hτs : 0 ≤ τs)
    (hT2 : (n : ℝ) * (1 / ((lam + 1) * N)) ≤ T2)
    (M : ℕ → ℕ) (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ) (hr : ∀ w z v, 0 ≤ route w z v)
    (hgX : ∀ z : Fin N → ℕ, InX (geqd z))
    (p : (ℕ → ℝ) → ℕ → ℝ) (hpK : IsLipschitzPolicyWith p K)
    (s : ℝ → ℕ → ℝ) (hs : IsPiTrajectory lam p s)
    (hsn : ∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ s t i) (hs0 : ∀ t : ℝ, 0 ≤ t → s t 0 = 1)
    (hsX : ∀ t : ℝ, 0 ≤ t → InX (fun j => s t j - s t (j + 1)))
    (hlip : ∀ t u : ℝ, 0 ≤ t → 0 ≤ u →
      l1dist (s u) (s t) ≤ ENNReal.ofReal ((lam + 1) * |u - t|))
    (TS : ℕ → ℝ)
    (hTS : ∀ k : ℕ, HasSum (fun j => s (k * (1 / ((lam + 1) * N))) (L + 1 + j)) (TS k))
    (hτsb : ∀ k ≤ n, ∀ n', ∑ i ∈ Ico (L + 1) n', s (k * (1 / ((lam + 1) * N))) i ≤ τs)
    (hτpb : ∀ k < n, ∀ n', ∑ i ∈ Ico L n', p (fun j => s (k * (1 / ((lam + 1) * N))) j -
      s (k * (1 / ((lam + 1) * N))) (j + 1)) i ≤ τp)
    (ys : ℕ → Fin N → ℕ)
    (hgood : ∀ k < n, l1dist (SC66D.levA M N route (ys k)) (p (geqd (ys k))) ≤ ENNReal.ofReal η)
    (H1 : ∀ n' ≤ n, ∀ i ∈ Icc 1 L, |occ (ys n') i - occ (ys 0) i - ∑ k ∈ range n',
        1 / ((lam + 1) * N) * (lam * SC66D.levA M N route (ys k) (i - 1) - geqd (ys k) i)| ≤ a)
    (Ht : ∀ n' ≤ n, |SC66D.tl (L + 1) (ys n') - SC66D.tl (L + 1) (ys 0) - ∑ k ∈ range n',
        1 / ((lam + 1) * N) * (lam * SC66D.levT M N route (ys k) (L + 1) - occ (ys k) (L + 1))| ≤ a)
    (H8 : ∑ i ∈ Icc 1 L, |occ (ys 0) i - s 0 i| + SC66D.tl (L + 1) (ys 0) + TS 0 ≤ e0) :
    l1dist (occ (ys n)) (s (n * (1 / ((lam + 1) * N)))) ≤ ENNReal.ofReal
      ((e0 + (L + 1) * a + L * (n * (2 * (lam + 1) * (lam * K + 1) * (1 / ((lam + 1) * N)) *
        (1 / ((lam + 1) * N)))) + τs + T2 * (lam * (2 * η + τp))) *
        Real.exp ((4 * lam * K + 2) * T2)) := by
  have hR : 0 < (lam + 1) * (N : ℝ) := mul_pos (by linarith) (by exact_mod_cast hN)
  refine SC66J.chain_det lam K (1 / ((lam + 1) * N)) T2 a η τp τs e0 L n hlam hK
    (one_div_pos.mpr hR).le ha hη hτp hτs hT2
    p hpK s hs hsn hs0 hsX hlip TS hTS hτsb hτpb (fun k => occ (ys k))
    (fun k => SC66D.levA M N route (ys k))
    (fun k => SC66D.tl (L + 1) (ys k)) (fun k => SC66D.levT M N route (ys k) (L + 1))
    (fun k i => occ_nonneg' _ _) (fun k => occ_zero hN _) ?_ (fun k => SC66D.occ_tail_hasSum _ _)
    (fun k j => levA_nonneg M N route hr _ _) (fun k => SC66V.levT_hasSum M N route _ L)
    ?_ ?_ Ht H8 n le_rfl
  · intro k; simpa only [SC66V.geqd_xOf] using hgX (ys k)
  · intro k hk; simpa only [SC66V.geqd_xOf] using hgood k hk
  · intro n' hn' i hi; simpa only [SC66V.geqd_xOf] using H1 n' hn' i hi

end SC66P

end
section
open Filter Topology MeasureTheory
open scoped ENNReal

namespace SC66A

/-! K3d part 1: Markov property in integral form, derived from the cylinder formula of
`IsUniformizedProcess`. Used (a) to show that the coupled chain `Z` built on `Ω × E` from the
given chain `Y` and independent random maps is a `piRoute` chain, and (b) for the drift of the
mismatch count `D`. -/

section Markov

variable {S : Type} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] [DecidableEq S]

/-- The path prefix `(Y 0, …, Y n)`. -/
def pre {Ω : Type*} (Y : ℕ → Ω → S) (n : ℕ) (ω : Ω) : Fin (n + 1) → S := fun i => Y i ω

lemma measurable_pre {Ω : Type*} [MeasurableSpace Ω] (Y : ℕ → Ω → S)
    (hY : ∀ n, Measurable (Y n)) (n : ℕ) : Measurable (pre Y n) :=
  measurable_pi_lambda _ (fun i => hY i)

/-- The extension of a prefix `xs` by a last state `x'`. -/
def ext {n : ℕ} (xs : Fin (n + 1) → S) (x' : S) : ℕ → S :=
  fun j => if h : j ≤ n then xs ⟨j, by omega⟩ else x'

lemma pre_preimage {Ω : Type*} (Y : ℕ → Ω → S) (n : ℕ) (xs : Fin (n + 1) → S) (x' : S) :
    pre Y n ⁻¹' {xs} = {ω | ∀ j ≤ n, Y j ω = ext xs x' j} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · intro h j hj
    rw [ext, dif_pos hj, ← h]
    rfl
  · intro h
    funext i
    have := h i.1 (by omega)
    rw [ext, dif_pos (by omega)] at this
    exact this

lemma pair_preimage {Ω : Type*} (Y : ℕ → Ω → S) (n : ℕ) (xs : Fin (n + 1) → S) (x' : S) :
    (fun ω => (pre Y n ω, Y (n + 1) ω)) ⁻¹' {(xs, x')}
      = {ω | ∀ j ≤ n + 1, Y j ω = ext xs x' j} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩ j hj
    by_cases hjn : j ≤ n
    · rw [ext, dif_pos hjn, ← h1]; rfl
    · have : j = n + 1 := by omega
      subst this
      rw [ext, dif_neg (by omega)]; exact h2
  · intro h
    refine ⟨?_, ?_⟩
    · funext i
      have := h i.1 (by omega)
      rw [ext, dif_pos (by omega)] at this
      exact this
    · have := h (n + 1) le_rfl
      rw [ext, dif_neg (by omega)] at this
      exact this

/-- Markov property in integral form. -/
theorem markov_int {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (K : S → S → ℝ)
    (hK : ∀ a b, 0 ≤ K a b) (z₀ : S) (Y : ℕ → Ω → S) (hY : ∀ n, Measurable (Y n))
    (hcyl : ∀ (n : ℕ) (zs : ℕ → S), P {ω | ∀ j ≤ n, Y j ω = zs j} =
      ENNReal.ofReal ((if zs 0 = z₀ then 1 else 0) * ∏ j ∈ Finset.range n, K (zs j) (zs (j + 1))))
    (n : ℕ) (H : (Fin (n + 1) → S) → S → ℝ≥0∞) :
    ∫⁻ ω, H (pre Y n ω) (Y (n + 1) ω) ∂P
      = ∫⁻ ω, ∑' x', ENNReal.ofReal (K (Y n ω) x') * H (pre Y n ω) x' ∂P := by
  have hpre := measurable_pre Y hY n
  have hV : Measurable (fun ω => (pre Y n ω, Y (n + 1) ω)) := hpre.prodMk (hY _)
  have hL := lintegral_map (μ := P) (f := fun c : (Fin (n + 1) → S) × S => H c.1 c.2)
    (measurable_of_countable _) hV
  have hR := lintegral_map (μ := P)
    (f := fun xs : Fin (n + 1) → S => ∑' x', ENNReal.ofReal (K (xs (Fin.last n)) x') * H xs x')
    (measurable_of_countable _) hpre
  simp only at hL hR
  rw [← hL]
  have hR' : ∫⁻ ω, ∑' x', ENNReal.ofReal (K (Y n ω) x') * H (pre Y n ω) x' ∂P
      = ∫⁻ xs, ∑' x', ENNReal.ofReal (K (xs (Fin.last n)) x') * H xs x' ∂(P.map (pre Y n)) := by
    rw [hR]; rfl
  rw [hR', lintegral_countable', lintegral_countable']
  refine (ENNReal.tsum_prod (f := fun xs x' =>
    H xs x' * (P.map (fun ω => (pre Y n ω, Y (n + 1) ω))) {(xs, x')})).trans ?_
  apply tsum_congr
  intro xs
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro x'
  rw [Measure.map_apply hV (measurableSet_singleton _),
    Measure.map_apply hpre (measurableSet_singleton _),
    pair_preimage Y n xs x', pre_preimage Y n xs x', hcyl, hcyl, Finset.prod_range_succ]
  have hlast : ext xs x' n = xs (Fin.last n) := by rw [ext, dif_pos le_rfl]; rfl
  have hnext : ext xs x' (n + 1) = x' := by rw [ext, dif_neg (by omega)]
  rw [hlast, hnext]
  have hnn : 0 ≤ (if ext xs x' 0 = z₀ then (1 : ℝ) else 0) *
      ∏ j ∈ Finset.range n, K (ext xs x' j) (ext xs x' (j + 1)) := by
    apply mul_nonneg (by split_ifs <;> norm_num)
    exact Finset.prod_nonneg (fun j _ => hK _ _)
  rw [← mul_assoc, ENNReal.ofReal_mul hnn]
  ring


/-- The compensated increment sum `f(y_n) - f(y_0) - Σ_{k<n} d(y_k)`. -/
def G (f d : S → ℝ) (n : ℕ) (ys : ℕ → S) : ℝ :=
  f (ys n) - f (ys 0) - ∑ k ∈ Finset.range n, d (ys k)

lemma G_succ (f d : S → ℝ) (n : ℕ) (ys : ℕ → S) :
    G f d (n + 1) ys = G f d n ys + (f (ys (n + 1)) - f (ys n) - d (ys n)) := by
  simp only [G, Finset.sum_range_succ]; ring

lemma G_congr (f d : S → ℝ) (n : ℕ) (ys ys' : ℕ → S) (h : ∀ j ≤ n, ys j = ys' j) :
    G f d n ys = G f d n ys' := by
  unfold G
  rw [h n le_rfl, h 0 (Nat.zero_le _)]
  congr 1
  exact Finset.sum_congr rfl (fun k hk => by rw [h k (by simp at hk; omega)])

lemma G_neg (f d : S → ℝ) (n : ℕ) (ys : ℕ → S) :
    G (fun x => -f x) (fun x => -d x) n ys = -G f d n ys := by
  simp only [G, Finset.sum_neg_distrib]; ring

lemma ext_pre (Ω : Type*) (Y : ℕ → Ω → S) (n : ℕ) (ω : Ω) (x' : S) (j : ℕ) (hj : j ≤ n) :
    ext (pre Y n ω) x' j = Y j ω := by
  rw [ext, dif_pos hj]; rfl

/-- One step of the exponential bound: a mean-zero increment bounded by `B` on the support. -/
lemma one_step (K : S → ℝ) (hK : ∀ x, 0 ≤ K x) (hs : HasSum K 1) (g : S → ℝ) (B : ℝ)
    (hB : ∀ x, K x ≠ 0 → |g x| ≤ B) (hmean : HasSum (fun x => K x * g x) 0) (θ : ℝ)
    (hθ : |θ| * B ≤ 1) :
    Summable (fun x => K x * Real.exp (θ * g x)) ∧
      ∑' x, K x * Real.exp (θ * g x) ≤ Real.exp (θ ^ 2 * B ^ 2) := by
  have hpt : ∀ x, K x * Real.exp (θ * g x) ≤ K x + θ * (K x * g x) + θ ^ 2 * B ^ 2 * K x := by
    intro x
    by_cases hx : K x = 0
    · simp [hx]
    have hg := hB x hx
    have hy : |θ * g x| ≤ 1 := by
      rw [abs_mul]
      calc |θ| * |g x| ≤ |θ| * B := mul_le_mul_of_nonneg_left hg (abs_nonneg _)
        _ ≤ 1 := hθ
    have he := Real.abs_exp_sub_one_sub_id_le hy
    have hsq : (θ * g x) ^ 2 ≤ θ ^ 2 * B ^ 2 := by
      rw [mul_pow, ← sq_abs (g x)]
      have h0 : 0 ≤ |g x| := abs_nonneg _
      have : |g x| ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ h0 hg 2
      exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
    have hle : Real.exp (θ * g x) ≤ 1 + θ * g x + θ ^ 2 * B ^ 2 := by
      have := (abs_le.mp he).2
      linarith
    calc K x * Real.exp (θ * g x) ≤ K x * (1 + θ * g x + θ ^ 2 * B ^ 2) :=
          mul_le_mul_of_nonneg_left hle (hK x)
      _ = _ := by ring
  have hR : HasSum (fun x => K x + θ * (K x * g x) + θ ^ 2 * B ^ 2 * K x)
      (1 + θ * 0 + θ ^ 2 * B ^ 2 * 1) :=
    (hs.add (hmean.mul_left θ)).add (hs.mul_left _)
  have hsum : Summable (fun x => K x * Real.exp (θ * g x)) :=
    Summable.of_nonneg_of_le (fun x => mul_nonneg (hK x) (Real.exp_pos _).le) hpt hR.summable
  refine ⟨hsum, ?_⟩
  calc ∑' x, K x * Real.exp (θ * g x) ≤ 1 + θ * 0 + θ ^ 2 * B ^ 2 * 1 := hasSum_le hpt hsum.hasSum hR
    _ = 1 + θ ^ 2 * B ^ 2 := by ring
    _ ≤ Real.exp (θ ^ 2 * B ^ 2) := by
        have := Real.add_one_le_exp (θ ^ 2 * B ^ 2); linarith

section AZ

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (K : S → S → ℝ)
    (hK : ∀ a b, 0 ≤ K a b) (hs : ∀ z, HasSum (K z) 1) (z₀ : S)
    (Y : ℕ → Ω → S) (hY : ∀ n, Measurable (Y n))
    (hcyl : ∀ (n : ℕ) (zs : ℕ → S), P {ω | ∀ j ≤ n, Y j ω = zs j} =
      ENNReal.ofReal ((if zs 0 = z₀ then 1 else 0) * ∏ j ∈ Finset.range n, K (zs j) (zs (j + 1))))
    (f d : S → ℝ) (b : ℝ) (hinc : ∀ z x, K z x ≠ 0 → |f x - f z| ≤ b)
    (hd : ∀ z, HasSum (fun x => K z x * (f x - f z)) (d z))

include hK hs hinc hd in
lemma step_bound (θ : ℝ) (hθ : |θ| * (2 * b) ≤ 1) (z : S) :
    Summable (fun x => K z x * Real.exp (θ * (f x - f z - d z))) ∧
      ∑' x, K z x * Real.exp (θ * (f x - f z - d z)) ≤ Real.exp (θ ^ 2 * (2 * b) ^ 2) := by
  have hdz : |d z| ≤ b := by
    rw [abs_le]; constructor
    · have h1 := hasSum_le (fun x => (show K z x * (-b) ≤ K z x * (f x - f z) by
          by_cases hx : K z x = 0
          · simp [hx]
          · exact mul_le_mul_of_nonneg_left (abs_le.mp (hinc z x hx)).1 (hK z x)))
        ((hs z).mul_left (-b) |>.congr_fun (fun x => by ring) |> fun h => h) (hd z)
      linarith
    · have h1 := hasSum_le (fun x => (show K z x * (f x - f z) ≤ K z x * b by
          by_cases hx : K z x = 0
          · simp [hx]
          · exact mul_le_mul_of_nonneg_left (abs_le.mp (hinc z x hx)).2 (hK z x)))
        (hd z) ((hs z).mul_left b |>.congr_fun (fun x => by ring) |> fun h => h)
      linarith
  refine one_step (K z) (hK z) (hs z) (fun x => f x - f z - d z) (2 * b) ?_ ?_ θ hθ
  · intro x hx
    calc |f x - f z - d z| ≤ |f x - f z| + |d z| := abs_sub _ _
      _ ≤ b + b := add_le_add (hinc z x hx) hdz
      _ = 2 * b := by ring
  · have h := (hd z).sub ((hs z).mul_right (d z))
    have h2 : (fun x => K z x * (f x - f z - d z)) = (fun x => K z x * (f x - f z) - K z x * d z) := by
      funext x; ring
    rw [h2]; simpa using h

include hK hs hinc hd hcyl hY in
theorem exp_moment [IsProbabilityMeasure P] (θ : ℝ) (hθ : |θ| * (2 * b) ≤ 1) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * G f d n (fun j => Y j ω))) ∂P
      ≤ ENNReal.ofReal (Real.exp (n * (θ ^ 2 * (2 * b) ^ 2))) := by
  induction n with
  | zero => simp [G]
  | succ n ih =>
    have hH := markov_int P K hK z₀ Y hY hcyl n
      (fun xs x' => ENNReal.ofReal (Real.exp (θ * G f d (n + 1) (ext xs x'))))
    have hL : (fun ω => ENNReal.ofReal (Real.exp (θ * G f d (n + 1) (fun j => Y j ω))))
        = fun ω => ENNReal.ofReal (Real.exp (θ * G f d (n + 1) (ext (pre Y n ω) (Y (n + 1) ω)))) := by
      funext ω
      rw [G_congr f d (n + 1) (fun j => Y j ω) (ext (pre Y n ω) (Y (n + 1) ω))]
      intro j hj
      by_cases hjn : j ≤ n
      · rw [ext_pre _ Y n ω _ j hjn]
      · have : j = n + 1 := by omega
        subst this
        rw [ext, dif_neg (by omega)]
    rw [hL, hH]
    have hpt : ∀ ω, ∑' x', ENNReal.ofReal (K (Y n ω) x') *
        ENNReal.ofReal (Real.exp (θ * G f d (n + 1) (ext (pre Y n ω) x')))
        ≤ ENNReal.ofReal (Real.exp (θ ^ 2 * (2 * b) ^ 2)) *
          ENNReal.ofReal (Real.exp (θ * G f d n (fun j => Y j ω))) := by
      intro ω
      obtain ⟨hsm, hle⟩ := step_bound K hK hs f d b hinc hd θ hθ (Y n ω)
      have heq : ∀ x', ENNReal.ofReal (K (Y n ω) x') *
          ENNReal.ofReal (Real.exp (θ * G f d (n + 1) (ext (pre Y n ω) x')))
          = ENNReal.ofReal (K (Y n ω) x' * Real.exp (θ * (f x' - f (Y n ω) - d (Y n ω)))) *
            ENNReal.ofReal (Real.exp (θ * G f d n (fun j => Y j ω))) := by
        intro x'
        have hG : G f d (n + 1) (ext (pre Y n ω) x')
            = G f d n (fun j => Y j ω) + (f x' - f (Y n ω) - d (Y n ω)) := by
          rw [G_succ, G_congr f d n (ext (pre Y n ω) x') (fun j => Y j ω)
            (fun j hj => ext_pre _ Y n ω x' j hj), ext_pre _ Y n ω x' n le_rfl]
          rw [ext, dif_neg (by omega)]
        rw [hG, mul_add, Real.exp_add, ENNReal.ofReal_mul (hK _ _),
          ENNReal.ofReal_mul (Real.exp_pos _).le]
        ring
      simp_rw [heq]
      rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg
        (fun x' => mul_nonneg (hK _ _) (Real.exp_pos _).le) hsm]
      gcongr
    calc ∫⁻ ω, ∑' x', ENNReal.ofReal (K (Y n ω) x') *
          ENNReal.ofReal (Real.exp (θ * G f d (n + 1) (ext (pre Y n ω) x'))) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (θ ^ 2 * (2 * b) ^ 2)) *
          ENNReal.ofReal (Real.exp (θ * G f d n (fun j => Y j ω))) ∂P := lintegral_mono hpt
      _ = ENNReal.ofReal (Real.exp (θ ^ 2 * (2 * b) ^ 2)) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * G f d n (fun j => Y j ω))) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp (θ ^ 2 * (2 * b) ^ 2)) *
          ENNReal.ofReal (Real.exp (n * (θ ^ 2 * (2 * b) ^ 2))) := by gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2; push_cast; ring

include hY in
lemma measurable_G (n : ℕ) : Measurable (fun ω => G f d n (fun j => Y j ω)) := by
  unfold G
  exact (((measurable_of_countable f).comp (hY n)).sub ((measurable_of_countable f).comp (hY 0))).sub
    (Finset.measurable_sum _ fun k _ => (measurable_of_countable d).comp (hY k))

include hK hs hinc hd hcyl hY in
theorem tail_one [IsProbabilityMeasure P] (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ * (2 * b) ≤ 1)
    (n : ℕ) (a : ℝ) :
    P {ω | a ≤ G f d n (fun j => Y j ω)}
      ≤ ENNReal.ofReal (Real.exp (-θ * a + n * (θ ^ 2 * (2 * b) ^ 2))) := by
  have hθ' : |θ| * (2 * b) ≤ 1 := by rwa [abs_of_nonneg hθ0]
  have hE := exp_moment P K hK hs z₀ Y hY hcyl f d b hinc hd θ hθ' n
  have hm : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (θ * G f d n (fun j => Y j ω)))) P :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_G Y hY f d n).const_mul θ))).aemeasurable
  have h1 := mul_meas_ge_le_lintegral₀ hm (ENNReal.ofReal (Real.exp (θ * a)))
  have hsub : {ω | a ≤ G f d n (fun j => Y j ω)} ⊆
      {ω | ENNReal.ofReal (Real.exp (θ * a)) ≤
        ENNReal.ofReal (Real.exp (θ * G f d n (fun j => Y j ω)))} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hθ0))
  have h2 : ENNReal.ofReal (Real.exp (θ * a)) * P {ω | a ≤ G f d n (fun j => Y j ω)}
      ≤ ENNReal.ofReal (Real.exp (n * (θ ^ 2 * (2 * b) ^ 2))) :=
    ((mul_le_mul_of_nonneg_left (measure_mono hsub) (zero_le)).trans h1).trans hE
  have hone : ENNReal.ofReal (Real.exp (-θ * a)) * ENNReal.ofReal (Real.exp (θ * a)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; simp
  calc P {ω | a ≤ G f d n (fun j => Y j ω)}
      = ENNReal.ofReal (Real.exp (-θ * a)) *
        (ENNReal.ofReal (Real.exp (θ * a)) * P {ω | a ≤ G f d n (fun j => Y j ω)}) := by
        rw [← mul_assoc, hone, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-θ * a)) *
        ENNReal.ofReal (Real.exp (n * (θ ^ 2 * (2 * b) ^ 2))) := by gcongr
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]

include hK hs hinc hd hcyl hY in
/-- Azuma-Hoeffding maximal bound for the compensated increment sum of a Markov chain. -/
theorem az [IsProbabilityMeasure P] (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ * (2 * b) ≤ 1)
    (m : ℕ) (a : ℝ) :
    P {ω | ∃ n ≤ m, a ≤ |G f d n (fun j => Y j ω)|}
      ≤ ENNReal.ofReal (2 * ((m : ℝ) + 1) *
          Real.exp (-θ * a + m * (θ ^ 2 * (2 * b) ^ 2))) := by
  set E := Real.exp (-θ * a + m * (θ ^ 2 * (2 * b) ^ 2)) with hE
  have hinc' : ∀ z x, K z x ≠ 0 → |(fun y => -f y) x - (fun y => -f y) z| ≤ b := by
    intro z x hx
    rw [show -f x - -f z = -(f x - f z) by ring, abs_neg]; exact hinc z x hx
  have hd' : ∀ z, HasSum (fun x => K z x * ((fun y => -f y) x - (fun y => -f y) z))
      ((fun y => -d y) z) := by
    intro z
    have h2 : (fun x => K z x * ((fun y => -f y) x - (fun y => -f y) z)) =
        fun x => -(K z x * (f x - f z)) := by
      funext x; ring
    rw [h2]; exact (hd z).neg
  have hb : ∀ n ≤ m, ENNReal.ofReal (Real.exp (-θ * a + n * (θ ^ 2 * (2 * b) ^ 2)))
      ≤ ENNReal.ofReal E := by
    intro n hn
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have : (n : ℝ) ≤ m := by exact_mod_cast hn
    have h0 : 0 ≤ θ ^ 2 * (2 * b) ^ 2 := by positivity
    nlinarith
  have hsub : {ω | ∃ n ≤ m, a ≤ |G f d n (fun j => Y j ω)|} ⊆
      ⋃ n ∈ Finset.range (m + 1), ({ω | a ≤ G f d n (fun j => Y j ω)} ∪
        {ω | a ≤ G (fun y => -f y) (fun y => -d y) n (fun j => Y j ω)}) := by
    intro ω hω
    obtain ⟨n, hn, ha⟩ := hω
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq, Finset.mem_range]
    refine ⟨n, by omega, ?_⟩
    rw [G_neg]
    rcases le_abs'.mp ha with h | h
    · right; linarith
    · left; exact h
  calc P {ω | ∃ n ≤ m, a ≤ |G f d n (fun j => Y j ω)|}
      ≤ ∑ n ∈ Finset.range (m + 1), P ({ω | a ≤ G f d n (fun j => Y j ω)} ∪
        {ω | a ≤ G (fun y => -f y) (fun y => -d y) n (fun j => Y j ω)}) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ n ∈ Finset.range (m + 1), (ENNReal.ofReal E + ENNReal.ofReal E) := by
        refine Finset.sum_le_sum fun n hn => (measure_union_le _ _).trans ?_
        have hn' : n ≤ m := by simp at hn; omega
        gcongr
        · exact (tail_one P K hK hs z₀ Y hY hcyl f d b hinc hd θ hθ0 hθ n a).trans (hb n hn')
        · exact (tail_one P K hK hs z₀ Y hY hcyl _ _ b hinc' hd' θ hθ0 hθ n a).trans (hb n hn')
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          show 2 * ((m : ℝ) + 1) * E = ((m + 1 : ℕ) : ℝ) * (E + E) by push_cast; ring,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]

end AZ

end Markov

end SC66A

end
section
open Filter Topology MeasureTheory Finset
open scoped ENNReal

namespace SC66O

open StrictCompatLB.MeanField

/-! PLLN piece (2): the (4.2) trajectory `s` is `(λ+1)`-Lipschitz in `ℓ₁`, and families that are
`ℓ₁`-Lipschitz in time have uniformly small tails on a compact time interval. -/

/-- The GEQD of an occupancy vector: `x_j = q_j - q_{j+1}`. -/
def xOf (q : ℕ → ℝ) : ℕ → ℝ := fun j => q j - q (j + 1)

lemma tele (q : ℕ → ℝ) (n : ℕ) : ∑ i ∈ range n, (q i - q (i + 1)) = q 0 - q n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

lemma xOf_inX (q : ℕ → ℝ) (hq : InY q) : InX (xOf q) := by
  obtain ⟨⟨h0, hnn, hanti⟩, hsum⟩ := hq
  have hx : ∀ j, 0 ≤ xOf q j := fun j => by
    unfold xOf; linarith [hanti (Nat.le_succ j)]
  refine ⟨hx, ?_⟩
  rw [hasSum_iff_tendsto_nat_of_nonneg hx]
  have ht : Tendsto q atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp hsum.tendsto_atTop_zero
  have : (fun n => ∑ i ∈ range n, xOf q i) = fun n => q 0 - q n := by
    funext n; exact tele q n
  rw [this, h0]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub ht

/-- Field of (4.2) at coordinate `i ≥ 1`. -/
noncomputable def F (lam : ℝ) (p : (ℕ → ℝ) → ℕ → ℝ) (q : ℕ → ℝ) (i : ℕ) : ℝ :=
  lam * p (xOf q) (i - 1) - (q i - q (i + 1))

lemma sumF_le (lam : ℝ) (hlam : 0 ≤ lam) (p : (ℕ → ℝ) → ℕ → ℝ) (hp : IsAssignmentFn p)
    (q : ℕ → ℝ) (hq : InY q) (n : ℕ) :
    ∑ i ∈ Ico 1 n, |F lam p q i| ≤ lam + 1 := by
  have hX := xOf_inX q hq
  obtain ⟨hpnn, hp1, -⟩ := hp _ hX
  obtain ⟨⟨h0, hnn, hanti⟩, -⟩ := hq
  calc ∑ i ∈ Ico 1 n, |F lam p q i|
      ≤ ∑ i ∈ Ico 1 n, (lam * p (xOf q) (i - 1) + (q i - q (i + 1))) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        unfold F
        have h1 := hpnn (i - 1)
        have h2 : q (i + 1) ≤ q i := hanti (Nat.le_succ i)
        rw [abs_le]; constructor <;> nlinarith
    _ = lam * ∑ k ∈ range (n - 1), p (xOf q) k + (q 1 - q (1 + (n - 1))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_Ico_eq_sum_range,
          Finset.sum_Ico_eq_sum_range]
        congr 1
        · simp
        · have := tele (fun k => q (1 + k)) (n - 1)
          simp only [add_zero] at this
          rw [← this]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          ring_nf
    _ ≤ lam * 1 + 1 := by
        gcongr
        · exact sum_le_hasSum _ (fun i _ => hpnn i) hp1
        · have := hnn (1 + (n - 1)); have := hanti (Nat.zero_le 1); linarith
    _ = lam + 1 := by ring

/-- `(λ+1)`-Lipschitz bound for finite partial `ℓ₁` sums along the (4.2) trajectory. -/
theorem lip_sum (lam : ℝ) (hlam : 0 ≤ lam) (p : (ℕ → ℝ) → ℕ → ℝ) (hp : IsAssignmentFn p)
    (s : ℝ → ℕ → ℝ) (hs : IsPiTrajectory lam p s) (hsY : ∀ t : ℝ, 0 ≤ t → InY (s t))
    (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (n : ℕ) :
    ∑ i ∈ range n, |s u i - s t i| ≤ (lam + 1) * |u - t| := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn, Nat.zero_add]
  have h00 : s u 0 - s t 0 = 0 := by rw [(hs.1 u hu).1, (hs.1 t ht).1]; ring
  rw [h00, abs_zero, zero_add]
  set σ : ℕ → ℝ := fun i => if s t i ≤ s u i then 1 else -1 with hσ
  have hσabs : ∀ i, |σ i| = 1 := fun i => by simp only [hσ]; split_ifs <;> simp
  let φ : ℝ → ℝ := fun r => ∑ i ∈ Ico 1 n, σ i * s r i
  have hder : ∀ r ∈ Set.Ici (0 : ℝ), HasDerivWithinAt φ
      (∑ i ∈ Ico 1 n, σ i * F lam p (s r) i) (Set.Ici 0) r := by
    intro r hr
    apply HasDerivWithinAt.fun_sum
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    exact (hs.2 i hi1 r hr).const_mul (σ i)
  have hbd : ∀ r ∈ Set.Ici (0 : ℝ), ‖∑ i ∈ Ico 1 n, σ i * F lam p (s r) i‖ ≤ lam + 1 := by
    intro r hr
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun i _ => by rw [abs_mul, hσabs, one_mul])))
      (sumF_le lam hlam p hp (s r) (hsY r hr) n)
  have key := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd
    (Set.mem_Ici.mpr ht) (Set.mem_Ici.mpr hu)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at key
  have heq : φ u - φ t = ∑ i ∈ Ico 1 n, |s u i - s t i| := by
    simp only [φ, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hσ]
    split_ifs with h
    · rw [abs_of_nonneg (by linarith)]; ring
    · rw [abs_of_neg (by linarith)]; ring
  rw [heq, abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))] at key
  exact key

/-- `ℓ₁` form: `l1dist (s u) (s t) ≤ (λ+1)|u - t|`. -/
theorem l1_lip (lam : ℝ) (hlam : 0 ≤ lam) (p : (ℕ → ℝ) → ℕ → ℝ) (hp : IsAssignmentFn p)
    (s : ℝ → ℕ → ℝ) (hs : IsPiTrajectory lam p s) (hsY : ∀ t : ℝ, 0 ≤ t → InY (s t))
    (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    PowerOfDUniversality.Fluid.l1dist (s u) (s t) ≤ ENNReal.ofReal ((lam + 1) * |u - t|) := by
  unfold PowerOfDUniversality.Fluid.l1dist
  refine ENNReal.tsum_le_of_sum_range_le (fun n => ?_)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (lip_sum lam hlam p hp s hs hsY t u ht hu n)

/-- Uniform tails on `[0, T]` for a time-indexed family that is `ℓ₁`-Lipschitz in time. -/
theorem unif_tail (f : ℝ → ℕ → ℝ) (T C : ℝ) (hC : 0 ≤ C)
    (hnn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, 0 ≤ f t i)
    (hsum : ∀ t ∈ Set.Icc (0 : ℝ) T, Summable (f t))
    (hlip : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ n,
      ∑ i ∈ range n, |f u i - f t i| ≤ C * |u - t|)
    (η : ℝ) (hη : 0 < η) :
    ∃ L : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ L' ≥ L, ∀ n, ∑ i ∈ Ico L' n, f t i ≤ η := by
  rcases lt_or_ge T 0 with hT | hT
  · exact ⟨0, fun t ht => absurd (ht.1.trans ht.2) (not_le.mpr hT)⟩
  set δ : ℝ := η / (2 * (C + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hCδ : C * δ ≤ η / 2 := by
    rw [hδ, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  let g : ℕ → ℝ := fun j => min ((j : ℝ) * δ) T
  have hg : ∀ j, g j ∈ Set.Icc (0 : ℝ) T := fun j =>
    ⟨le_min (by positivity) hT, min_le_right _ _⟩
  -- a tail index for each grid point
  have hgood : ∀ j, ∃ L : ℕ, ∀ L' ≥ L, ∀ n, ∑ i ∈ Ico L' n, f (g j) i ≤ η / 2 := by
    intro j
    have hS := (hsum (g j) (hg j)).hasSum
    have hT' := hS.tendsto_sum_nat
    have hev : ∀ᶠ m in atTop, ∑' i, f (g j) i - η / 2 < ∑ i ∈ range m, f (g j) i :=
      hT'.eventually (lt_mem_nhds (by linarith))
    obtain ⟨L, hL⟩ := eventually_atTop.mp hev
    refine ⟨L, fun L' hL' n => ?_⟩
    rcases le_or_gt L' n with hn | hn
    · rw [Finset.sum_Ico_eq_sub _ hn]
      have h1 := sum_le_hasSum (range n) (fun i _ => hnn (g j) (hg j) i) hS
      have h2 := hL L' hL'
      linarith
    · rw [Finset.Ico_eq_empty_of_le hn.le, Finset.sum_empty]; linarith
  choose Lf hLf using hgood
  set J : ℕ := ⌊T / δ⌋₊
  refine ⟨∑ j ∈ range (J + 1), Lf j, fun t ht L' hL' n => ?_⟩
  set j : ℕ := ⌊t / δ⌋₊ with hj
  have hjJ : j ≤ J := Nat.floor_le_floor (div_le_div_of_nonneg_right ht.2 hδ0.le)
  have hjt : (j : ℝ) * δ ≤ t := by
    have := Nat.floor_le (div_nonneg ht.1 hδ0.le)
    rw [le_div_iff₀ hδ0] at this; exact this
  have htj : t - (j : ℝ) * δ < δ := by
    have := Nat.lt_floor_add_one (t / δ)
    rw [div_lt_iff₀ hδ0] at this; nlinarith
  have hgj : g j = (j : ℝ) * δ := min_eq_left (hjt.trans ht.2)
  have hLj : Lf j ≤ L' := le_trans
    (Finset.single_le_sum (fun k _ => Nat.zero_le (Lf k)) (Finset.mem_range.mpr (by omega))) hL'
  have h1 := hLf j L' hLj n
  have h2 : ∑ i ∈ Ico L' n, (f t i - f (g j) i) ≤ C * δ := by
    calc ∑ i ∈ Ico L' n, (f t i - f (g j) i)
        ≤ ∑ i ∈ Ico L' n, |f t i - f (g j) i| :=
          Finset.sum_le_sum (fun i _ => le_abs_self _)
      _ ≤ ∑ i ∈ range n, |f t i - f (g j) i| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi; rw [Finset.mem_Ico] at hi; rw [Finset.mem_range]; omega
          · intro i _ _; exact abs_nonneg _
      _ ≤ C * |t - g j| := hlip (g j) (hg j) t ht n
      _ ≤ C * δ := by
          gcongr
          rw [hgj, abs_of_nonneg (by linarith)]; exact htj.le
  rw [Finset.sum_sub_distrib] at h2
  linarith

end SC66O

end
section
open Filter Topology Finset
open scoped ENNReal

namespace SC66M

open StrictCompatLB.MeanField PowerOfDUniversality.Fluid

/-- Initial error: head `1..L` plus process tail plus trajectory tail is at most `l1 + 2 * tail`. -/
theorem init_E (q S : ℕ → ℝ) (hqn : ∀ i, 0 ≤ q i) (hSn : ∀ i, 0 ≤ S i) (L : ℕ) (Tq TS : ℝ)
    (hTq : HasSum (fun j => q (L + 1 + j)) Tq) (hTS : HasSum (fun j => S (L + 1 + j)) TS)
    (D : ℝ) (hD0 : 0 ≤ D) (hl1 : l1dist q S ≤ ENNReal.ofReal D) :
    ∑ i ∈ Icc 1 L, |q i - S i| + Tq + TS ≤ D + 2 * TS := by
  have hfin : ∀ I : Finset ℕ, ∑ i ∈ I, |q i - S i| ≤ D := by
    intro I
    have h1 : ENNReal.ofReal (∑ i ∈ I, |q i - S i|) ≤ ENNReal.ofReal D := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
      exact (ENNReal.sum_le_tsum I).trans hl1
    exact (ENNReal.ofReal_le_ofReal_iff hD0).mp h1
  have hIcc : ∑ i ∈ Icc 1 L, |q i - S i| ≤ ∑ i ∈ range (L + 1), |q i - S i| :=
    sum_le_sum_of_subset_of_nonneg (fun i hi => by
      have := mem_Icc.mp hi; exact mem_range.mpr (by omega)) (fun _ _ _ => abs_nonneg _)
  have hTq' : Tq ≤ D + TS - ∑ i ∈ Icc 1 L, |q i - S i| := by
    rw [← hTq.tsum_eq]
    refine Real.tsum_le_of_sum_range_le (fun j => hqn _) fun n => ?_
    have h1 : ∑ j ∈ range n, q (L + 1 + j) ≤
        ∑ j ∈ range n, |q (L + 1 + j) - S (L + 1 + j)| + ∑ j ∈ range n, S (L + 1 + j) := by
      rw [← sum_add_distrib]
      exact sum_le_sum fun j _ => by
        have := le_abs_self (q (L + 1 + j) - S (L + 1 + j)); linarith
    have h2 : ∑ j ∈ range n, S (L + 1 + j) ≤ TS :=
      sum_le_hasSum (range n) (fun j _ => hSn _) hTS
    have h3 := hfin (range (L + 1 + n))
    rw [sum_range_add] at h3
    linarith
  linarith

/-- The Azuma bound with `θ = (a / (8κ)) N`, `b = 1/N` and `m N ≤ κ N` tends to `0`. -/
theorem az_lim (a κ : ℝ) (ha : 0 < a) (hκ : 1 ≤ κ) (m : ℕ → ℕ)
    (hm : ∀ N : ℕ, 1 ≤ N → (m N : ℝ) ≤ κ * N) :
    Tendsto (fun N : ℕ => ENNReal.ofReal (2 * ((m N : ℝ) + 1) *
      Real.exp (-(a / (8 * κ) * N) * a + m N * ((a / (8 * κ) * N) ^ 2 * (2 * (1 / (N : ℝ))) ^ 2))))
      atTop (𝓝 0) := by
  have hκ0 : 0 < κ := by linarith
  set c : ℝ := a / (8 * κ) with hc
  set β : ℝ := a ^ 2 / (16 * κ) with hβ
  have hβ0 : 0 < β := by positivity
  have hc0 : 0 < c := by positivity
  have hg : Tendsto (fun N : ℕ => (2 * κ / β) * ((β * N) ^ 1 * Real.exp (-(β * N))) +
      2 * Real.exp (-(β * N))) atTop (𝓝 0) := by
    have hx : Tendsto (fun N : ℕ => β * (N : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hβ0
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hx
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp hx
    have := (h1.const_mul (2 * κ / β)).add (h2.const_mul 2)
    simpa using this
  have hreal : Tendsto (fun N : ℕ => 2 * ((m N : ℝ) + 1) *
      Real.exp (-(c * N) * a + m N * ((c * N) ^ 2 * (2 * (1 / (N : ℝ))) ^ 2))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
      (Eventually.of_forall fun N => by positivity) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hmN := hm N hN
    have e1 : (m N : ℝ) * ((c * N) ^ 2 * (2 * (1 / (N : ℝ))) ^ 2) = 4 * c ^ 2 * m N := by
      field_simp <;> ring
    have e2 : -(c * N) * a + 4 * c ^ 2 * (κ * N) = -(β * N) := by
      rw [hc, hβ]; field_simp <;> ring
    have hexp : Real.exp (-(c * N) * a + m N * ((c * N) ^ 2 * (2 * (1 / (N : ℝ))) ^ 2)) ≤
        Real.exp (-(β * N)) := by
      rw [e1, ← e2]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hmN (by positivity : (0 : ℝ) ≤ 4 * c ^ 2)
      linarith
    have heq : (2 * κ / β) * ((β * N) ^ 1 * Real.exp (-(β * N))) + 2 * Real.exp (-(β * N)) =
        2 * (κ * N + 1) * Real.exp (-(β * N)) := by
      field_simp <;> ring
    rw [heq]
    have hm1 : 2 * ((m N : ℝ) + 1) ≤ 2 * (κ * N + 1) := by linarith
    exact mul_le_mul hm1 hexp (Real.exp_pos _).le (by positivity)
  have := ENNReal.tendsto_ofReal hreal
  rwa [ENNReal.ofReal_zero] at this

end SC66M

end
section
open Filter Topology MeasureTheory Finset
open scoped ENNReal
namespace SC66L

open StrictCompatLB.MeanField

/-- Empirical distribution of `z` over a finite set `S` of servers. -/
noncomputable def emp {N : ℕ} (S : Finset (Fin N)) (z : Fin N → ℕ) (i : ℕ) : ℝ :=
  ((S.filter (fun v => z v = i)).card : ℝ) / (S.card : ℝ)

lemma emp_inX {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty) (z : Fin N → ℕ) :
    InX (emp S z) := by
  refine ⟨fun i => by unfold emp; positivity, ?_⟩
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hzero : ∀ i ∉ range (S.sup z + 1), emp S z i = 0 := by
    intro i hi
    simp only [mem_range, not_lt] at hi
    have : S.filter (fun v => z v = i) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v hv hvi
      have := Finset.le_sup (f := z) hv
      omega
    simp [emp, this]
  have hsum : ∑ i ∈ range (S.sup z + 1), emp S z i = 1 := by
    unfold emp
    rw [← Finset.sum_div]
    have hcard : S.card = ∑ i ∈ range (S.sup z + 1), (S.filter (fun v => z v = i)).card :=
      Finset.card_eq_sum_card_fiberwise (fun v hv => Finset.mem_coe.mpr
        (mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_coe.mp hv)))))
    rw [div_eq_one_iff_eq hc.ne']
    exact_mod_cast hcard.symm
  rw [← hsum]
  exact hasSum_sum_of_ne_finset_zero hzero

lemma geqd_eq {N : ℕ} (z : Fin N → ℕ) : geqd z = emp univ z := by
  funext i; simp [geqd, emp]

lemma leqd_eq (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) : leqd M G N z w = emp (nbrW M G N w) z := by
  funext i; simp [leqd, emp]

lemma geqd_inX {N : ℕ} (hN : 1 ≤ N) (z : Fin N → ℕ) : InX (geqd z) := by
  rw [geqd_eq]
  exact emp_inX _ ⟨⟨0, by omega⟩, mem_univ _⟩ z

end SC66L
end
section
open Filter Topology MeasureTheory Finset
open scoped ENNReal

namespace SC66Q

open StrictCompatLB.MeanField PowerOfDUniversality.Fluid

/-- Drift of `occ · i` under one step of `lbKernel`. -/
noncomputable def dOcc (lam : ℝ) (M : ℕ → ℕ) (N : ℕ)
    (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ) (i : ℕ) (z : Fin N → ℕ) : ℝ :=
  1 / ((lam + 1) * (N : ℝ)) * (lam * SC66D.levA M N route z (i - 1) - geqd z i)

/-- Drift of the occupancy tail `tl k`. -/
noncomputable def dTl (lam : ℝ) (M : ℕ → ℕ) (N : ℕ)
    (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ) (k : ℕ) (z : Fin N → ℕ) : ℝ :=
  1 / ((lam + 1) * (N : ℝ)) * (lam * SC66D.levT M N route z k - occ z k)

/-- The Azuma bad event: the compensated sum leaves `(-a, a)` before step `m`. -/
def bad {Ω : Type*} {N : ℕ} (Y : ℕ → Ω → (Fin N → ℕ)) (f d : (Fin N → ℕ) → ℝ) (m : ℕ)
    (a : ℝ) : Set Ω :=
  {ω | ∃ n ≤ m, a ≤ |SC66A.G f d n (fun j => Y j ω)|}

/-- The Azuma bound with `θ = (a/(8κ)) N`, `b = 1/N`, `m = ⌈(T+1)(λ+1)N⌉`. -/
noncomputable def azb (a κ T lam : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * ((⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊ : ℝ) + 1) *
    Real.exp (-(a / (8 * κ) * N) * a + (⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊ : ℝ) *
      ((a / (8 * κ) * N) ^ 2 * (2 * (1 / (N : ℝ))) ^ 2)))

/-- Arithmetic of the final path bound. -/
lemma bnd (lam K T2 a δ ε n L h : ℝ) (hlam : 0 ≤ lam) (hK : 0 ≤ K) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (haδ : (L + 1) * a = δ) (hT2n : n * h ≤ T2)
    (hrN : L * (2 * (lam + 1) * (lam * K + 1)) * h * T2 ≤ δ) (hε : 0 < ε)
    (hδε : (6 + 3 * T2 * lam) * δ * Real.exp ((4 * lam * K + 2) * T2) ≤ ε / 4) :
    (3 * δ + (L + 1) * a + L * (n * (2 * (lam + 1) * (lam * K + 1) * h * h)) + δ +
      T2 * (lam * (2 * δ + δ))) * Real.exp ((4 * lam * K + 2) * T2) < ε / 2 := by
  have hC : 0 ≤ L * (2 * (lam + 1) * (lam * K + 1)) * h := by positivity
  have hr : L * (n * (2 * (lam + 1) * (lam * K + 1) * h * h)) ≤ δ := by
    calc L * (n * (2 * (lam + 1) * (lam * K + 1) * h * h))
        = (L * (2 * (lam + 1) * (lam * K + 1)) * h) * (n * h) := by ring
      _ ≤ (L * (2 * (lam + 1) * (lam * K + 1)) * h) * T2 := mul_le_mul_of_nonneg_left hT2n hC
      _ ≤ δ := by linarith [hrN]
  have hin : 3 * δ + (L + 1) * a + L * (n * (2 * (lam + 1) * (lam * K + 1) * h * h)) + δ +
      T2 * (lam * (2 * δ + δ)) ≤ (6 + 3 * T2 * lam) * δ := by nlinarith
  calc _ ≤ (6 + 3 * T2 * lam) * δ * Real.exp ((4 * lam * K + 2) * T2) :=
        mul_le_mul_of_nonneg_right hin (Real.exp_pos _).le
    _ ≤ ε / 4 := hδε
    _ < ε / 2 := by linarith

set_option maxHeartbeats 1000000 in
/-- CHAIN: the discrete-time embedded chain stays `ε/2`-close to the fluid trajectory up to
step `⌈(T+1)(λ+1)N⌉` on the event that the level error stays below `η`, with probability `→ 1`. -/
theorem chain (lam : ℝ) (hlam : 0 ≤ lam) (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (route : (N : ℕ) → Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (hroute : ∀ N, 1 ≤ N → (∀ w z v, 0 ≤ route N w z v) ∧ ∀ w z, ∑ v, route N w z v = 1)
    (p : (ℕ → ℝ) → ℕ → ℝ) (hp : IsAssignmentFn p) (hpL : IsLipschitzPolicy p)
    (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ)
    (hz : Tendsto (fun N => l1dist (occ (z₀ N)) q₀) atTop (𝓝 0))
    (s : ℝ → ℕ → ℝ) (hs : IsPiTrajectory lam p s) (hsY : ∀ t : ℝ, 0 ≤ t → InY (s t))
    (hs0 : s 0 = q₀)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ)
    (hY : ∀ N, 1 ≤ N → IsLBProcess P lam M N (route N) (z₀ N) (Y N) (τ N))
    (T : ℝ) (hT : 0 ≤ T) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ Tendsto (fun N : ℕ => P {ω | ∃ n ≤ ⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊,
      (∀ k < n, l1dist (SC66D.levA M N (route N) (Y N k ω)) (p (geqd (Y N k ω)))
        < ENNReal.ofReal η) ∧
      ENNReal.ofReal (ε / 2) ≤ l1dist (occ (Y N n ω)) (s ((n : ℝ) / ((lam + 1) * (N : ℝ))))})
      atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure P := (hY 1 le_rfl).1
  obtain ⟨K, hK0, hpK⟩ := hpL
  obtain ⟨T2, hT2def⟩ : ∃ T2 : ℝ, T2 = T + 2 := ⟨_, rfl⟩
  have hT2 : 0 < T2 := by rw [hT2def]; linarith
  have hΓ0 : 0 < Real.exp ((4 * lam * K + 2) * T2) := Real.exp_pos _
  have hB0 : 0 < 6 + 3 * T2 * lam := by have := mul_nonneg hT2.le hlam; linarith
  obtain ⟨δ, hδ0, hδ1, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (6 + 3 * T2 * lam) * δ * Real.exp ((4 * lam * K + 2) * T2) ≤ ε / 4 := by
    have hD : 0 < 4 * (6 + 3 * T2 * lam) * Real.exp ((4 * lam * K + 2) * T2) :=
      mul_pos (mul_pos (by norm_num) hB0) hΓ0
    refine ⟨min 1 (ε / (4 * (6 + 3 * T2 * lam) * Real.exp ((4 * lam * K + 2) * T2))),
      lt_min one_pos (div_pos hε hD), min_le_left _ _, ?_⟩
    have h1 := (le_div_iff₀ hD).mp (min_le_right 1
      (ε / (4 * (6 + 3 * T2 * lam) * Real.exp ((4 * lam * K + 2) * T2))))
    linarith
  refine ⟨δ, hδ0, ?_⟩
  -- trajectory facts
  have hsn : ∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ s t i := fun t ht => (hsY t ht).1.2.1
  have hs00 : ∀ t : ℝ, 0 ≤ t → s t 0 = 1 := fun t ht => (hsY t ht).1.1
  have hsX : ∀ t : ℝ, 0 ≤ t → InX (fun j => s t j - s t (j + 1)) :=
    fun t ht => SC66O.xOf_inX _ (hsY t ht)
  have hssum : ∀ t : ℝ, 0 ≤ t → Summable (s t) :=
    fun t ht => (summable_nat_add_iff 1).mp (hsY t ht).2
  have hlip : ∀ t u : ℝ, 0 ≤ t → 0 ≤ u →
      l1dist (s u) (s t) ≤ ENNReal.ofReal ((lam + 1) * |u - t|) :=
    fun t u ht hu => SC66O.l1_lip lam hlam p hp s hs hsY t u ht hu
  have hsumt : ∀ t : ℝ, 0 ≤ t → ∀ k0 : ℕ, Summable (fun j => s t (k0 + j)) := by
    intro t ht k0
    exact ((summable_nat_add_iff k0).mpr (hssum t ht)).congr
      (fun j => by rw [Nat.add_comm j k0])
  -- uniform tails
  obtain ⟨L1, hL1⟩ := SC66O.unif_tail s T2 (lam + 1) (by linarith)
    (fun t ht i => hsn t ht.1 i) (fun t ht => hssum t ht.1)
    (fun t ht u hu n => SC66O.lip_sum lam hlam p hp s hs hsY t u ht.1 hu.1 n) δ hδ0
  obtain ⟨L2, hL2⟩ := SC66O.unif_tail (fun t i => p (fun j => s t j - s t (j + 1)) i) T2
    (K * (2 * (lam + 1))) (mul_nonneg hK0.le (by linarith))
    (fun t ht i => (hp _ (hsX t ht.1)).1 i) (fun t ht => (hp _ (hsX t ht.1)).2.1.summable)
    (fun t ht u hu n => by
      refine SC66V.fin_le_l1 _ _ _ _
        (mul_nonneg (mul_nonneg hK0.le (by linarith)) (abs_nonneg _)) ?_
      have h1 := hpK _ _ (hsX u hu.1) (hsX t ht.1)
      have h2 := SC66V.xOf_l1 (s u) (s t)
      have h3 := hlip t u ht.1 hu.1
      refine (h1.trans (mul_le_mul_right (h2.trans (mul_le_mul_right h3 _)) _)).trans
        (le_of_eq ?_)
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
        ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num), ← ENNReal.ofReal_mul hK0.le]
      congr 1; ring)
    δ hδ0
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = max L1 L2 := ⟨_, rfl⟩
  have hLL1 : L1 ≤ L + 1 := by rw [hLdef]; omega
  have hLL2 : L2 ≤ L := by rw [hLdef]; exact le_max_right _ _
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = (T + 1) * (lam + 1) + 1 := ⟨_, rfl⟩
  have hκ : 1 ≤ κ := by
    have : 0 ≤ (T + 1) * (lam + 1) := mul_nonneg (by linarith) (by linarith)
    rw [hκdef]; linarith
  have hκ0 : 0 < κ := by linarith
  obtain ⟨a, ha, ha1, haδ⟩ : ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ((L : ℝ) + 1) * a = δ := by
    have hL : (0 : ℝ) < (L : ℝ) + 1 := by positivity
    refine ⟨δ / ((L : ℝ) + 1), div_pos hδ0 hL, ?_, ?_⟩
    · rw [div_le_one hL]; have : (0 : ℝ) ≤ L := Nat.cast_nonneg _; linarith
    · rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hL.ne', mul_one]
  have hmκ : ∀ N : ℕ, 1 ≤ N → ((⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊ : ℕ) : ℝ) ≤ κ * N := by
    intro N hN
    have h1 := Nat.ceil_lt_add_one
      (show 0 ≤ (T + 1) * ((lam + 1) * (N : ℝ)) from
        mul_nonneg (by linarith) (mul_nonneg (by linarith) (Nat.cast_nonneg _)))
    have h2 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [hκdef]; nlinarith
  have hbd : Tendsto (azb a κ T lam) atTop (𝓝 0) :=
    SC66M.az_lim a κ ha hκ (fun N => ⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊) hmκ
  have hU := (tendsto_finset_sum (Icc 1 L) (fun i _ => hbd)).add hbd
  simp only [Finset.sum_const_zero, add_zero] at hU
  have hev1 : ∀ᶠ N : ℕ in atTop, l1dist (occ (z₀ N)) q₀ < ENNReal.ofReal δ :=
    hz.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ0))
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev1
  obtain ⟨N2, hN2⟩ := exists_nat_ge
    ((L : ℝ) * (2 * (lam + 1) * (lam * K + 1)) * T2 / δ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
    (Filter.Eventually.of_forall fun N => zero_le) ?_
  rw [eventually_atTop]
  refine ⟨max 1 (max N1 N2), fun N hNmax => ?_⟩
  have hN : 1 ≤ N := le_trans (le_max_left _ _) hNmax
  have hNN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hNmax
  have hNN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hNmax
  have hYN := hY N hN
  have hYm : ∀ n, Measurable (Y N n) := hYN.2.1
  have hcyl := hYN.2.2.1
  have hr : ∀ w z v, 0 ≤ route N w z v := (hroute N hN).1
  have hK1 : ∀ x y, 0 ≤ lbKernel lam M N (route N) x y :=
    fun x y => SC66D.lb_nonneg lam M N (route N) hlam hr x y
  have hs1 : ∀ z, HasSum (lbKernel lam M N (route N) z) 1 :=
    fun z => SC66D.lb_hasSum_one lam M N (route N) hlam (hM N) hN (hroute N hN).2 z
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hR : 0 < (lam + 1) * (N : ℝ) := mul_pos (by linarith) hN0
  have hR1 : 1 ≤ (lam + 1) * (N : ℝ) := by
    have := mul_nonneg hlam hN0.le; linarith
  have hh0 : 0 ≤ 1 / ((lam + 1) * (N : ℝ)) := one_div_nonneg.mpr hR.le
  have hθ0 : 0 ≤ a / (8 * κ) * N := mul_nonneg (div_nonneg ha.le (by linarith)) hN0.le
  have hθ : a / (8 * κ) * N * (2 * (1 / (N : ℝ))) ≤ 1 := by
    have e1 : (N : ℝ) * (2 * (1 / (N : ℝ))) = 2 := by
      rw [mul_left_comm, mul_one_div, div_self hN0.ne', mul_one]
    rw [mul_assoc, e1, div_mul_eq_mul_div, div_le_one (by linarith)]; linarith
  have hAZo : ∀ i ∈ Icc 1 L, P (bad (Y N) (fun z => occ z i) (dOcc lam M N (route N) i)
      ⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊ a) ≤ azb a κ T lam N := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    exact SC66A.az (P := P) (K := lbKernel lam M N (route N)) (hK := hK1) (hs := hs1)
      (z₀ := z₀ N) (Y := Y N) (hY := hYm) (hcyl := hcyl) (f := fun z => occ z i)
      (d := dOcc lam M N (route N) i) (b := 1 / (N : ℝ))
      (hinc := fun z x hx => SC66D.inc_occ lam M N (route N) z x hx i)
      (hd := fun z => SC66D.drift_occ lam M N (route N) z i hi1)
      (a / (8 * κ) * N) hθ0 hθ _ a
  have hAZt : P (bad (Y N) (SC66D.tl (L + 1)) (dTl lam M N (route N) (L + 1))
      ⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊ a) ≤ azb a κ T lam N :=
    SC66A.az (P := P) (K := lbKernel lam M N (route N)) (hK := hK1) (hs := hs1)
      (z₀ := z₀ N) (Y := Y N) (hY := hYm) (hcyl := hcyl) (f := SC66D.tl (L + 1))
      (d := dTl lam M N (route N) (L + 1)) (b := 1 / (N : ℝ))
      (hinc := fun z x hx => SC66D.inc_tl lam M N (route N) (L + 1) (by omega) z x hx)
      (hd := fun z => SC66D.drift_tl lam M N (route N) z (L + 1) (by omega))
      (a / (8 * κ) * N) hθ0 hθ _ a
  have h00 : P {ω | Y N 0 ω ≠ z₀ N} = 0 := by
    have h1 : P {ω | ∀ j ≤ 0, Y N j ω = z₀ N} = 1 := by
      rw [hcyl 0 (fun _ => z₀ N)]; simp
    have hpre : {ω | ∀ j ≤ 0, Y N j ω = z₀ N} = Y N 0 ⁻¹' {z₀ N} := by ext ω; simp
    have hms : MeasurableSet {ω | ∀ j ≤ 0, Y N j ω = z₀ N} := by
      rw [hpre]; exact (hYm 0) (measurableSet_singleton _)
    have hset : {ω | Y N 0 ω ≠ z₀ N} = {ω | ∀ j ≤ 0, Y N j ω = z₀ N}ᶜ := by ext ω; simp
    rw [hset, measure_compl hms (measure_ne_top _ _), h1, measure_univ, tsub_self]
  have hrN : (L : ℝ) * (2 * (lam + 1) * (lam * K + 1)) * (1 / ((lam + 1) * N)) * T2 ≤ δ := by
    have hX : 0 ≤ (L : ℝ) * (2 * (lam + 1) * (lam * K + 1)) * T2 :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) hT2.le
    have hN2' : (L : ℝ) * (2 * (lam + 1) * (lam * K + 1)) * T2 / δ ≤ N :=
      hN2.trans (by exact_mod_cast hNN2)
    have h1 : 1 / ((lam + 1) * (N : ℝ)) ≤ 1 / (N : ℝ) :=
      one_div_le_one_div_of_le hN0 (by have := mul_nonneg hlam hN0.le; linarith)
    rw [div_le_iff₀ hδ0] at hN2'
    calc (L : ℝ) * (2 * (lam + 1) * (lam * K + 1)) * (1 / ((lam + 1) * N)) * T2
        = ((L : ℝ) * (2 * (lam + 1) * (lam * K + 1)) * T2) * (1 / ((lam + 1) * N)) := by ring
      _ ≤ ((L : ℝ) * (2 * (lam + 1) * (lam * K + 1)) * T2) * (1 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 hX
      _ ≤ δ := by
          rw [mul_one_div, div_le_iff₀ hN0]; linarith
  have hsub : {ω | ∃ n ≤ ⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊,
      (∀ k < n, l1dist (SC66D.levA M N (route N) (Y N k ω)) (p (geqd (Y N k ω)))
        < ENNReal.ofReal δ) ∧
      ENNReal.ofReal (ε / 2) ≤ l1dist (occ (Y N n ω)) (s ((n : ℝ) / ((lam + 1) * (N : ℝ))))} ⊆
      {ω | Y N 0 ω ≠ z₀ N} ∪ ((⋃ i ∈ Icc 1 L, bad (Y N) (fun z => occ z i)
        (dOcc lam M N (route N) i) ⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊ a) ∪
        bad (Y N) (SC66D.tl (L + 1)) (dTl lam M N (route N) (L + 1))
          ⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊ a) := by
    intro ω hω
    by_contra hcon
    have h0 : Y N 0 ω = z₀ N := by
      by_contra h
      exact hcon (Set.mem_union_left _ (show ω ∈ {ω | Y N 0 ω ≠ z₀ N} from h))
    have hAi : ∀ i ∈ Icc 1 L, ∀ n ≤ ⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊,
        |SC66A.G (fun z => occ z i) (dOcc lam M N (route N) i) n (fun j => Y N j ω)| < a := by
      intro i hi n hn
      by_contra h
      have hmem : ω ∈ bad (Y N) (fun z => occ z i) (dOcc lam M N (route N) i)
          ⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊ a := by
        simp only [bad, Set.mem_setOf_eq]; exact ⟨n, hn, not_lt.mp h⟩
      exact hcon (Set.mem_union_right _ (Set.mem_union_left _
        (Set.mem_iUnion₂.mpr ⟨i, hi, hmem⟩)))
    have hAt : ∀ n ≤ ⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊,
        |SC66A.G (SC66D.tl (L + 1)) (dTl lam M N (route N) (L + 1)) n (fun j => Y N j ω)| < a := by
      intro n hn
      by_contra h
      have hmem : ω ∈ bad (Y N) (SC66D.tl (L + 1)) (dTl lam M N (route N) (L + 1))
          ⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊ a := by
        simp only [bad, Set.mem_setOf_eq]; exact ⟨n, hn, not_lt.mp h⟩
      exact hcon (Set.mem_union_right _ (Set.mem_union_right _ hmem))
    obtain ⟨n, hn, hgood, hfar⟩ := hω
    have hn' : (n : ℝ) ≤ (T + 1) * ((lam + 1) * N) + 1 := by
      have h1 := Nat.ceil_lt_add_one (show 0 ≤ (T + 1) * ((lam + 1) * (N : ℝ)) from
        mul_nonneg (by linarith) hR.le)
      have h2 : (n : ℝ) ≤ (⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊ : ℝ) := by exact_mod_cast hn
      linarith
    have hT2n : (n : ℝ) * (1 / ((lam + 1) * N)) ≤ T2 := by
      rw [mul_one_div, div_le_iff₀ hR, hT2def]; nlinarith
    have hkt : ∀ k ≤ n, (k : ℝ) * (1 / ((lam + 1) * N)) ∈ Set.Icc (0 : ℝ) T2 := by
      intro k hk
      refine ⟨mul_nonneg (Nat.cast_nonneg _) hh0, le_trans ?_ hT2n⟩
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh0
    have hTS0 : HasSum (fun j => s 0 (L + 1 + j))
        (∑' j, s (((0 : ℕ) : ℝ) * (1 / ((lam + 1) * N))) (L + 1 + j)) := by
      simp only [Nat.cast_zero, zero_mul]; exact (hsumt 0 le_rfl (L + 1)).hasSum
    have hTS0le : ∑' j, s (((0 : ℕ) : ℝ) * (1 / ((lam + 1) * N))) (L + 1 + j) ≤ δ :=
      SC66V.tail_le (s 0) (hsn 0 le_rfl) (L + 1) _ δ hTS0
        (fun n' => hL1 0 ⟨le_rfl, hT2.le⟩ (L + 1) hLL1 n')
    have hl1 : l1dist (occ (z₀ N)) (s 0) ≤ ENNReal.ofReal δ := by
      rw [hs0]; exact (hN1 N hNN1).le
    have hE := SC66M.init_E (occ (z₀ N)) (s 0) (fun i => SC66P.occ_nonneg' _ i) (hsn 0 le_rfl) L
      (SC66D.tl (L + 1) (z₀ N)) _ (SC66D.occ_tail_hasSum _ _) hTS0 δ hδ0.le hl1
    have H8 : ∑ i ∈ Icc 1 L, |occ (Y N 0 ω) i - s 0 i| + SC66D.tl (L + 1) (Y N 0 ω) +
        ∑' j, s (((0 : ℕ) : ℝ) * (1 / ((lam + 1) * N))) (L + 1 + j) ≤ 3 * δ := by
      rw [h0]; linarith
    have hres := SC66P.chain_path lam K T2 a δ δ δ (3 * δ) L N n hN hlam hK0.le ha.le
      hδ0.le hδ0.le hδ0.le hT2n M (route N) hr (fun z => SC66L.geqd_inX hN z) p hpK s hs hsn
      hs00 hsX hlip (fun k => ∑' j, s (k * (1 / ((lam + 1) * N))) (L + 1 + j))
      (fun k => (hsumt _ (mul_nonneg (Nat.cast_nonneg _) hh0) (L + 1)).hasSum)
      (fun k hk n' => hL1 _ (hkt k hk) (L + 1) hLL1 n')
      (fun k hk n' => hL2 _ (hkt k hk.le) L hLL2 n')
      (fun j => Y N j ω) (fun k hk => (hgood k hk).le)
      (fun n' hn' i hi => (hAi i hi n' (hn'.trans hn)).le)
      (fun n' hn' => (hAt n' (hn'.trans hn)).le) H8
    have hb := bnd lam K T2 a δ ε n L (1 / ((lam + 1) * N)) hlam hK0.le (Nat.cast_nonneg _)
      hh0 haδ hT2n hrN hε hδε
    rw [show (n : ℝ) / ((lam + 1) * (N : ℝ)) = n * (1 / ((lam + 1) * N)) from
      (mul_one_div _ _).symm] at hfar
    rcases (ENNReal.ofReal_le_ofReal_iff').mp (hfar.trans hres) with h1 | h1 <;> linarith
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [h00, zero_add]
  exact (measure_union_le _ _).trans (add_le_add
    ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hAZo)) hAZt)

end SC66Q
end


set_option autoImplicit false
set_option linter.unusedSectionVars false

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SC66C

open StrictCompatLB.MeanField

/-! PLLN piece (5): the Poisson clock. With i.i.d. Exp(r) gaps, `sup_{t ≤ T} |n(t)/r - t| → 0`
in probability as `r → ∞` (two-sided Chernoff at finitely many grid indices + monotonicity). -/

lemma expM_Iio (r : ℝ) (hr : 0 < r) : expMeasure r (Set.Iio 0) = 0 := by
  have := isProbabilityMeasure_expMeasure hr
  have h := cdf_expMeasure_eq hr 0
  rw [if_pos le_rfl, mul_zero, neg_zero, Real.exp_zero, sub_self, cdf_eq_real,
    measureReal_def] at h
  have h0 : expMeasure r (Set.Iic 0) = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (measure_ne_top _ _)
  exact measure_mono_null Set.Iio_subset_Iic_self h0

lemma expM_Iic (r : ℝ) (hr : 0 < r) : expMeasure r (Set.Iic 0) = 0 := by
  have := isProbabilityMeasure_expMeasure hr
  have h := cdf_expMeasure_eq hr 0
  rw [if_pos le_rfl, mul_zero, neg_zero, Real.exp_zero, sub_self, cdf_eq_real,
    measureReal_def] at h
  exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (measure_ne_top _ _)

lemma lint_expθ (r θ : ℝ) (hr : 0 < r) (hθ : θ < r) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (θ * x)) ∂(expMeasure r) = ENNReal.ofReal (r / (r - θ)) := by
  have h1 : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  have hm : Measurable (exponentialPDF r) := (measurable_exponentialPDFReal r).ennreal_ofReal
  have hg : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x))) := by fun_prop
  have hrθ : 0 < r - θ := by linarith
  rw [h1, lintegral_withDensity_eq_lintegral_mul _ hm hg]
  have hpt : ∀ x, (exponentialPDF r * fun x => ENNReal.ofReal (Real.exp (θ * x))) x
      = ENNReal.ofReal (r / (r - θ)) * exponentialPDF (r - θ) x := by
    intro x
    simp only [Pi.mul_apply]
    by_cases hx : 0 ≤ x
    · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (div_nonneg hr.le hrθ.le)]
      congr 1
      rw [mul_assoc, ← Real.exp_add]
      have : -(r * x) + θ * x = -((r - θ) * x) := by ring
      rw [this, div_mul_eq_mul_div, eq_div_iff hrθ.ne']
      ring
    · rw [exponentialPDF_of_neg (lt_of_not_ge hx), exponentialPDF_of_neg (lt_of_not_ge hx),
        zero_mul, mul_zero]
  have hm2 : Measurable (exponentialPDF (r - θ)) := (measurable_exponentialPDFReal _).ennreal_ofReal
  rw [lintegral_congr hpt, lintegral_const_mul _ hm2,
    lintegral_exponentialPDF_eq_one hrθ, mul_one]

lemma int_expθ (r θ : ℝ) (hr : 0 < r) (hθ : θ < r) :
    ∫ x, Real.exp (θ * x) ∂(expMeasure r) = r / (r - θ) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun x => (Real.exp_pos _).le))
    (by fun_prop : Measurable (fun x : ℝ => Real.exp (θ * x))).aestronglyMeasurable,
    lint_expθ r θ hr hθ, ENNReal.toReal_ofReal (div_nonneg hr.le (by linarith))]

lemma integ_expθ (r θ : ℝ) (hr : 0 < r) (hθ : θ < r) :
    Integrable (fun x => Real.exp (θ * x)) (expMeasure r) := by
  refine ⟨(by fun_prop : Measurable (fun x : ℝ => Real.exp (θ * x))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => (Real.exp_pos _).le)),
    lint_expθ r θ hr hθ]
  exact ENNReal.ofReal_lt_top

lemma ineq1 (u : ℝ) (hu : 0 < u) (hu2 : u ≤ 1 / 2) : 1 / (1 - u) ≤ Real.exp (u + u ^ 2) := by
  rw [div_le_iff₀ (by linarith), Real.exp_add]
  have ha := Real.quadratic_le_exp_of_nonneg hu.le
  have hb := Real.add_one_le_exp (u ^ 2)
  have hab : (1 + u + u ^ 2 / 2) * (u ^ 2 + 1) ≤ Real.exp u * Real.exp (u ^ 2) :=
    mul_le_mul ha hb (by positivity) (Real.exp_pos _).le
  have h : 0 ≤ 1 - u - u ^ 2 - u ^ 3 := by nlinarith
  have h1u : 0 ≤ 1 - u := by linarith
  nlinarith [mul_nonneg (sq_nonneg u) h, mul_le_mul_of_nonneg_right hab h1u]

lemma ineq2 (u : ℝ) (hu : 0 < u) : 1 / (1 + u) ≤ Real.exp (-u + u ^ 2) := by
  rw [div_le_iff₀ (by linarith)]
  have := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-u + u ^ 2))
    (by linarith : (0 : ℝ) ≤ 1 + u)
  nlinarith [pow_pos hu 3]

variable (r : ℝ) (hr : 0 < r) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
  (τ : ℕ → Ω → ℝ) (hτ : ∀ k, Measurable (τ k)) (hlaw : ∀ k, P.map (τ k) = expMeasure r)

include hr hτ hlaw in
lemma tau_nonneg : ∀ᵐ ω ∂P, ∀ k, 0 ≤ τ k ω := by
  rw [ae_all_iff]
  intro k
  have h : P (τ k ⁻¹' Set.Iio 0) = 0 := by
    rw [← Measure.map_apply (hτ k) measurableSet_Iio, hlaw k, expM_Iio r hr]
  refine ae_iff.mpr ?_
  convert h using 2
  ext ω
  simp

include hr hτ hlaw in
lemma tau_pos : ∀ᵐ ω ∂P, ∀ k, 0 < τ k ω := by
  rw [ae_all_iff]
  intro k
  have h : P (τ k ⁻¹' Set.Iic 0) = 0 := by
    rw [← Measure.map_apply (hτ k) measurableSet_Iic, hlaw k, expM_Iic r hr]
  refine ae_iff.mpr ?_
  convert h using 2
  ext ω
  simp

include hr hτ hlaw in
lemma integ_tau (θ : ℝ) (hθ : θ < r) (k : ℕ) :
    Integrable (fun ω => Real.exp (θ * τ k ω)) P := by
  have h := integ_expθ r θ hr hθ
  rw [← hlaw k] at h
  exact (integrable_map_measure h.1 (hτ k).aemeasurable).mp h

include hr hτ hlaw in
lemma mgf_tauθ (θ : ℝ) (hθ : θ < r) (k : ℕ) : mgf (τ k) P θ = r / (r - θ) := by
  have hsm : AEStronglyMeasurable (fun x => Real.exp (θ * x)) (P.map (τ k)) :=
    (by fun_prop : Measurable (fun x : ℝ => Real.exp (θ * x))).aestronglyMeasurable
  calc mgf (τ k) P θ = ∫ x, Real.exp (θ * x) ∂(P.map (τ k)) :=
        (integral_map (hτ k).aemeasurable hsm).symm
    _ = r / (r - θ) := by rw [hlaw k, int_expθ r θ hr hθ]

variable [IsProbabilityMeasure P] (hind : iIndepFun τ P)

include hr hτ hlaw hind in
theorem upper (n : ℕ) (u d : ℝ) (hu : 0 < u) (hu2 : u ≤ 1 / 2) :
    P.real {ω | (n : ℝ) / r + d ≤ (∑ k ∈ Finset.range n, τ k) ω}
      ≤ Real.exp (n * u ^ 2 - u * r * d) := by
  have hθ : u * r < r := by nlinarith
  have hint := hind.integrable_exp_mul_sum (t := u * r) hτ (s := Finset.range n)
    (fun k _ => integ_tau r hr P τ hτ hlaw (u * r) hθ k)
  have hch := measure_ge_le_exp_mul_mgf (μ := P) (X := ∑ k ∈ Finset.range n, τ k)
    ((n : ℝ) / r + d) (by positivity : 0 ≤ u * r) hint
  rw [hind.mgf_sum hτ, Finset.prod_congr rfl (fun k _ => mgf_tauθ r hr P τ hτ hlaw (u * r) hθ k),
    Finset.prod_const, Finset.card_range] at hch
  refine hch.trans ?_
  have hq : r / (r - u * r) ≤ Real.exp (u + u ^ 2) := by
    have h1 : r / (r - u * r) = 1 / (1 - u) := by
      rw [div_eq_div_iff (by nlinarith : (0:ℝ) < r - u * r).ne' (by linarith : (0:ℝ) < 1 - u).ne']
      ring
    rw [h1]
    exact ineq1 u hu hu2
  have hp : (r / (r - u * r)) ^ n ≤ Real.exp (n * (u + u ^ 2)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (div_nonneg hr.le (by nlinarith)) hq n
  have e : (u * r) * ((n : ℝ) / r) = u * n := by field_simp
  calc Real.exp (-(u * r) * ((n : ℝ) / r + d)) * (r / (r - u * r)) ^ n
      ≤ Real.exp (-(u * r) * ((n : ℝ) / r + d)) * Real.exp (n * (u + u ^ 2)) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = Real.exp (n * u ^ 2 - u * r * d) := by
        rw [← Real.exp_add]
        congr 1
        linear_combination (-1 : ℝ) * e

include hr hτ hlaw hind in
theorem lower (n : ℕ) (u d : ℝ) (hu : 0 < u) :
    P.real {ω | (∑ k ∈ Finset.range n, τ k) ω ≤ (n : ℝ) / r - d}
      ≤ Real.exp (n * u ^ 2 - u * r * d) := by
  have hθ : -(u * r) < r := by nlinarith
  have hint := hind.integrable_exp_mul_sum (t := -(u * r)) hτ (s := Finset.range n)
    (fun k _ => integ_tau r hr P τ hτ hlaw (-(u * r)) hθ k)
  have hch := measure_le_le_exp_mul_mgf (μ := P) (X := ∑ k ∈ Finset.range n, τ k)
    ((n : ℝ) / r - d) (by nlinarith : -(u * r) ≤ 0) hint
  rw [hind.mgf_sum hτ,
    Finset.prod_congr rfl (fun k _ => mgf_tauθ r hr P τ hτ hlaw (-(u * r)) hθ k),
    Finset.prod_const, Finset.card_range] at hch
  refine hch.trans ?_
  have hq : r / (r - -(u * r)) ≤ Real.exp (-u + u ^ 2) := by
    have h1 : r / (r - -(u * r)) = 1 / (1 + u) := by
      rw [div_eq_div_iff (by nlinarith : (0:ℝ) < r - -(u * r)).ne' (by linarith : (0:ℝ) < 1 + u).ne']
      ring
    rw [h1]
    exact ineq2 u hu
  have hp : (r / (r - -(u * r))) ^ n ≤ Real.exp (n * (-u + u ^ 2)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (div_nonneg hr.le (by nlinarith)) hq n
  have e : (u * r) * ((n : ℝ) / r) = u * n := by field_simp
  calc Real.exp (-(-(u * r)) * ((n : ℝ) / r - d)) * (r / (r - -(u * r))) ^ n
      ≤ Real.exp (-(-(u * r)) * ((n : ℝ) / r - d)) * Real.exp (n * (-u + u ^ 2)) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = Real.exp (n * u ^ 2 - u * r * d) := by
        rw [← Real.exp_add]
        congr 1
        linear_combination e

include hr hτ hlaw hind in
theorem tail2 (n : ℕ) (u d : ℝ) (hu : 0 < u) (hu2 : u ≤ 1 / 2) :
    P {ω | d ≤ |(∑ k ∈ Finset.range n, τ k) ω - (n : ℝ) / r|}
      ≤ ENNReal.ofReal (2 * Real.exp (n * u ^ 2 - u * r * d)) := by
  have hsub : {ω | d ≤ |(∑ k ∈ Finset.range n, τ k) ω - (n : ℝ) / r|}
      ⊆ {ω | (n : ℝ) / r + d ≤ (∑ k ∈ Finset.range n, τ k) ω}
        ∪ {ω | (∑ k ∈ Finset.range n, τ k) ω ≤ (n : ℝ) / r - d} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    rcases le_abs.mp hω with h | h
    · left; linarith
    · right; linarith
  have hU := upper r hr P τ hτ hlaw hind n u d hu hu2
  have hL := lower r hr P τ hτ hlaw hind n u d hu
  calc P {ω | d ≤ |(∑ k ∈ Finset.range n, τ k) ω - (n : ℝ) / r|}
      ≤ P ({ω | (n : ℝ) / r + d ≤ (∑ k ∈ Finset.range n, τ k) ω}
        ∪ {ω | (∑ k ∈ Finset.range n, τ k) ω ≤ (n : ℝ) / r - d}) := measure_mono hsub
    _ ≤ P {ω | (n : ℝ) / r + d ≤ (∑ k ∈ Finset.range n, τ k) ω}
        + P {ω | (∑ k ∈ Finset.range n, τ k) ω ≤ (n : ℝ) / r - d} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (n * u ^ 2 - u * r * d))
        + ENNReal.ofReal (Real.exp (n * u ^ 2 - u * r * d)) := by
        gcongr
        · rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
          exact ENNReal.ofReal_le_ofReal (by rw [← measureReal_def]; exact hU)
        · rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
          exact ENNReal.ofReal_le_ofReal (by rw [← measureReal_def]; exact hL)
    _ = ENNReal.ofReal (2 * Real.exp (n * u ^ 2 - u * r * d)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul]

end SC66C

namespace SC66C2

open StrictCompatLB.MeanField

lemma S_mono (τ : ℕ → ℝ) (hτ : ∀ k, 0 ≤ τ k) {a b : ℕ} (h : a ≤ b) :
    ∑ k ∈ Finset.range a, τ k ≤ ∑ k ∈ Finset.range b, τ k :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun k _ _ => hτ k)

/-- Grid control: closeness at the indices `j g` (`j ≤ J`) gives closeness at every `n ≤ J g`. -/
lemma grid (τ : ℕ → ℝ) (hτ : ∀ k, 0 ≤ τ k) (r : ℝ) (hr : 0 < r) (g J : ℕ) (hg : 1 ≤ g) (η : ℝ)
    (h : ∀ j ≤ J, |∑ k ∈ Finset.range (j * g), τ k - ((j * g : ℕ) : ℝ) / r| < η) :
    ∀ n ≤ J * g, |∑ k ∈ Finset.range n, τ k - (n : ℝ) / r| ≤ η + g / r := by
  intro n hn
  have hj : n / g * g ≤ n := Nat.div_mul_le_self n g
  have hj2 : n < n / g * g + g := Nat.lt_div_mul_add (by omega)
  have hjJ : n / g ≤ J := by
    by_contra hc
    push_neg at hc
    have : (J + 1) * g ≤ n / g * g := Nat.mul_le_mul_right g hc
    nlinarith
  have hA := abs_lt.mp (h (n / g) hjJ)
  have hSa := S_mono τ hτ hj
  have ha : ((n / g * g : ℕ) : ℝ) ≤ n := by exact_mod_cast hj
  have hb : (n : ℝ) < ((n / g * g : ℕ) : ℝ) + g := by exact_mod_cast hj2
  have ha' : ((n / g * g : ℕ) : ℝ) / r ≤ (n : ℝ) / r := by gcongr
  have hb' : (n : ℝ) / r < ((n / g * g : ℕ) : ℝ) / r + (g : ℝ) / r := by
    rw [← add_div]; gcongr
  have hgr : 0 ≤ (g : ℝ) / r := by positivity
  rw [abs_le]
  constructor
  · linarith
  · rcases Nat.lt_or_ge (n / g) J with hlt | hge
    · have hB := abs_lt.mp (h (n / g + 1) (by omega))
      have hSb := S_mono τ hτ (show n ≤ (n / g + 1) * g by rw [add_mul, one_mul]; omega)
      have hcast : (((n / g + 1) * g : ℕ) : ℝ) / r = ((n / g * g : ℕ) : ℝ) / r + (g : ℝ) / r := by
        push_cast; rw [← add_div]; ring
      linarith
    · have hn' : n = n / g * g := by
        have : J * g ≤ n / g * g := Nat.mul_le_mul_right g hge
        omega
      rw [hn'] at hSa ⊢
      linarith [hA.2]

/-- Time change: closeness of `S_n` to `n/r` for all `n ≤ m` controls `n(t)/r - t` on `[0,T]`. -/
lemma time (τ : ℕ → ℝ) (hτ : ∀ k, 0 ≤ τ k) (r : ℝ) (hr : 0 < r) (m : ℕ) (η T : ℝ)
    (h : ∀ n ≤ m, |∑ k ∈ Finset.range n, τ k - (n : ℝ) / r| ≤ η)
    (hm : T + η < (m : ℝ) / r) (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    |(epochCount τ t : ℝ) / r - t| ≤ η + 1 / r := by
  have hbig : ∀ n, m ≤ n → t < ∑ k ∈ Finset.range n, τ k := by
    intro n hn
    have h1 := (abs_le.mp (h m le_rfl)).1
    have := S_mono τ hτ hn
    linarith
  have hne : {n : ℕ | ∑ k ∈ Finset.range n, τ k ≤ t}.Nonempty :=
    ⟨0, by simp only [Set.mem_ofPred_eq, Finset.range_zero, Finset.sum_empty]; exact ht0⟩
  have hbdd : BddAbove {n : ℕ | ∑ k ∈ Finset.range n, τ k ≤ t} := by
    refine ⟨m, fun n hn => ?_⟩
    by_contra hc
    push_neg at hc
    exact absurd (hn : ∑ k ∈ Finset.range n, τ k ≤ t) (not_le.mpr (hbig n hc.le))
  have hdef : epochCount τ t = sSup {n : ℕ | ∑ k ∈ Finset.range n, τ k ≤ t} := rfl
  have hmem := Nat.sSup_mem hne hbdd
  rw [← hdef] at hmem
  have hS0 : ∑ k ∈ Finset.range (epochCount τ t), τ k ≤ t := hmem
  have hnm : epochCount τ t < m := by
    by_contra hc
    push_neg at hc
    exact absurd hS0 (not_le.mpr (hbig _ hc))
  have hS1 : t < ∑ k ∈ Finset.range (epochCount τ t + 1), τ k := by
    by_contra hc
    push_neg at hc
    have := le_csSup hbdd (show epochCount τ t + 1 ∈ {n : ℕ | ∑ k ∈ Finset.range n, τ k ≤ t} from hc)
    rw [← hdef] at this
    omega
  have e1 := abs_le.mp (h _ hnm.le)
  have e2 := abs_le.mp (h _ hnm)
  have hcast : (((epochCount τ t + 1 : ℕ) : ℝ)) / r = (epochCount τ t : ℝ) / r + 1 / r := by
    push_cast; rw [add_div]
  rw [hcast] at e2
  have hr1 : 0 < 1 / r := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- **Poisson clock LLN.** If the gaps are i.i.d. `Exp(r N)` with `r N → ∞`, then
`sup_{t ∈ [0,T]} |n(t)/r N - t| → 0` in probability. -/
theorem clock (r : ℕ → ℝ) (hrt : Tendsto r atTop atTop)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ℕ → ℕ → Ω → ℝ)
    (hτ : ∀ᶠ N in atTop, (∀ k, Measurable (τ N k)) ∧ iIndepFun (τ N) P ∧
      ∀ k, P.map (τ N k) = expMeasure (r N))
    (T : ℝ) (hT : 0 ≤ T) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N => P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
      δ ≤ |(epochCount (fun k => τ N k ω) t : ℝ) / r N - t|}) atTop (𝓝 0) := by
  set d : ℝ := δ / 5 with hd_def
  have hd : 0 < d := by positivity
  set J : ℕ := ⌈(T + 4 * d) / d⌉₊ + 1 with hJ_def
  have hJ1 : (1 : ℝ) ≤ J := by rw [hJ_def]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈(T + 4 * d) / d⌉₊]
  have hJ : (T + 4 * d) / d + 1 ≤ (J : ℝ) := by
    rw [hJ_def]; push_cast; linarith [Nat.le_ceil ((T + 4 * d) / d)]
  set c : ℝ := (J : ℝ) * (d + 1) with hc_def
  have hc : 0 < c := by positivity
  have hdc : d < c := by rw [hc_def]; nlinarith
  set u : ℝ := d / (2 * c) with hu_def
  have hu : 0 < u := by positivity
  have hu2 : u ≤ 1 / 2 := by
    rw [hu_def, div_le_iff₀ (by positivity)]; linarith
  set κ : ℝ := d ^ 2 / (4 * c) with hκ_def
  have hκ : 0 < κ := by positivity
  have hkey : ∀ R : ℝ, c * R * u ^ 2 - u * R * d = -(R * κ) := by
    intro R; rw [hu_def, hκ_def]; field_simp; ring
  have hlim : Tendsto (fun N => ((J + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-(r N * κ))))
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun N => Real.exp (-(r N * κ))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hrt.atTop_mul_const hκ)
    have h3 := h2.const_mul 2
    rw [mul_zero] at h3
    have h4 := ENNReal.tendsto_ofReal h3
    rw [ENNReal.ofReal_zero] at h4
    have h5 := ENNReal.Tendsto.const_mul h4 (Or.inr (ENNReal.natCast_ne_top (J + 1)))
    rwa [mul_zero] at h5
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hτ, hrt.eventually_ge_atTop 1, hrt.eventually_ge_atTop (1 / d)]
    with N hN hr1 hrd
  obtain ⟨hm, hind, hlaw⟩ := hN
  have hR : 0 < r N := by linarith
  set R := r N with hR_def
  have h1R : 1 / R ≤ d := by
    rw [div_le_iff₀ hR]
    have := mul_le_mul_of_nonneg_left hrd hd.le
    rwa [mul_one_div_cancel hd.ne'] at this
  set g : ℕ := ⌈d * R⌉₊ with hg_def
  have hg1 : d * R ≤ g := Nat.le_ceil _
  have hg2 : (g : ℝ) < d * R + 1 := Nat.ceil_lt_add_one (by positivity)
  have hgpos : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have hgR : (g : ℝ) / R ≤ d + 1 / R := by
    rw [div_le_iff₀ hR, add_mul, one_div_mul_cancel hR.ne']; linarith
  have hgR' : d ≤ (g : ℝ) / R := by rw [le_div_iff₀ hR]; exact hg1
  have hsub : {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
      δ ≤ |(epochCount (fun k => τ N k ω) t : ℝ) / R - t|}
      ⊆ (⋃ j ∈ Finset.range (J + 1),
          {ω | d ≤ |(∑ k ∈ Finset.range (j * g), τ N k) ω - ((j * g : ℕ) : ℝ) / R|})
        ∪ {ω | ¬ ∀ k, 0 ≤ τ N k ω} := by
    intro ω hω
    obtain ⟨t, ⟨ht0, htT⟩, hb⟩ := hω
    by_contra hc
    rw [Set.mem_union, not_or] at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hnn : ∀ k, 0 ≤ τ N k ω := by
      by_contra h
      exact hc2 h
    have hgrid : ∀ j ≤ J, |∑ k ∈ Finset.range (j * g), τ N k ω - ((j * g : ℕ) : ℝ) / R| < d := by
      intro j hj
      have h1 : ω ∉ {ω | d ≤ |(∑ k ∈ Finset.range (j * g), τ N k) ω - ((j * g : ℕ) : ℝ) / R|} :=
        fun hb' => hc1 (Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))) hb')
      simp only [Set.mem_ofPred_eq, not_le, Finset.sum_apply] at h1
      exact h1
    have hall := grid (fun k => τ N k ω) hnn R hR g J hgpos d hgrid
    have hm' : T + (d + (g : ℝ) / R) < ((J * g : ℕ) : ℝ) / R := by
      rw [Nat.cast_mul, mul_div_assoc]
      have hmul := mul_le_mul hJ hgR' hd.le (by positivity)
      have hid : ((T + 4 * d) / d + 1) * d = T + 5 * d := by
        rw [add_mul, div_mul_cancel₀ _ hd.ne']; ring
      linarith
    have ht := time (fun k => τ N k ω) hnn R hR (J * g) (d + (g : ℝ) / R) T hall hm' t ht0 htT
    linarith
  calc P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, δ ≤ |(epochCount (fun k => τ N k ω) t : ℝ) / R - t|}
      ≤ P ((⋃ j ∈ Finset.range (J + 1),
          {ω | d ≤ |(∑ k ∈ Finset.range (j * g), τ N k) ω - ((j * g : ℕ) : ℝ) / R|})
        ∪ {ω | ¬ ∀ k, 0 ≤ τ N k ω}) := measure_mono hsub
    _ ≤ P (⋃ j ∈ Finset.range (J + 1),
          {ω | d ≤ |(∑ k ∈ Finset.range (j * g), τ N k) ω - ((j * g : ℕ) : ℝ) / R|})
        + P {ω | ¬ ∀ k, 0 ≤ τ N k ω} := measure_union_le _ _
    _ = P (⋃ j ∈ Finset.range (J + 1),
          {ω | d ≤ |(∑ k ∈ Finset.range (j * g), τ N k) ω - ((j * g : ℕ) : ℝ) / R|}) := by
        rw [ae_iff.mp (SC66C.tau_nonneg R hR P (τ N) hm hlaw), add_zero]
    _ ≤ ∑ j ∈ Finset.range (J + 1),
          P {ω | d ≤ |(∑ k ∈ Finset.range (j * g), τ N k) ω - ((j * g : ℕ) : ℝ) / R|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range (J + 1), ENNReal.ofReal (2 * Real.exp (-(R * κ))) := by
        refine Finset.sum_le_sum fun j hj => ?_
        refine (SC66C.tail2 R hR P (τ N) hm hlaw hind (j * g) u d hu hu2).trans ?_
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr ?_) (by norm_num))
        have hj' : (j : ℝ) ≤ J := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hg' : (g : ℝ) ≤ (d + 1) * R := by nlinarith
        have hjg : ((j * g : ℕ) : ℝ) ≤ c * R := by
          push_cast
          calc (j : ℝ) * g ≤ J * g := mul_le_mul_of_nonneg_right hj' (Nat.cast_nonneg _)
            _ ≤ J * ((d + 1) * R) := mul_le_mul_of_nonneg_left hg' (Nat.cast_nonneg _)
            _ = c * R := by rw [hc_def]; ring
        have := mul_le_mul_of_nonneg_right hjg (sq_nonneg u)
        linarith [hkey R]
    _ = ((J + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-(R * κ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! Time change glue: chain closeness + clock + level-law closeness on `[0,T]` give the
continuous-time uniform closeness (PLLN from the discrete chain statement). -/

open PowerOfDUniversality.Fluid

lemma l1_tri (a b c : ℕ → ℝ) : l1dist a c ≤ l1dist a b + l1dist b c := by
  unfold l1dist
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

lemma epoch_mem (τ : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    ∑ k ∈ Finset.range (epochCount τ t), τ k ≤ t := by
  unfold epochCount
  by_cases hb : BddAbove {n : ℕ | ∑ k ∈ Finset.range n, τ k ≤ t}
  · exact Nat.sSup_mem ⟨0, by simpa using ht⟩ hb
  · rw [Nat.sSup_of_not_bddAbove hb]; simpa using ht

lemma epoch_at (τ : ℕ → ℝ) (hτ : ∀ j, 0 < τ j) (k : ℕ) :
    epochCount τ (∑ j ∈ Finset.range k, τ j) = k := by
  unfold epochCount
  have hub : ∀ m ∈ {n : ℕ | ∑ j ∈ Finset.range n, τ j ≤ ∑ j ∈ Finset.range k, τ j}, m ≤ k := by
    intro m hm
    by_contra hc
    push_neg at hc
    have h1 : ∑ j ∈ Finset.range (k + 1), τ j ≤ ∑ j ∈ Finset.range m, τ j :=
      S_mono τ (fun j => (hτ j).le) hc
    rw [Finset.sum_range_succ] at h1
    have := hτ k
    have hm' : ∑ j ∈ Finset.range m, τ j ≤ ∑ j ∈ Finset.range k, τ j := hm
    linarith
  exact le_antisymm (csSup_le' fun m hm => hub m hm)
    (le_csSup ⟨k, fun m hm => hub m hm⟩
      (by show (∑ j ∈ Finset.range k, τ j) ≤ ∑ j ∈ Finset.range k, τ j; exact le_rfl))

theorem glue {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lam : ℝ) (hlam : 0 ≤ lam) (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ)
    (hτ : ∀ N, 1 ≤ N → (∀ k, Measurable (τ N k)) ∧ iIndepFun (τ N) P ∧
      ∀ k, P.map (τ N k) = expMeasure ((lam + 1) * (N : ℝ)))
    (gd : (N : ℕ) → (Fin N → ℕ) → ℝ≥0∞) (s : ℝ → ℕ → ℝ)
    (hlip : ∀ t u : ℝ, 0 ≤ t → 0 ≤ u →
      l1dist (s u) (s t) ≤ ENNReal.ofReal ((lam + 1) * |u - t|))
    (T : ℝ) (hT : 0 ≤ T) (ε : ℝ) (hε : 0 < ε) (η : ℝ)
    (hA : Tendsto (fun N : ℕ => P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal η ≤ gd N (statePath (Y N) (τ N) ω t)}) atTop (𝓝 0))
    (hC : Tendsto (fun N : ℕ => P {ω | ∃ n ≤ ⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊,
      (∀ k < n, gd N (Y N k ω) < ENNReal.ofReal η) ∧
      ENNReal.ofReal (ε / 2) ≤ l1dist (occ (Y N n ω)) (s ((n : ℝ) / ((lam + 1) * (N : ℝ))))})
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => P {ω | ENNReal.ofReal ε ≤ supDistL1 (occPath (Y N) (τ N) ω) s T})
      atTop (𝓝 0) := by
  have hl1 : 0 < lam + 1 := by linarith
  set δ : ℝ := min (1 / 2) (ε / (4 * (lam + 1))) with hδ_def
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ ε / (4 * (lam + 1)) := min_le_right _ _
  have h4 : δ * (4 * (lam + 1)) ≤ ε := (le_div_iff₀ (by positivity)).mp hδ2
  have hB := clock (fun N : ℕ => (lam + 1) * (N : ℝ))
    (Tendsto.const_mul_atTop hl1 tendsto_natCast_atTop_atTop) P τ
    (eventually_atTop.mpr ⟨1, fun N hN => hτ N hN⟩) T hT δ hδ
  have hsum := (hA.add hB).add hC
  rw [add_zero, add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  obtain ⟨hm, hind, hlaw⟩ := hτ N hN
  have hR : 0 < (lam + 1) * (N : ℝ) := mul_pos hl1 (by exact_mod_cast hN)
  have hZ : P {ω | ¬ ∀ k, 0 < τ N k ω} = 0 :=
    ae_iff.mp (SC66C.tau_pos _ hR P (τ N) hm hlaw)
  have hsub : {ω | ENNReal.ofReal ε ≤ supDistL1 (occPath (Y N) (τ N) ω) s T} ⊆
      (({ω | ∃ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal η ≤ gd N (statePath (Y N) (τ N) ω t)} ∪
        {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
          δ ≤ |(epochCount (fun k => τ N k ω) t : ℝ) / ((lam + 1) * (N : ℝ)) - t|}) ∪
        {ω | ∃ n ≤ ⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊,
          (∀ k < n, gd N (Y N k ω) < ENNReal.ofReal η) ∧
          ENNReal.ofReal (ε / 2) ≤ l1dist (occ (Y N n ω))
            (s ((n : ℝ) / ((lam + 1) * (N : ℝ))))}) ∪
        {ω | ¬ ∀ k, 0 < τ N k ω} := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    obtain ⟨⟨⟨hAω, hBω⟩, hCω⟩, hZω⟩ := hc
    have hpos : ∀ k, 0 < τ N k ω := by
      by_contra h
      exact hZω h
    have hpt : ∀ t ∈ Set.Icc (0 : ℝ) T,
        l1dist (occPath (Y N) (τ N) ω t) (s t) ≤ ENNReal.ofReal (3 * ε / 4) := by
      intro t ht
      have hclk : |(epochCount (fun k => τ N k ω) t : ℝ) / ((lam + 1) * (N : ℝ)) - t| < δ := by
        by_contra h
        push_neg at h
        exact hBω ⟨t, ht, h⟩
      have hmem := epoch_mem (fun k => τ N k ω) t ht.1
      have hab := abs_lt.mp hclk
      have hnle : epochCount (fun k => τ N k ω) t ≤ ⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊ := by
        have h1 : (epochCount (fun k => τ N k ω) t : ℝ) / ((lam + 1) * (N : ℝ)) ≤ T + 1 := by
          linarith [ht.2]
        rw [div_le_iff₀ hR] at h1
        exact_mod_cast h1.trans (Nat.le_ceil _)
      have hgood : ∀ k < epochCount (fun k => τ N k ω) t,
          gd N (Y N k ω) < ENNReal.ofReal η := by
        intro k hk
        have hSk := (S_mono (fun j => τ N j ω) (fun j => (hpos j).le) hk.le).trans hmem
        have hS0 : 0 ≤ ∑ j ∈ Finset.range k, τ N j ω :=
          Finset.sum_nonneg fun j _ => (hpos j).le
        have hst : statePath (Y N) (τ N) ω (∑ j ∈ Finset.range k, τ N j ω) = Y N k ω := by
          show Y N (epochCount (fun j => τ N j ω) (∑ j ∈ Finset.range k, τ N j ω)) ω = Y N k ω
          rw [epoch_at (fun j => τ N j ω) hpos k]
        by_contra h
        push_neg at h
        exact hAω ⟨_, ⟨hS0, hSk.trans ht.2⟩, by rw [hst]; exact h⟩
      have hch : l1dist (occ (Y N (epochCount (fun k => τ N k ω) t) ω))
          (s ((epochCount (fun k => τ N k ω) t : ℝ) / ((lam + 1) * (N : ℝ))))
            < ENNReal.ofReal (ε / 2) := by
        by_contra h
        push_neg at h
        exact hCω ⟨_, hnle, hgood, h⟩
      have hl := hlip t ((epochCount (fun k => τ N k ω) t : ℝ) / ((lam + 1) * (N : ℝ))) ht.1
        (div_nonneg (Nat.cast_nonneg _) hR.le)
      have hq : (lam + 1) * |(epochCount (fun k => τ N k ω) t : ℝ) / ((lam + 1) * (N : ℝ)) - t|
          ≤ ε / 4 := by
        have := mul_le_mul_of_nonneg_left hclk.le hl1.le
        linarith
      calc l1dist (occPath (Y N) (τ N) ω t) (s t)
          ≤ l1dist (occ (Y N (epochCount (fun k => τ N k ω) t) ω))
              (s ((epochCount (fun k => τ N k ω) t : ℝ) / ((lam + 1) * (N : ℝ))))
            + l1dist (s ((epochCount (fun k => τ N k ω) t : ℝ) / ((lam + 1) * (N : ℝ)))) (s t) :=
            l1_tri _ _ _
        _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4) :=
            add_le_add hch.le (hl.trans (ENNReal.ofReal_le_ofReal hq))
        _ = ENNReal.ofReal (3 * ε / 4) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
    have hsup : supDistL1 (occPath (Y N) (τ N) ω) s T ≤ ENNReal.ofReal (3 * ε / 4) := by
      unfold supDistL1
      exact iSup₂_le hpt
    have hlt : ENNReal.ofReal (3 * ε / 4) < ENNReal.ofReal ε :=
      (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)
    exact absurd ((hω : ENNReal.ofReal ε ≤ _).trans hsup) (not_le.mpr hlt)
  calc P {ω | ENNReal.ofReal ε ≤ supDistL1 (occPath (Y N) (τ N) ω) s T}
      ≤ P ((({ω | ∃ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal η ≤ gd N (statePath (Y N) (τ N) ω t)} ∪
        {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
          δ ≤ |(epochCount (fun k => τ N k ω) t : ℝ) / ((lam + 1) * (N : ℝ)) - t|}) ∪
        {ω | ∃ n ≤ ⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊,
          (∀ k < n, gd N (Y N k ω) < ENNReal.ofReal η) ∧
          ENNReal.ofReal (ε / 2) ≤ l1dist (occ (Y N n ω))
            (s ((n : ℝ) / ((lam + 1) * (N : ℝ))))}) ∪
        {ω | ¬ ∀ k, 0 < τ N k ω}) := measure_mono hsub
    _ ≤ P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal η ≤ gd N (statePath (Y N) (τ N) ω t)}
        + P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
          δ ≤ |(epochCount (fun k => τ N k ω) t : ℝ) / ((lam + 1) * (N : ℝ)) - t|}
        + P {ω | ∃ n ≤ ⌈(T + 1) * ((lam + 1) * (N : ℝ))⌉₊,
          (∀ k < n, gd N (Y N k ω) < ENNReal.ofReal η) ∧
          ENNReal.ofReal (ε / 2) ≤ l1dist (occ (Y N n ω))
            (s ((n : ℝ) / ((lam + 1) * (N : ℝ))))}
        + P {ω | ¬ ∀ k, 0 < τ N k ω} := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ = _ := by rw [hZ, add_zero]

end SC66C2

section
open Filter Topology MeasureTheory
open scoped ENNReal
open StrictCompatLB.MeanField PowerOfDUniversality.Fluid

open StrictCompatLB.MeanField in
theorem plln_zero_aux (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (route : (N : ℕ) → Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (hroute : ∀ N, 1 ≤ N → (∀ w z v, 0 ≤ route N w z v) ∧ ∀ w z, ∑ v, route N w z v = 1)
    (p : (ℕ → ℝ) → ℕ → ℝ) (hp : IsAssignmentFn p) (hLip : IsLipschitzPolicy p)
    (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ) (hq₀ : InY q₀)
    (hinit : Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0))
    (s : ℝ → ℕ → ℝ) (hs : IsPiTrajectory lam p s) (hsY : ∀ t : ℝ, 0 ≤ t → InY (s t))
    (hs0 : s 0 = q₀)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ)
    (hproc : ∀ N, 1 ≤ N → IsLBProcess P lam M N (route N) (z₀ N) (Y N) (τ N))
    (T : ℝ) (hT : 0 ≤ T)
    (hlev : ∀ η : ℝ, 0 < η → Tendsto (fun N => P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal η ≤ PowerOfDUniversality.Fluid.l1dist
        (fun i => (1 / (M N : ℝ)) * ∑ w : Fin (M N),
          ∑ v ∈ Finset.univ.filter (fun v => statePath (Y N) (τ N) ω t v = i),
            route N w (statePath (Y N) (τ N) ω t) v)
        (p (geqd (statePath (Y N) (τ N) ω t)))}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
        PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T})
      atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure P := (hproc 1 le_rfl).1
  obtain ⟨η, hη, hC⟩ := SC66Q.chain lam hlam0 M hM route hroute p hp hLip z₀ q₀ hinit s hs hsY
    hs0 P Y τ hproc T hT ε hε
  exact SC66C2.glue P lam hlam0 Y τ
    (fun N hN => ⟨(hproc N hN).2.2.2.1, (hproc N hN).2.2.2.2.1, (hproc N hN).2.2.2.2.2.1⟩)
    (fun N z => PowerOfDUniversality.Fluid.l1dist (SC66D.levA M N (route N) z) (p (geqd z))) s
    (fun t u ht hu => SC66O.l1_lip lam hlam0 p hp s hs hsY t u ht hu) T hT ε hε η
    (hlev η hη) hC

end

namespace SC9aZ
open Filter Topology MeasureTheory
open scoped ENNReal
open StrictCompatLB.MeanField PowerOfDUniversality.Fluid

/-- Uniform routing: every server is chosen with probability `1/N`. -/
noncomputable def unifRoute (M : ℕ → ℕ) (N : ℕ) : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ :=
  fun _ _ _ => 1 / (N : ℝ)

lemma lbKernel_zero (M : ℕ → ℕ) (N : ℕ) (r r' : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ) :
    lbKernel 0 M N r = lbKernel 0 M N r' := by
  funext z z'
  simp [lbKernel]

lemma unif_hroute (M : ℕ → ℕ) (N : ℕ) (hN : 1 ≤ N) :
    (∀ w z v, 0 ≤ unifRoute M N w z v) ∧ ∀ w z, ∑ v, unifRoute M N w z v = 1 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  refine ⟨fun w z v => by simp [unifRoute], fun w z => ?_⟩
  simp [unifRoute, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hN']

lemma lev_eq (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (N : ℕ) (hN : 1 ≤ N) (z : Fin N → ℕ) :
    (fun i => (1 / (M N : ℝ)) * ∑ w : Fin (M N),
        ∑ v ∈ Finset.univ.filter (fun v => z v = i), unifRoute M N w z v) = geqd z := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hM' : (M N : ℝ) ≠ 0 := by exact_mod_cast (hM N).ne'
  funext i
  simp only [unifRoute, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, geqd]
  field_simp

lemma traj_zero (d : ℕ) (s : ℝ → ℕ → ℝ) (hs : PowerTwoChoices.Limit.IsTrajectory 0 d s) :
    IsPiTrajectory 0 (fun x => x) s := by
  refine ⟨hs.1, fun i hi t ht => ?_⟩
  have h := hs.2 i hi t ht
  simpa [PowerTwoChoices.Limit.drift] using h

lemma id_assign : IsAssignmentFn (fun x => x) := fun x hx => ⟨hx.1, hx.2, fun _ h => h⟩

lemma id_lip : IsLipschitzPolicy (fun x => x) := ⟨1, one_pos, fun x y _ _ => by simp⟩

end SC9aZ

open Filter Topology MeasureTheory
open scoped ENNReal

open StrictCompatLB.MeanField in
theorem solution (d : ℕ) (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (route : (N : ℕ) → Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ) (hq₀ : InY q₀)
    (hinit : Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0))
    (s : ℝ → ℕ → ℝ) (hs : PowerTwoChoices.Limit.IsTrajectory 0 d s)
    (hsY : ∀ t : ℝ, 0 ≤ t → InY (s t)) (hs0 : s 0 = q₀)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ)
    (hproc : ∀ N, 1 ≤ N → IsLBProcess P 0 M N (route N) (z₀ N) (Y N) (τ N))
    (T : ℝ) (hT : 0 ≤ T) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
        PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T})
      atTop (𝓝 0) := by
  refine plln_zero_aux 0 le_rfl zero_lt_one M hM (fun N => SC9aZ.unifRoute M N)
    (fun N hN => SC9aZ.unif_hroute M N hN) (fun x => x) SC9aZ.id_assign SC9aZ.id_lip z₀ q₀ hq₀
    hinit s (SC9aZ.traj_zero d s hs) hsY hs0 Ω P Y τ (fun N hN => ?_) T hT ?_ ε hε
  · have h := hproc N hN
    unfold IsLBProcess at h ⊢
    rwa [SC9aZ.lbKernel_zero M N (SC9aZ.unifRoute M N) (route N)]
  · intro η hη
    refine (tendsto_const_nhds (x := (0 : ℝ≥0∞))).congr'
      (Filter.eventually_atTop.2 ⟨1, fun N hN => ?_⟩)
    symm
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    obtain ⟨t, -, ht⟩ := hω
    rw [SC9aZ.lev_eq M hM N hN] at ht
    have h0 : PowerOfDUniversality.Fluid.l1dist (geqd (statePath (Y N) (τ N) ω t))
        (geqd (statePath (Y N) (τ N) ω t)) = 0 := by
      simp [PowerOfDUniversality.Fluid.l1dist]
    rw [h0] at ht
    simp only [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at ht
    exact absurd ht (not_le.2 hη)
