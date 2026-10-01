-- Prove2me | solution 1 for VeinottWagnerSS.Selection.f_below_s
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:50:47.034827+00:00
-- url     : https://prove2.me/submissions/6c4c4153-eb1a-44a8-83ca-5d7e4965584c

import Definitions.Def_VeinottWagnerSS_Selection_Model
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

open VeinottWagnerSS.Selection

namespace CInventory

noncomputable def law (p : PMF ℕ) (s S x : ℤ) : ℕ → PMF ℤ
  | 0 => PMF.pure x
  | t + 1 => (law p s S x t).bind (fun y => p.map (fun k : ℕ => sSOrder s S y - (k : ℤ)))

noncomputable def pcost (K : ℝ) (G : ℤ → ℝ) (s S y : ℤ) : ℝ :=
  K * delta (sSOrder s S y - y) + G (sSOrder s S y)

noncomputable def ecost (p : PMF ℕ) (K : ℝ) (G : ℤ → ℝ) (s S x : ℤ) (t : ℕ) : ℝ :=
  ∑' y, (law p s S x t y).toReal * pcost K G s S y

noncomputable def total (p : PMF ℕ) (α K : ℝ) (G : ℤ → ℝ) (s S x : ℤ) : ℝ :=
  ∑' t, α ^ t * ecost p K G s S x t

theorem pmf_real_hasSum {ι : Type*} (p : PMF ι) : HasSum (fun a => (p a).toReal) 1 := by
  have h := ENNReal.hasSum_toReal p.tsum_coe_ne_top
  have ht : (∑' a, (p a).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe, ENNReal.toReal_one]
  exact ht ▸ h

theorem pmf_average_bound {ι : Type*} (p : PMF ι) (f : ι → ℝ) (C : ℝ)
    (hf : ∀ a ∈ p.support, ‖f a‖ ≤ C) :
    Summable (fun a => (p a).toReal * f a) ∧ ‖∑' a, (p a).toReal * f a‖ ≤ C := by
  have hp := pmf_real_hasSum p
  have hC : HasSum (fun a => (p a).toReal * C) C := by simpa using hp.mul_right C
  have hb : ∀ a, ‖(p a).toReal * f a‖ ≤ (p a).toReal * C := by
    intro a
    by_cases ha : a ∈ p.support
    · rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul_of_nonneg_left (hf a ha) ENNReal.toReal_nonneg
    · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
      simp [hz]
  have hs := hC.summable.of_norm_bounded hb
  exact ⟨hs, hs.hasSum.norm_le_of_bounded hC hb⟩

theorem order_lower (s S y : ℤ) (hsS : s ≤ S) : s ≤ sSOrder s S y := by
  unfold sSOrder
  split_ifs with h <;> omega

theorem order_upper (s S y U : ℤ) (hS : S ≤ U) (hy : y ≤ U) : sSOrder s S y ≤ U := by
  unfold sSOrder
  split_ifs <;> assumption

theorem law_support_upper (p : PMF ℕ) (s S x : ℤ) (t : ℕ) :
    ∀ y ∈ (law p s S x t).support, y ≤ max x S := by
  induction t with
  | zero =>
    intro y hy
    have hyx : y = x := by simpa [law] using hy
    subst y
    exact le_max_left _ _
  | succ t ih =>
    intro y hy
    simp only [law, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hy
    obtain ⟨z, hz, k, hk, rfl⟩ := hy
    have horder := order_upper s S z (max x S) (le_max_right _ _) (ih z hz)
    omega

theorem pcost_bound (K : ℝ) (G : ℤ → ℝ) (s S U : ℤ) (hsS : s ≤ S) (hSU : S ≤ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ≤ U, ‖pcost K G s S y‖ ≤ C := by
  let C := |K| + ∑ z ∈ Finset.Icc s U, |G z|
  have hsum0 : 0 ≤ ∑ z ∈ Finset.Icc s U, |G z| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C, add_nonneg (abs_nonneg K) hsum0, fun y hy => ?_⟩
  have hG : |G (sSOrder s S y)| ≤ ∑ z ∈ Finset.Icc s U, |G z| := by
    apply Finset.single_le_sum (f := fun z : ℤ => |G z|) (fun z _ => abs_nonneg (G z))
    exact Finset.mem_Icc.mpr ⟨order_lower s S y hsS, order_upper s S y U hSU hy⟩
  have hd : |K * delta (sSOrder s S y - y)| ≤ |K| := by
    unfold delta
    split_ifs <;> simp
  calc
    ‖pcost K G s S y‖ = |K * delta (sSOrder s S y - y) + G (sSOrder s S y)| := rfl
    _ ≤ |K * delta (sSOrder s S y - y)| + |G (sSOrder s S y)| := abs_add_le _ _
    _ ≤ C := add_le_add hd hG

theorem ecost_uniform_bound (p : PMF ℕ) (K : ℝ) (G : ℤ → ℝ) (s S x : ℤ) (hsS : s ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖ecost p K G s S x t‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := pcost_bound K G s S (max x S) hsS (le_max_right _ _)
  refine ⟨C, hC0, fun t => ?_⟩
  exact (pmf_average_bound (law p s S x t) (pcost K G s S) C
    (fun y hy => hC y (law_support_upper p s S x t y hy))).2

theorem total_summable (p : PMF ℕ) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (G : ℤ → ℝ) (s S x : ℤ) (hsS : s ≤ S) :
    Summable (fun t => α ^ t * ecost p K G s S x t) := by
  obtain ⟨C, hC0, hC⟩ := ecost_uniform_bound p K G s S x hsS
  apply ((summable_geometric_of_lt_one hα0 hα1).mul_right C).of_norm_bounded
  intro t
  rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hα0 _)]
  exact mul_le_mul_of_nonneg_left (hC t) (pow_nonneg hα0 _)

theorem law_below (p : PMF ℕ) (s S x : ℤ) (hsS : s ≤ S) (hx : x < s) (t : ℕ) :
    law p s S x (t + 1) = law p s S S (t + 1) := by
  induction t with
  | zero => simp [law, sSOrder, hx, not_lt.mpr hsS]
  | succ t ih =>
    change (law p s S x (t + 1)).bind _ = (law p s S S (t + 1)).bind _
    rw [ih]

theorem ecost_zero (p : PMF ℕ) (K : ℝ) (G : ℤ → ℝ) (s S x : ℤ) :
    ecost p K G s S x 0 = pcost K G s S x := by
  simp [ecost, law, PMF.pure_apply, ENNReal.toReal_one, apply_ite]

theorem total_below (p : PMF ℕ) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (G : ℤ → ℝ) (s S : ℤ) (hsS : s ≤ S) (x : ℤ) (hx : x < s) :
    total p α K G s S x = K + total p α K G s S S := by
  have he : ∀ t, ecost p K G s S x (t + 1) = ecost p K G s S S (t + 1) := by
    intro t
    unfold ecost
    rw [law_below p s S x hsS hx t]
  unfold total
  rw [(total_summable p α K hα0 hα1 G s S x hsS).tsum_eq_zero_add,
    (total_summable p α K hα0 hα1 G s S S hsS).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, he, ecost_zero]
  have hdiff : pcost K G s S x = K + pcost K G s S S := by
    simp [pcost, sSOrder, hx, not_lt.mpr hsS, delta, show x < S by omega]
  rw [hdiff]
  ring

end CInventory

namespace CInventory

theorem selection_law (M : Model) (s S x : ℤ) (t : ℕ) :
    law M.φ s S x t = stateLaw M s S x t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [law, stateLaw, ih]

theorem selection_total (M : Model) (α : ℝ) (s S x : ℤ) :
    total M.φ α M.K M.G s S x = fCost M α s S x := by
  unfold total fCost
  apply tsum_congr
  intro t
  unfold ecost expectedPeriodCost
  simp only [selection_law]
  rfl

end CInventory

theorem solution (M : Model) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (s S : ℤ) (hsS : s ≤ S) (x : ℤ) (hx : x < s) :
    fCost M α s S x = M.K + fCost M α s S S := by
  simpa only [CInventory.selection_total] using
    CInventory.total_below M.φ α M.K hα0 hα1 M.G s S hsS x hx
