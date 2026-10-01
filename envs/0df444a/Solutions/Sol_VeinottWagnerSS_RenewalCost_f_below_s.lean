-- Prove2me | solution 1 for VeinottWagnerSS.RenewalCost.f_below_s
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:53:54.772425+00:00
-- url     : https://prove2.me/submissions/60ddc876-62c4-40ef-904d-a3634e7254ba

import Definitions.Def_VeinottWagnerSS_Selection_Model
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Tactic
import Definitions.Def_VeinottWagnerSS_RenewalCost_PolicyCost

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

open VeinottWagnerSS.RenewalCost

namespace CInventory

noncomputable def demandPMF (D : DemandDist) : PMF ℕ :=
  ⟨fun k => ENNReal.ofReal (D.φ k), by
    have hsum : (∑' k, ENNReal.ofReal (D.φ k)) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg D.nonneg D.hasSum.summable,
        D.hasSum.tsum_eq, ENNReal.ofReal_one]
    exact hsum ▸ ENNReal.summable.hasSum⟩

theorem demandPMF_apply (D : DemandDist) (k : ℕ) :
    demandPMF D k = ENNReal.ofReal (D.φ k) := rfl

theorem map_sub_apply (p : PMF ℕ) (a z : ℤ) :
    (p.map (fun k : ℕ => a - (k : ℤ))) z = if z ≤ a then p (a - z).toNat else 0 := by
  by_cases hz : z ≤ a
  · have heq : ∀ k : ℕ, z = a - (k : ℤ) ↔ k = (a - z).toNat := by
      intro k
      omega
    simp [PMF.map_apply, heq, hz]
  · have hne : ∀ k : ℕ, z ≠ a - (k : ℤ) := by intro k; omega
    simp [PMF.map_apply, hne, hz]

theorem raw_law (D : DemandDist) (s S x : ℤ) (t : ℕ) (z : ℤ) :
    stateDist D s S x t z = (law (demandPMF D) s S x t z).toReal := by
  induction t generalizing z with
  | zero => simp [stateDist, law, PMF.pure_apply, apply_ite]
  | succ t ih =>
    simp only [stateDist]
    change (∑' y, stateDist D s S x t y *
      (if z ≤ VeinottWagnerSS.RenewalCost.sSOrder s S y then D.φ (VeinottWagnerSS.RenewalCost.sSOrder s S y - z).toNat else 0)) =
      (((law (demandPMF D) s S x t).bind (fun y =>
        (demandPMF D).map (fun k : ℕ => VeinottWagnerSS.Selection.sSOrder s S y - (k : ℤ)))) z).toReal
    rw [PMF.bind_apply, ENNReal.tsum_toReal_eq (fun y => ENNReal.mul_ne_top
      ((law (demandPMF D) s S x t).apply_ne_top y)
      (((demandPMF D).map (fun k : ℕ => VeinottWagnerSS.Selection.sSOrder s S y - (k : ℤ))).apply_ne_top z))]
    apply tsum_congr
    intro y
    rw [ENNReal.toReal_mul, ih, map_sub_apply]
    simp only [apply_ite, demandPMF_apply, ENNReal.toReal_ofReal (D.nonneg _), ENNReal.toReal_zero]
    simp only [VeinottWagnerSS.Selection.sSOrder, VeinottWagnerSS.RenewalCost.sSOrder]
    split_ifs <;> simp_all

theorem raw_total (D : DemandDist) (α K : ℝ) (G : ℤ → ℝ) (s S x : ℤ) :
    total (demandPMF D) α K G s S x = VeinottWagnerSS.RenewalCost.fCost D α K G s S x := by
  unfold total VeinottWagnerSS.RenewalCost.fCost
  apply tsum_congr
  intro t
  unfold ecost VeinottWagnerSS.RenewalCost.expectedPeriodCost
  simp only [raw_law]
  rfl

end CInventory


theorem solution (D : DemandDist) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hK : 0 ≤ K)
    (G : ℤ → ℝ) (s S : ℤ) (hsS : s ≤ S) (x : ℤ) (hx : x < s) :
    VeinottWagnerSS.RenewalCost.fCost D α K G s S x =
      K + VeinottWagnerSS.RenewalCost.fCost D α K G s S S := by
  simpa only [CInventory.raw_total] using
    CInventory.total_below (CInventory.demandPMF D) α K hα0 hα1 G s S hsS x hx
