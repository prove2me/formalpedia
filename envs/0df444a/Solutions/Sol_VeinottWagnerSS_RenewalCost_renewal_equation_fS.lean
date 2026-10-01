-- Prove2me | solution 1 for VeinottWagnerSS.RenewalCost.renewal_equation_fS
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:13:47.280663+00:00
-- url     : https://prove2.me/submissions/2edd045c-3cc1-4cc9-8ec6-2f9b4cde99e1

import Definitions.Def_VeinottWagnerSS_RenewalCost_RenewalFunctions
import Mathlib.Tactic
import Definitions.Def_VeinottWagnerSS_Selection_Model
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.Int.Interval
import Definitions.Def_VeinottWagnerSS_RenewalCost_PolicyCost
import Mathlib.Algebra.BigOperators.Intervals
section

open Filter VeinottWagnerSS.RenewalCost
open scoped Topology

namespace CVeinottRenewal

theorem summable_recurrence (u v : ℕ → ℝ) (q : ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hvs : Summable v) (hrec : ∀ n, u (n + 1) ≤ q * u n + v n) : Summable u := by
  apply summable_of_sum_range_le hu (c := (u 0 + ∑' n, v n) / (1 - q))
  intro N
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun n _ => hrec n)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hshift : (∑ n ∈ Finset.range N, u (n + 1)) + u 0 =
      (∑ n ∈ Finset.range N, u n) + u N := by
    rw [← Finset.sum_range_succ', Finset.sum_range_succ]
  have hbound := hvs.sum_le_tsum (Finset.range N) (fun n _ => hv n)
  apply (le_div_iff₀ (by linarith : 0 < 1 - q)).mpr
  nlinarith [hu N]

theorem conv_nonneg (D : DemandDist) (i k : ℕ) : 0 ≤ convPow D.φ i k := by
  induction i generalizing k with
  | zero => simp only [convPow]; split_ifs <;> norm_num
  | succ i hi =>
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (D.nonneg _) (hi j))

theorem weighted_conv_summable (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α)
    (hφ0 : α * D.φ 0 < 1) (k : ℕ) :
    Summable (fun i : ℕ => α ^ i * convPow D.φ i k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    let u : ℕ → ℝ := fun i => α ^ i * convPow D.φ i k
    let v : ℕ → ℝ := fun i => ∑ j ∈ Finset.range k,
      (α * D.φ (k - j)) * (α ^ i * convPow D.φ i j)
    have hu : ∀ i, 0 ≤ u i := fun i => mul_nonneg (pow_nonneg hα0 _) (conv_nonneg D _ _)
    have hv : ∀ i, 0 ≤ v i := fun i => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg hα0 (D.nonneg _)) (mul_nonneg (pow_nonneg hα0 _) (conv_nonneg D _ _)))
    have hvs : Summable v := by
      apply summable_sum
      intro j hj
      exact (ih j (Finset.mem_range.mp hj)).mul_left (α * D.φ (k - j))
    apply summable_recurrence u v (α * D.φ 0) hu hv (mul_nonneg hα0 (D.nonneg 0)) hφ0 hvs
    intro i
    have heq : u (i + 1) = (α * D.φ 0) * u i + v i := by
      dsimp [u, v]
      simp only [convPow]
      rw [Finset.sum_range_succ, mul_add, Nat.sub_self]
      simp only [Finset.mul_sum]
      rw [add_comm]
      congr 1
      · rw [pow_succ]; ring
      · apply Finset.sum_congr rfl
        intro j hj
        rw [pow_succ]
        ring
    exact heq.le

theorem weighted_cdf_summable (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α)
    (hφ0 : α * D.φ 0 < 1) (k : ℕ) :
    Summable (fun i : ℕ => α ^ i * cdfPow D.φ i k) := by
  simp only [cdfPow, Finset.mul_sum]
  apply summable_sum
  intro j hj
  exact weighted_conv_summable D α hα0 hφ0 j

theorem appendix_summable (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α)
    (hφ0 : α * D.φ 0 < 1) (k : ℕ) :
    Summable (fun i : ℕ => α ^ (i + 1) * cdfPow D.φ (i + 1) k) := by
  exact (weighted_cdf_summable D α hα0 hφ0 k).comp_injective
    (show Function.Injective (fun i : ℕ => i + 1) by intro a b h; exact Nat.add_right_cancel h)

end CVeinottRenewal

namespace CVeinottRenewal

theorem weighted_conv_succ_summable (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α)
    (hφ0 : α * D.φ 0 < 1) (k : ℕ) :
    Summable (fun i : ℕ => α ^ (i + 1) * convPow D.φ (i + 1) k) := by
  exact (weighted_conv_summable D α hα0 hφ0 k).comp_injective
    (show Function.Injective (fun i : ℕ => i + 1) by intro a b h; exact Nat.add_right_cancel h)

theorem LAlpha_interchange (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α)
    (hφ0 : α * D.φ 0 < 1) (G : ℤ → ℝ) (x : ℤ) (d : ℕ) :
    Summable (fun i : ℕ => ∑ k ∈ Finset.range (d + 1),
        |α ^ (i + 1) * G (x - (k : ℤ)) * convPow D.φ (i + 1) k|) ∧
      LAlpha D.φ α G x d =
        G x + ∑ j ∈ Finset.range (d + 1), G (x - (j : ℤ)) * mAlpha D.φ α j := by
  have hterm : ∀ k : ℕ, Summable (fun i : ℕ =>
      α ^ (i + 1) * G (x - (k : ℤ)) * convPow D.φ (i + 1) k) := by
    intro k
    convert! (weighted_conv_succ_summable D α hα0 hφ0 k).mul_left (G (x - (k : ℤ))) using 1
    congr 1
    funext i
    ring
  constructor
  · apply summable_sum
    intro k hk
    exact (hterm k).abs
  · unfold LAlpha
    rw [Summable.tsum_finsetSum (fun k _ => hterm k)]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    unfold mAlpha
    rw [← (weighted_conv_succ_summable D α hα0 hφ0 k).tsum_mul_left]
    apply tsum_congr
    intro i
    ring

theorem rAlpha_closed_form (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α)
    (hφ0 : α * D.φ 0 < 1) (d : ℕ) :
    rAlpha D.φ α d = α - (1 - α) * MAlpha D.φ α d := by
  have hs := weighted_cdf_summable D α hα0 hφ0 d
  have hs' := appendix_summable D α hα0 hφ0 d
  have hfirst : Summable (fun i : ℕ => α ^ (i + 1) * cdfPow D.φ i d) := by
    simpa only [pow_succ', mul_assoc] using hs.mul_left α
  have hzero : cdfPow D.φ 0 d = 1 := by
    simp [cdfPow, convPow]
  have htotal : (∑' i : ℕ, α ^ i * cdfPow D.φ i d) = 1 + MAlpha D.φ α d := by
    rw [hs.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, hzero, MAlpha]
  have hfirst_eq : (∑' i : ℕ, α ^ (i + 1) * cdfPow D.φ i d) =
      α * (1 + MAlpha D.φ α d) := by
    simp_rw [pow_succ', mul_assoc]
    rw [hs.tsum_mul_left, htotal]
  unfold rAlpha
  simp only [mul_sub]
  rw [hfirst.tsum_sub hs', hfirst_eq]
  change α * (1 + MAlpha D.φ α d) - MAlpha D.φ α d = _
  ring

end CVeinottRenewal
end
section

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
end
section

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

end
section

namespace CInventory

noncomputable def avg {ι : Type*} (p : PMF ι) (f : ι → ℝ) : ℝ :=
  ∑' a, (p a).toReal * f a

theorem bind_real {ι κ : Type*} (p : PMF ι) (q : ι → PMF κ) (b : κ) :
    ((p.bind q) b).toReal = ∑' a, (p a).toReal * (q a b).toReal := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq (fun a => ENNReal.mul_ne_top
    (p.apply_ne_top a) ((q a).apply_ne_top b))]
  simp only [ENNReal.toReal_mul]

theorem avg_bind {ι κ : Type*} (p : PMF ι) (q : ι → PMF κ) (f : κ → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ b, ‖f b‖ ≤ C) :
    avg (p.bind q) f = avg p (fun a => avg (q a) f) := by
  have hmajor : Summable (fun ab : ι × κ => (p ab.1).toReal * (q ab.1 ab.2).toReal * C) := by
    apply (summable_prod_of_nonneg (fun ab => by positivity)).mpr
    constructor
    · intro a
      exact ((pmf_real_hasSum (q a)).summable.mul_left (p a).toReal).mul_right C
    · simp_rw [mul_assoc, tsum_mul_left, tsum_mul_right, (pmf_real_hasSum _).tsum_eq, one_mul]
      exact (pmf_real_hasSum p).summable.mul_right C
  have hjoint : Summable (fun ab : ι × κ => (p ab.1).toReal * (q ab.1 ab.2).toReal * f ab.2) := by
    apply hmajor.of_norm_bounded
    intro ab
    rw [norm_mul, norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg,
      Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left (hf ab.2) (by positivity)
  unfold avg
  simp_rw [bind_real, ← tsum_mul_right]
  rw [hjoint.tsum_comm]
  simp_rw [mul_assoc, tsum_mul_left]

theorem avg_eq_of_support {ι : Type*} (p : PMF ι) (f g : ι → ℝ)
    (hfg : ∀ a ∈ p.support, f a = g a) : avg p f = avg p g := by
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [hfg a ha]
  · simp [(p.apply_eq_zero_iff a).mpr ha]

theorem avg_map {ι κ : Type*} (p : PMF ι) (g : ι → κ) (f : κ → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ b, ‖f b‖ ≤ C) :
    avg (p.map g) f = avg p (fun a => f (g a)) := by
  rw [PMF.map, avg_bind p (PMF.pure ∘ g) f C hC hf]
  unfold avg
  simp [PMF.pure_apply, apply_ite]

end CInventory

namespace CInventory

open VeinottWagnerSS.Selection

theorem law_first (p : PMF ℕ) (s S x : ℤ) (t : ℕ) :
    law p s S x (t + 1) = p.bind (fun k : ℕ => law p s S (sSOrder s S x - (k : ℤ)) t) := by
  induction t with
  | zero => simp [law, PMF.map, Function.comp_def]
  | succ t ih =>
    change (law p s S x (t + 1)).bind _ = _
    rw [ih, PMF.bind_bind]
    rfl

theorem law_support_upper_of_le (p : PMF ℕ) (s S x U : ℤ) (hS : S ≤ U) (hx : x ≤ U)
    (t : ℕ) (z : ℤ) (hz : z ∈ (law p s S x t).support) : z ≤ U :=
  (law_support_upper p s S x t z hz).trans (max_le hx hS)

theorem ecost_bound_of_le (p : PMF ℕ) (K : ℝ) (G : ℤ → ℝ) (s S U : ℤ)
    (hSU : S ≤ U) (C : ℝ) (hbound : ∀ y ≤ U, ‖pcost K G s S y‖ ≤ C)
    (x : ℤ) (hx : x ≤ U) (t : ℕ) : ‖ecost p K G s S x t‖ ≤ C :=
  (pmf_average_bound (law p s S x t) (pcost K G s S) C
    (fun z hz => hbound z (law_support_upper_of_le p s S x U hSU hx t z hz))).2

theorem ecost_first (p : PMF ℕ) (K : ℝ) (G : ℤ → ℝ) (s S x : ℤ) (hsS : s ≤ S) (t : ℕ) :
    ecost p K G s S x (t + 1) =
      ∑' k : ℕ, (p k).toReal * ecost p K G s S (sSOrder s S x - (k : ℤ)) t := by
  let U := max x S
  obtain ⟨C, hC, hbound⟩ := pcost_bound K G s S U hsS (le_max_right _ _)
  let f : ℤ → ℝ := fun y => if y ≤ U then pcost K G s S y else 0
  have hf : ∀ y, ‖f y‖ ≤ C := by
    intro y
    dsimp [f]
    split_ifs with hy
    · exact hbound y hy
    · simpa using hC
  have hclip : ∀ z ≤ U, ∀ n, avg (law p s S z n) f = ecost p K G s S z n := by
    intro z hz n
    apply avg_eq_of_support
    intro y hy
    exact if_pos (law_support_upper_of_le p s S z U (le_max_right _ _) hz n y hy)
  have hnext : ∀ k : ℕ, sSOrder s S x - (k : ℤ) ≤ U := by
    intro k
    have := order_upper s S x U (le_max_right _ _) (le_max_left _ _)
    omega
  rw [← hclip x (le_max_left _ _) (t + 1), law_first, avg_bind p _ f C hC hf]
  unfold avg
  apply tsum_congr
  intro k
  change (p k).toReal * avg (law p s S (sSOrder s S x - (k : ℤ)) t) f = _
  rw [hclip _ (hnext k) t]

theorem total_first (p : PMF ℕ) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (G : ℤ → ℝ) (s S x : ℤ) (hsS : s ≤ S) :
    total p α K G s S x = pcost K G s S x +
      α * ∑' k : ℕ, (p k).toReal * total p α K G s S (sSOrder s S x - (k : ℤ)) := by
  let U := max x S
  obtain ⟨C, hC, hbound⟩ := pcost_bound K G s S U hsS (le_max_right _ _)
  have hnext : ∀ k : ℕ, sSOrder s S x - (k : ℤ) ≤ U := by
    intro k
    have := order_upper s S x U (le_max_right _ _) (le_max_left _ _)
    omega
  have he : ∀ k t : ℕ, ‖ecost p K G s S (sSOrder s S x - (k : ℤ)) t‖ ≤ C := by
    intro k t
    exact ecost_bound_of_le p K G s S U (le_max_right _ _) C hbound _ (hnext k) t
  have hmajor : Summable (fun tk : ℕ × ℕ => α ^ tk.1 * (p tk.2).toReal * C) := by
    apply (summable_prod_of_nonneg (fun tk => by positivity)).mpr
    constructor
    · intro t
      exact ((pmf_real_hasSum p).summable.mul_left (α ^ t)).mul_right C
    · simp_rw [mul_assoc, tsum_mul_left, tsum_mul_right, (pmf_real_hasSum p).tsum_eq, one_mul]
      exact (summable_geometric_of_lt_one hα0 hα1).mul_right C
  have hjoint : Summable (fun tk : ℕ × ℕ => α ^ tk.1 * (p tk.2).toReal *
      ecost p K G s S (sSOrder s S x - (tk.2 : ℤ)) tk.1) := by
    apply hmajor.of_norm_bounded
    intro tk
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (pow_nonneg hα0 _),
      Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left (he _ _) (by positivity)
  unfold total
  rw [(total_summable p α K hα0 hα1 G s S x hsS).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, ecost_zero]
  congr 1
  simp_rw [ecost_first p K G s S x hsS, pow_succ', mul_assoc, ← tsum_mul_left]
  calc
    _ = ∑' k : ℕ, ∑' t : ℕ, α * (α ^ t * ((p k).toReal *
        ecost p K G s S (sSOrder s S x - (k : ℤ)) t)) := by
      have hh : Summable (Function.uncurry (fun t k : ℕ => α * (α ^ t * ((p k).toReal *
          ecost p K G s S (sSOrder s S x - (k : ℤ)) t)))) := by
        convert! hjoint.mul_left α using 1
        funext tk
        dsimp [Function.uncurry]
        ring
      exact hh.tsum_comm.symm
    _ = _ := by
      apply tsum_congr
      intro k
      apply tsum_congr
      intro t
      ring

end CInventory


namespace CInventory

open VeinottWagnerSS.Selection

theorem total_uniform_bound (p : PMF ℕ) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (G : ℤ → ℝ) (s S U : ℤ) (hsS : s ≤ S) (hSU : S ≤ U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ≤ U, ‖total p α K G s S x‖ ≤ B := by
  obtain ⟨C, hC, hbound⟩ := pcost_bound K G s S U hsS hSU
  let B : ℝ := ∑' t : ℕ, α ^ t * C
  refine ⟨B, tsum_nonneg (fun t => mul_nonneg (pow_nonneg hα0 _) hC), fun x hx => ?_⟩
  apply (total_summable p α K hα0 hα1 G s S x hsS).hasSum.norm_le_of_bounded
    ((summable_geometric_of_lt_one hα0 hα1).mul_right C).hasSum
  intro t
  rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hα0 _)]
  exact mul_le_mul_of_nonneg_left
    (ecost_bound_of_le p K G s S U hSU C hbound x hx t) (pow_nonneg hα0 _)

theorem weighted_total_summable (p : PMF ℕ) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (G : ℤ → ℝ) (s S x : ℤ) (hsS : s ≤ S) :
    Summable (fun k : ℕ => (p k).toReal * total p α K G s S (x - (k : ℤ))) := by
  obtain ⟨B, hB, hb⟩ := total_uniform_bound p α K hα0 hα1 G s S (max x S) hsS (le_max_right _ _)
  apply (pmf_average_bound p (fun k : ℕ => total p α K G s S (x - (k : ℤ))) B ?_).1
  intro k hk
  apply hb
  have := le_max_left x S
  omega

theorem total_eq_of_eq_below (p : PMF ℕ) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (G : ℤ → ℝ) (s S s' S' : ℤ) (hsS : s ≤ S) (hsS' : s' ≤ S') (hss' : s ≤ s')
    (heq : ∀ x : ℤ, x < s' → total p α K G s S x = total p α K G s' S' x) :
    ∀ x : ℤ, total p α K G s S x = total p α K G s' S' x := by
  let F := total p α K G s S
  let H := total p α K G s' S'
  have hstep : ∀ x : ℤ, s' ≤ x → (∀ y < x, F y = H y) → F x = H x := by
    intro x hx hi
    have h1 := total_first p α K hα0 hα1 G s S x hsS
    have h2 := total_first p α K hα0 hα1 G s' S' x hsS'
    have hxs : s ≤ x := hss'.trans hx
    simp only [pcost, sSOrder, not_lt.mpr hx, not_lt.mpr hxs, if_false,
      sub_self, delta, lt_self_iff_false, mul_zero, zero_add] at h1 h2
    have hs1 := weighted_total_summable p α K hα0 hα1 G s S x hsS
    have hs2 := weighted_total_summable p α K hα0 hα1 G s' S' x hsS'
    have hdiff : (∑' k : ℕ, (p k).toReal * F (x - (k : ℤ))) -
        (∑' k : ℕ, (p k).toReal * H (x - (k : ℤ))) = (p 0).toReal * (F x - H x) := by
      rw [← hs1.tsum_sub hs2, tsum_eq_single 0]
      · simp [F, H]
        ring
      · intro k hk
        have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        have hh := hi (x - (k : ℤ)) (by omega)
        change (p k).toReal * F (x - (k : ℤ)) - (p k).toReal * H (x - (k : ℤ)) = 0
        rw [hh, sub_self]
    have hp0 : (p 0).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one 0)
    have hq : α * (p 0).toReal < 1 :=
      (mul_le_mul_of_nonneg_left hp0 hα0).trans_lt (by simpa using hα1)
    have hrel : F x - H x = α * (p 0).toReal * (F x - H x) := by
      calc
        F x - H x = α * ((∑' k : ℕ, (p k).toReal * F (x - (k : ℤ))) -
            (∑' k : ℕ, (p k).toReal * H (x - (k : ℤ)))) := by
          dsimp [F, H]
          rw [h1, h2]
          ring
        _ = _ := by rw [hdiff]; ring
    have hz : (1 - α * (p 0).toReal) * (F x - H x) = 0 := by nlinarith [hrel]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (by linarith))
  have hall : ∀ n : ℕ, ∀ x : ℤ, (x - s').toNat = n → F x = H x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hn
      by_cases hx : x < s'
      · exact heq x hx
      · apply hstep x (le_of_not_gt hx)
        intro y hy
        by_cases hy' : y < s'
        · exact heq y hy'
        · exact ih (y - s').toNat (by omega) y rfl
  intro x
  exact hall _ x rfl

end CInventory
end
section

open VeinottWagnerSS.RenewalCost

namespace CInventoryGreen

theorem convolution_sum (D : DemandDist) (n d : ℕ) (H : ℕ → ℝ) :
    (∑ l ∈ Finset.range (d + 1), convPow D.φ (n + 1) l * H l) =
      ∑ j ∈ Finset.range (d + 1), convPow D.φ n j *
        ∑ k ∈ Finset.range (d - j + 1), D.φ k * H (j + k) := by
  calc
    _ = ∑ l ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (l + 1),
        D.φ (l - j) * convPow D.φ n j * H (j + (l - j)) := by
      apply Finset.sum_congr rfl
      intro l hl
      simp only [convPow, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    _ = ∑ j ∈ Finset.range (d + 1), ∑ k ∈ Finset.range (d + 1 - j),
        D.φ k * convPow D.φ n j * H (j + k) :=
      Finset.sum_range_diag_flip (d + 1) (fun j k => D.φ k * convPow D.φ n j * H (j + k))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjd : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have heq : d + 1 - j = d - j + 1 := by omega
      rw [heq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem weighted_sum_summable (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α)
    (hφ0 : α * D.φ 0 < 1) (H : ℕ → ℝ) (d : ℕ) :
    Summable (fun n : ℕ => α ^ n * ∑ j ∈ Finset.range (d + 1), convPow D.φ n j * H j) := by
  simp only [Finset.mul_sum, ← mul_assoc]
  apply summable_sum
  intro j hj
  exact (CVeinottRenewal.weighted_conv_summable D α hα0 hφ0 j).mul_right (H j)

theorem green_solution (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α)
    (hφ0 : α * D.φ 0 < 1) (c H : ℕ → ℝ) (d : ℕ)
    (hrec : ∀ j ≤ d, H j = c j + α * ∑ k ∈ Finset.range (d - j + 1), D.φ k * H (j + k)) :
    H 0 = ∑' n : ℕ, α ^ n * ∑ j ∈ Finset.range (d + 1), convPow D.φ n j * c j := by
  let V : ℕ → ℝ := fun n => α ^ n * ∑ j ∈ Finset.range (d + 1), convPow D.φ n j * H j
  let P : ℕ → ℝ := fun n => α ^ n * ∑ j ∈ Finset.range (d + 1), convPow D.φ n j * c j
  have hs : Summable V := weighted_sum_summable D α hα0 hφ0 H d
  have hshift : Summable (fun n => V (n + 1)) := hs.comp_injective (by intro a b h; exact Nat.add_right_cancel h)
  have hdiff : ∀ n, V n - V (n + 1) = P n := by
    intro n
    have hsum : (∑ j ∈ Finset.range (d + 1), convPow D.φ n j * H j) =
        (∑ j ∈ Finset.range (d + 1), convPow D.φ n j * c j) +
          α * ∑ j ∈ Finset.range (d + 1), convPow D.φ (n + 1) j * H j := by
      calc
        _ = ∑ j ∈ Finset.range (d + 1), convPow D.φ n j *
            (c j + α * ∑ k ∈ Finset.range (d - j + 1), D.φ k * H (j + k)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← hrec j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
        _ = (∑ j ∈ Finset.range (d + 1), convPow D.φ n j * c j) +
            α * ∑ j ∈ Finset.range (d + 1), convPow D.φ n j *
              ∑ k ∈ Finset.range (d - j + 1), D.φ k * H (j + k) := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by rw [← convolution_sum D n d H]
    dsimp [V, P]
    rw [hsum, pow_succ]
    ring
  have ht := hs.tsum_sub hshift
  simp only [hdiff] at ht
  have hz := hs.tsum_eq_zero_add
  have hv0 : V 0 = H 0 := by simp [V, convPow]
  rw [hv0] at hz
  change H 0 = ∑' n, P n
  linarith

end CInventoryGreen
end
section

open VeinottWagnerSS.RenewalCost

namespace CInventoryGreen

theorem cost_green (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α) (hφ0 : α * D.φ 0 < 1)
    (G : ℤ → ℝ) (x : ℤ) (d : ℕ) :
    (∑' n : ℕ, α ^ n * ∑ j ∈ Finset.range (d + 1), convPow D.φ n j * G (x - (j : ℤ))) =
      LAlpha D.φ α G x d := by
  have hzero : α ^ (0 : ℕ) * (∑ j ∈ Finset.range (d + 1), convPow D.φ 0 j * G (x - (j : ℤ))) = G x := by
    simp [convPow]
  rw [(weighted_sum_summable D α hα0 hφ0 (fun j => G (x - (j : ℤ))) d).tsum_eq_zero_add, hzero]
  unfold LAlpha
  congr 1
  apply tsum_congr
  intro n
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem cdf_green (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α) (hφ0 : α * D.φ 0 < 1) (d : ℕ) :
    (∑' n : ℕ, α ^ n * cdfPow D.φ n d) = 1 + MAlpha D.φ α d := by
  rw [(CVeinottRenewal.weighted_cdf_summable D α hα0 hφ0 d).tsum_eq_zero_add]
  simp [cdfPow, convPow, MAlpha]

theorem shifted_cost_green (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α) (hφ0 : α * D.φ 0 < 1)
    (G : ℤ → ℝ) (x : ℤ) (d : ℕ) (C : ℝ) :
    (∑' n : ℕ, α ^ n * ∑ j ∈ Finset.range (d + 1), convPow D.φ n j * (G (x - (j : ℤ)) - C)) =
      LAlpha D.φ α G x d - C * (1 + MAlpha D.φ α d) := by
  have heq : ∀ n : ℕ,
      α ^ n * (∑ j ∈ Finset.range (d + 1), convPow D.φ n j * (G (x - (j : ℤ)) - C)) =
        (α ^ n * ∑ j ∈ Finset.range (d + 1), convPow D.φ n j * G (x - (j : ℤ))) -
          C * (α ^ n * cdfPow D.φ n d) := by
    intro n
    simp only [mul_sub, Finset.sum_sub_distrib, cdfPow]
    rw [← Finset.sum_mul]
    ring
  simp_rw [heq]
  rw [(weighted_sum_summable D α hα0 hφ0 (fun j => G (x - (j : ℤ))) d).tsum_sub
    ((CVeinottRenewal.weighted_cdf_summable D α hα0 hφ0 d).mul_left C)]
  rw [tsum_mul_left, cost_green D α hα0 hφ0 G x d, cdf_green D α hα0 hφ0 d]

theorem ofReal_demand (D : DemandDist) (k : ℕ) :
    (CInventory.demandPMF D k).toReal = D.φ k := by
  exact ENNReal.toReal_ofReal (D.nonneg k)

theorem discount_zero_lt_one (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    α * D.φ 0 < 1 := by
  have hφ : D.φ 0 ≤ 1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top ((CInventory.demandPMF D).coe_le_one 0)
    simpa only [ofReal_demand, ENNReal.toReal_one] using h
  exact (mul_le_mul_of_nonneg_left hφ hα0).trans_lt (by simpa using hα1)

theorem total_above (D : DemandDist) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (G : ℤ → ℝ) (s S : ℤ) (hsS : s ≤ S) (x : ℤ) (hx : s ≤ x) :
    CInventory.total (CInventory.demandPMF D) α K G s S x =
      LAlpha D.φ α G x (x - s).toNat +
        (K + CInventory.total (CInventory.demandPMF D) α K G s S S) * rAlpha D.φ α (x - s).toNat := by
  let p := CInventory.demandPMF D
  let F := CInventory.total p α K G s S
  let B := K + F S
  let d := (x - s).toNat
  let H : ℕ → ℝ := fun j => F (x - (j : ℤ)) - B
  let c : ℕ → ℝ := fun j => G (x - (j : ℤ)) - (1 - α) * B
  have hφ0 := discount_zero_lt_one D α hα0 hα1
  have hrec : ∀ j ≤ d, H j = c j + α * ∑ k ∈ Finset.range (d - j + 1), D.φ k * H (j + k) := by
    intro j hj
    let y := x - (j : ℤ)
    have hy : s ≤ y := by dsimp [y, d] at *; omega
    have hbell : F y = G y + α * ∑' k : ℕ, D.φ k * F (y - (k : ℤ)) := by
      have h := CInventory.total_first p α K hα0 hα1 G s S y hsS
      simpa only [CInventory.pcost, VeinottWagnerSS.Selection.sSOrder, not_lt.mpr hy, if_false,
        sub_self, VeinottWagnerSS.Selection.delta, lt_self_iff_false, mul_zero, zero_add,
        p, ofReal_demand] using h
    have htail : ∀ k : ℕ, d - j < k → H (j + k) = 0 := by
      intro k hk
      have hz : x - ((j + k : ℕ) : ℤ) < s := by dsimp [d] at *; omega
      have h := CInventory.total_below p α K hα0 hα1 G s S hsS (x - ((j + k : ℕ) : ℤ)) hz
      dsimp [H, F, B]
      simpa only [Nat.cast_add] using sub_eq_zero.mpr h
    have hfinite : (∑' k : ℕ, D.φ k * H (j + k)) =
        ∑ k ∈ Finset.range (d - j + 1), D.φ k * H (j + k) := by
      apply tsum_eq_sum
      intro k hk
      rw [htail k (by simp only [Finset.mem_range, not_lt] at hk; omega)]
      ring
    have hfs : Summable (fun k : ℕ => D.φ k * F (y - (k : ℤ))) := by
      simpa only [p, ofReal_demand] using CInventory.weighted_total_summable p α K hα0 hα1 G s S y hsS
    have hsub : (∑' k : ℕ, D.φ k * H (j + k)) =
        (∑' k : ℕ, D.φ k * F (y - (k : ℤ))) - B := by
      have heq : ∀ k : ℕ, H (j + k) = F (y - (k : ℤ)) - B := by
        intro k
        dsimp [H, y]
        congr 2
        push_cast
        ring
      simp_rw [heq, mul_sub]
      rw [hfs.tsum_sub (D.hasSum.summable.mul_right B), tsum_mul_right, D.hasSum.tsum_eq, one_mul]
    calc
      H j = F y - B := rfl
      _ = G y - (1 - α) * B + α * ((∑' k : ℕ, D.φ k * F (y - (k : ℤ))) - B) := by
        rw [hbell]
        ring
      _ = _ := by rw [← hsub, hfinite]
  have hg := green_solution D α hα0 hφ0 c H d hrec
  simp only [H, Nat.cast_zero, sub_zero] at hg
  change F x - B = ∑' n : ℕ, α ^ n * ∑ j ∈ Finset.range (d + 1),
    convPow D.φ n j * (G (x - (j : ℤ)) - (1 - α) * B) at hg
  rw [shifted_cost_green D α hα0 hφ0 G x d ((1 - α) * B)] at hg
  change F x = LAlpha D.φ α G x d + B * rAlpha D.φ α d
  rw [CVeinottRenewal.rAlpha_closed_form D α hα0 hφ0 d]
  nlinarith [hg]

end CInventoryGreen
end
section

open VeinottWagnerSS.RenewalCost

namespace CInventoryGreen

theorem raw_above (D : DemandDist) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (G : ℤ → ℝ) (s S : ℤ) (hsS : s ≤ S) (x : ℤ) (hx : s ≤ x) :
    fCost D α K G s S x = LAlpha D.φ α G x (x - s).toNat +
      K * rAlpha D.φ α (x - s).toNat + fCost D α K G s S S * rAlpha D.φ α (x - s).toNat := by
  have h := total_above D α K hα0 hα1 G s S hsS x hx
  simpa only [CInventory.raw_total, add_mul, add_assoc] using h

theorem raw_below (D : DemandDist) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (G : ℤ → ℝ) (s S : ℤ) (hsS : s ≤ S) (x : ℤ) (hx : x < s) :
    fCost D α K G s S x = K + fCost D α K G s S S := by
  simpa only [CInventory.raw_total] using
    CInventory.total_below (CInventory.demandPMF D) α K hα0 hα1 G s S hsS x hx

theorem MAlpha_nonneg (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α) (d : ℕ) :
    0 ≤ MAlpha D.φ α d := by
  apply tsum_nonneg
  intro i
  apply mul_nonneg (pow_nonneg hα0 _)
  exact Finset.sum_nonneg (fun k _ => CVeinottRenewal.conv_nonneg D _ k)

theorem rAlpha_lt_one (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (d : ℕ) :
    rAlpha D.φ α d < 1 := by
  rw [CVeinottRenewal.rAlpha_closed_form D α hα0 (discount_zero_lt_one D α hα0 hα1) d]
  nlinarith [MAlpha_nonneg D α hα0 d]

theorem base_closed (D : DemandDist) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (G : ℤ → ℝ) (s S : ℤ) (hsS : s ≤ S) :
    K + fCost D α K G s S S =
      (LAlpha D.φ α G S (S - s).toNat + K) / (1 - rAlpha D.φ α (S - s).toNat) := by
  have h := raw_above D α K hα0 hα1 G s S hsS S hsS
  apply (eq_div_iff (by linarith [rAlpha_lt_one D α hα0 hα1 (S - s).toNat])).mpr
  nlinarith [h]

theorem cost_closed (D : DemandDist) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (G : ℤ → ℝ) (s S : ℤ) (hsS : s ≤ S) (x : ℤ) :
    fCost D α K G s S x =
      if x < s then
        (LAlpha D.φ α G S (S - s).toNat + K) / (1 - rAlpha D.φ α (S - s).toNat)
      else
        LAlpha D.φ α G x (x - s).toNat +
          (LAlpha D.φ α G S (S - s).toNat + K) / (1 - rAlpha D.φ α (S - s).toNat) *
            rAlpha D.φ α (x - s).toNat := by
  by_cases hx : x < s
  · rw [if_pos hx, raw_below D α K hα0 hα1 G s S hsS x hx,
      base_closed D α K hα0 hα1 G s S hsS]
  · rw [if_neg hx, raw_above D α K hα0 hα1 G s S hsS x (le_of_not_gt hx)]
    rw [← base_closed D α K hα0 hα1 G s S hsS]
    ring

theorem average_closed (D : DemandDist) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (G : ℤ → ℝ) (s S : ℤ) (hsS : s ≤ S) (x : ℤ) :
    aCost D α K G s S x =
      if x < s then
        (LAlpha D.φ α G S (S - s).toNat + K) / (1 + MAlpha D.φ α (S - s).toNat)
      else
        (1 - α) * LAlpha D.φ α G x (x - s).toNat +
          (LAlpha D.φ α G S (S - s).toNat + K) / (1 + MAlpha D.φ α (S - s).toNat) *
            rAlpha D.φ α (x - s).toNat := by
  have hscale : (1 - α) * ((LAlpha D.φ α G S (S - s).toNat + K) /
      (1 - rAlpha D.φ α (S - s).toNat)) =
      (LAlpha D.φ α G S (S - s).toNat + K) / (1 + MAlpha D.φ α (S - s).toNat) := by
    have hr := CVeinottRenewal.rAlpha_closed_form D α hα0 (discount_zero_lt_one D α hα0 hα1) (S - s).toNat
    have hden : 1 - rAlpha D.φ α (S - s).toNat = (1 - α) * (1 + MAlpha D.φ α (S - s).toNat) := by
      rw [hr]
      ring
    rw [hden]
    have ha : 1 - α ≠ 0 := by linarith
    have hM : 1 + MAlpha D.φ α (S - s).toNat ≠ 0 := by linarith [MAlpha_nonneg D α hα0 (S - s).toNat]
    field_simp
  unfold aCost
  rw [cost_closed D α K hα0 hα1 G s S hsS x]
  split_ifs with hx
  · exact hscale
  · rw [mul_add, ← mul_assoc, hscale]

end CInventoryGreen
end
open VeinottWagnerSS.RenewalCost

theorem solution (D : DemandDist) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hK : 0 ≤ K) (G : ℤ → ℝ) (s S : ℤ) (hsS : s ≤ S) :
    fCost D α K G s S S =
      LAlpha D.φ α G S (S - s).toNat + K * rAlpha D.φ α (S - s).toNat
        + fCost D α K G s S S * rAlpha D.φ α (S - s).toNat := by
  exact CInventoryGreen.raw_above D α K hα0 hα1 G s S hsS S hsS
