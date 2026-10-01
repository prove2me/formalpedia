-- Prove2me | solution 1 for VeinottWagnerSS.Selection.theorem1_aCost_eq_of_eq_below
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:03:48.033496+00:00
-- url     : https://prove2.me/submissions/d9622103-282d-4ae0-977b-de330fdc1068

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
    (s S s' S' : ℤ) (hsS : s ≤ S) (hsS' : s' ≤ S') (hss' : s ≤ s')
    (heq : ∀ x : ℤ, x < s' → aCost M α s S x = aCost M α s' S' x) :
    ∀ x : ℤ, aCost M α s S x = aCost M α s' S' x := by
  have heqT : ∀ x : ℤ, x < s' → CInventory.total M.φ α M.K M.G s S x =
      CInventory.total M.φ α M.K M.G s' S' x := by
    intro x hx
    rw [CInventory.selection_total, CInventory.selection_total]
    exact mul_left_cancel₀ (show 1 - α ≠ 0 by linarith) (heq x hx)
  have h := CInventory.total_eq_of_eq_below M.φ α M.K hα0 hα1 M.G s S s' S' hsS hsS' hss' heqT
  intro x
  unfold aCost
  rw [← CInventory.selection_total, ← CInventory.selection_total, h x]
