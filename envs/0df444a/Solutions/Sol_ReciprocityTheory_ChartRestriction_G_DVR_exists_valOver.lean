-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.exists_valOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:37:46.575206+00:00
-- url     : https://prove2.me/submissions/bab0422b-6fa8-4d6f-87c7-d57c97c38c5f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {ϖ : V} (hϖ : Irreducible ϖ) (F : Type) [Field F] [Algebra (FractionRing V) F]
    [Algebra.IsAlgebraic (FractionRing V) F] : ∃ v : AddValuation F (WithTop ℚ), ValOver ϖ F v := by
  classical
  let i : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V _)
  have ii : Function.Injective i := (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _)
  obtain ⟨A, hA, hl⟩ := IsLocalRing.exists_factor_valuationRing i
  let w := A.valuation
  have le : ∀ r, w (i r) ≤ 1 := fun r => (A.valuation_le_one_iff _).2 (hA r)
  have un : ∀ u : Vˣ, w (i u) = 1 := fun u => le_antisymm (le _) (by
    have := le (↑u⁻¹ : V)
    have e : w (i u) * w (i ↑u⁻¹) = 1 := by rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    calc 1 = w (i u) * w (i ↑u⁻¹) := e.symm
      _ ≤ w (i u) * 1 := mul_le_mul_right this _
      _ = _ := mul_one _)
  set p := w (i ϖ) with hp
  have p0 : 0 < p := zero_lt_iff.2 ((Valuation.ne_zero_iff w).2 fun h => hϖ.ne_zero (ii (h.trans (map_zero i).symm)))
  have p1 : p < 1 := lt_of_le_of_ne (le ϖ) fun h => hϖ.not_isUnit
    ((isUnit_map_iff (i.codRestrict A.toSubring hA) ϖ).1 ((A.valuation_eq_one_iff ⟨_, hA ϖ⟩).2 h))
  have hv : ∀ c n, HasVal ϖ c n → w (algebraMap _ F c) = p ^ n := by
    rintro _ n ⟨u, rfl⟩
    rw [map_mul, map_zpow₀, map_mul, map_zpow₀]
    exact (congrArg _ (un u)).trans (mul_one _)
  have ex : ∀ c : FractionRing V, c ≠ 0 → ∃ n : ℤ, w (algebraMap _ F c) = p ^ n := fun c hc => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) c
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (x := a) (by rintro rfl; simp at hc) hϖ
    obtain ⟨n, u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
    refine ⟨m - n, ?_⟩
    rw [map_div₀, map_div₀, zpow_sub₀ p0.ne', zpow_natCast, zpow_natCast]
    show w (i _) / w (i _) = _
    simp only [map_mul, map_pow, un, one_mul, ← hp]
  have rat : ∀ x : F, x ≠ 0 → ∃ (n : ℕ) (m : ℤ), 0 < n ∧ w x ^ n = p ^ m := fun x hx => by
    by_contra hc
    push Not at hc
    obtain ⟨f, hf, h0⟩ := Algebra.IsAlgebraic.isAlgebraic (R := FractionRing V) x
    let T := fun j => algebraMap _ F (f.coeff j) * x ^ j
    have wx : w x ≠ 0 := (Valuation.ne_zero_iff w).2 hx
    have ne : ∀ a ∈ f.support, ∀ b ∈ f.support, a < b → w (T a) ≠ w (T b) := fun a ha b hb hab h => by
      obtain ⟨r, hr⟩ := ex _ (Polynomial.mem_support_iff.1 ha)
      obtain ⟨s, hs⟩ := ex _ (Polynomial.mem_support_iff.1 hb)
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
      simp only [T, map_mul, map_pow, hr, hs] at h
      rw [add_assoc, pow_add, mul_comm (w x ^ a), ← mul_assoc] at h
      refine hc (d + 1) (r - s) d.succ_pos ?_
      rw [zpow_sub₀ p0.ne', mul_right_cancel₀ (pow_ne_zero a wx) h, mul_div_cancel_left₀ _ (zpow_ne_zero s p0.ne')]
    obtain ⟨j, hj, hm⟩ := f.support.exists_max_image (fun j => w (T j)) (Polynomial.support_nonempty.2 hf)
    have := w.map_sum_eq_of_lt hj fun a ha => lt_of_le_of_ne (hm a (Finset.mem_sdiff.1 ha).1) (by
      rcases lt_or_gt_of_ne (Finset.notMem_singleton.1 (Finset.mem_sdiff.1 ha).2) with h | h
      exacts [ne a (Finset.mem_sdiff.1 ha).1 j hj h, (ne j hj a (Finset.mem_sdiff.1 ha).1 h).symm])
    rw [show ∑ a ∈ f.support, T a = 0 by rw [← h0, Polynomial.aeval_def, Polynomial.eval₂_eq_sum]; rfl, map_zero] at this
    exact mul_ne_zero ((map_ne_zero _).2 (Polynomial.mem_support_iff.1 hj)) (pow_ne_zero j hx) ((Valuation.zero_iff w).1 this.symm)
  have cmp : ∀ {x y : F} {n n' : ℕ} {m m' : ℤ}, 0 < n → 0 < n' → w x ^ n = p ^ m → w y ^ n' = p ^ m' →
      (w x ≤ w y ↔ (m' : ℚ) / n' ≤ m / n) := fun {x y n n' m m'} hn hn' h h' => by
    rw [← pow_le_pow_iff_left₀ zero_le zero_le (Nat.mul_pos hn hn').ne', pow_mul, h, mul_comm n, pow_mul, h', ← zpow_natCast,
      ← zpow_natCast, ← zpow_mul, ← zpow_mul, zpow_le_zpow_iff_right_of_lt_one₀ p0 p1,
      div_le_div_iff₀ (by exact_mod_cast hn') (by exact_mod_cast hn)]
    exact_mod_cast Iff.rfl
  choose! N M hN hM using rat
  let v : F → WithTop ℚ := fun x => if x = 0 then ⊤ else ((M x : ℚ) / N x : ℚ)
  have spec : ∀ {x : F} {n : ℕ} {m : ℤ}, x ≠ 0 → 0 < n → w x ^ n = p ^ m → v x = ((m : ℚ) / (n : ℕ) : ℚ) := fun {x n m} hx hn h =>
    (if_neg hx).trans (congrArg _ (le_antisymm ((cmp hn (hN x hx) h (hM x hx)).1 le_rfl) ((cmp (hN x hx) hn (hM x hx) h).1 le_rfl)))
  have mono : ∀ x y, w x ≤ w y → v y ≤ v x := fun x y h => by
    by_cases hx : x = 0
    · simp [v, hx]
    · have hy : y ≠ 0 := by rintro rfl; exact hx ((Valuation.zero_iff w).1 (le_zero_iff.1 (h.trans_eq (map_zero w))))
      simp only [v, if_neg hx, if_neg hy, WithTop.coe_le_coe]
      exact (cmp (hN x hx) (hN y hy) (hM x hx) (hM y hy)).1 h
  refine ⟨AddValuation.of v (if_pos rfl) (by simpa using spec (n := 1) (m := 0) one_ne_zero one_pos (by simp)) (fun x y => ?_)
    fun x y => ?_, fun c n h => ?_⟩
  · rcases le_max_iff.1 (w.map_add x y) with h | h
    exacts [(min_le_left _ _).trans (mono _ _ h), (min_le_right _ _).trans (mono _ _ h)]
  · by_cases hx : x = 0
    · simp [v, hx]
    by_cases hy : y = 0
    · simp [v, hy]
    rw [spec (n := N x * N y) (m := M x * N y + M y * N x) (mul_ne_zero hx hy) (Nat.mul_pos (hN x hx) (hN y hy)) (by
      rw [map_mul, mul_pow, pow_mul, hM x hx, mul_comm (N x), pow_mul, hM y hy, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
        zpow_add₀ p0.ne'])]
    simp only [v, if_neg hx, if_neg hy, ← WithTop.coe_add, WithTop.coe_inj]
    have := (hN x hx).ne'
    have := (hN y hy).ne'
    push_cast
    field_simp
  · have e := hv c n h
    have := spec (n := 1) (m := n) ((Valuation.ne_zero_iff w).1 (e ▸ zpow_ne_zero n p0.ne')) one_pos ((pow_one _).trans e)
    simpa using this
end ReciprocityTheory.ChartRestriction.G.DVR
