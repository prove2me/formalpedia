-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P41.tilted_law_minimizes_KL_on_level
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:40:57.923356+00:00
-- url     : https://prove2.me/submissions/e35fc233-e303-47bc-8969-2db8b97d3f25

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P41
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P41
open scoped Matrix ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)

open QAlgorithms.Papers.Independent.Dependency50.P28
  (tr SupportLE relativeEntropy scalarPower classicalD typeI accept TestSequence
    scaled logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Claimed50.P15 (legendre)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type} [Fintype I] [DecidableEq I]

variable {X : Type} [Fintype X]



/-- PDF pp.8--9, Appendix, (23): every law on the tilt's q-divergence level has
at least the tilt's divergence to p. The comparison is between KL values; phat
is arbitrary and may have infinite divergence to p. No auxiliary t>=0 from the
source's proof is assumed. -/
theorem solution [Nonempty X]
    (p q : X → ℝ) (hp : IsLaw p) (hq : IsLaw q) (r s : ℝ)
    (hr : classicalD (.finite 1 (by norm_num)) p q < (r : EReal)) (hs : 0 < s)
    (hlevel : classicalD (.finite 1 (by norm_num)) (tilt p q s) q = (r : EReal))
    (phat : X → ℝ) (hphat : IsLaw phat)
    (heq : classicalD (.finite 1 (by norm_num)) phat q = classicalD (.finite 1 (by norm_num)) (tilt p q s) q) :
    classicalD (.finite 1 (by norm_num)) (tilt p q s) p ≤ classicalD (.finite 1 (by norm_num)) phat p := by
  classical
  have hD1 : ∀ a b : X → ℝ, classicalD (.finite 1 (by norm_num)) a b =
      if (∀ x, 0 < a x → 0 < b x) then
        ((∑ x, if 0 < a x then a x * Real.log (a x / b x) else 0 : ℝ) : EReal) else ⊤ := by
    intro a b; simp [classicalD]
  have hstrip : ∀ a b : X → ℝ, (∀ x, 0 ≤ a x) →
      (∑ x, if 0 < a x then a x * Real.log (a x / b x) else 0) =
        ∑ x, a x * Real.log (a x / b x) := by
    intro a b ha
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rfl
    · rw [le_antisymm (not_lt.mp h) (ha x)]; simp
  have hpq : ∀ x, 0 < p x → 0 < q x := by
    by_contra h
    rw [hD1, if_neg h] at hr
    exact not_top_lt hr
  set Z := ∑ x, scalarPower (p x) (1 + s) * scalarPower (q x) (-s) with hZdef
  have hsp0 : ∀ x t, 0 ≤ scalarPower x t := by
    intro x t; unfold scalarPower; split_ifs with h
    · exact Real.rpow_nonneg h.le _
    · exact le_refl _
  have hppos : ∃ x, 0 < p x := by
    by_contra h; push Not at h
    have : ∑ x, p x ≤ 0 := Finset.sum_nonpos fun x _ => h x
    linarith [hp.2]
  have hZ : 0 < Z := by
    obtain ⟨x0, hx0⟩ := hppos
    apply Finset.sum_pos' (fun x _ => mul_nonneg (hsp0 _ _) (hsp0 _ _))
    refine ⟨x0, Finset.mem_univ _, ?_⟩
    unfold scalarPower
    rw [if_pos hx0, if_pos (hpq x0 hx0)]
    exact mul_pos (Real.rpow_pos_of_pos hx0 _) (Real.rpow_pos_of_pos (hpq x0 hx0) _)
  have hpsi : classicalPsi p q s = Real.log Z := rfl
  set t := tilt p q s with htdef
  have hteq : ∀ x, t x = Z⁻¹ * (scalarPower (p x) (1 + s) * scalarPower (q x) (-s)) := by
    intro x
    rw [htdef]; unfold tilt
    rw [hpsi, Real.exp_neg, Real.exp_log hZ]; ring
  have ht0 : ∀ x, 0 ≤ t x := fun x => by
    rw [hteq]; exact mul_nonneg (inv_nonneg.mpr hZ.le) (mul_nonneg (hsp0 _ _) (hsp0 _ _))
  have htz : ∀ x, ¬ 0 < p x → t x = 0 := by
    intro x hx; rw [hteq]; unfold scalarPower; rw [if_neg hx]; simp
  have htpos : ∀ x, 0 < p x → 0 < t x ∧
      Real.log (t x) = -Real.log Z + (1 + s) * Real.log (p x) - s * Real.log (q x) := by
    intro x hx
    have hqx := hpq x hx
    have e : t x = Z⁻¹ * (p x ^ (1 + s) * q x ^ (-s)) := by
      rw [hteq]; unfold scalarPower; rw [if_pos hx, if_pos hqx]; rfl
    have h1 : 0 < p x ^ (1 + s) := Real.rpow_pos_of_pos hx _
    have h2 : 0 < q x ^ (-s) := Real.rpow_pos_of_pos hqx _
    refine ⟨by rw [e]; positivity, ?_⟩
    rw [e, Real.log_mul (inv_pos.mpr hZ).ne' (mul_pos h1 h2).ne', Real.log_mul h1.ne' h2.ne',
      Real.log_inv, Real.log_rpow hx, Real.log_rpow hqx]; ring
  have htp : ∀ x, 0 < t x → 0 < p x := by
    intro x hx; by_contra h; rw [htz x h] at hx; exact lt_irrefl _ hx
  have htsum : ∑ x, t x = 1 := by
    simp_rw [hteq]; rw [← Finset.mul_sum, ← hZdef]; field_simp
  by_cases hph : ∀ x, 0 < phat x → 0 < p x
  swap
  · rw [hD1 phat p, if_neg hph]; exact le_top
  have hphq : ∀ x, 0 < phat x → 0 < q x := fun x hx => hpq x (hph x hx)
  have htq : ∀ x, 0 < t x → 0 < q x := fun x hx => hpq x (htp x hx)
  rw [hD1 t q, if_pos htq, hD1 phat q, if_pos hphq] at heq
  rw [hD1 t p, if_pos htp, hD1 phat p, if_pos hph, EReal.coe_le_coe_iff]
  have heq' := EReal.coe_injective heq
  rw [hstrip _ _ hphat.1, hstrip _ _ ht0] at heq'
  rw [hstrip _ _ hphat.1, hstrip _ _ ht0]
  -- per-x identities
  have E1 : ∀ x, phat x * Real.log (phat x / t x) =
      (1 + s) * (phat x * Real.log (phat x / p x)) - s * (phat x * Real.log (phat x / q x)) +
        Real.log Z * phat x := by
    intro x
    rcases eq_or_lt_of_le (hphat.1 x) with h | h
    · rw [← h]; simp
    · have hpx := hph x h
      obtain ⟨htx, hlt⟩ := htpos x hpx
      rw [Real.log_div h.ne' htx.ne', Real.log_div h.ne' hpx.ne',
        Real.log_div h.ne' (hpq x hpx).ne', hlt]; ring
  have E2 : ∀ x, (1 + s) * (t x * Real.log (t x / p x)) =
      s * (t x * Real.log (t x / q x)) - Real.log Z * t x := by
    intro x
    by_cases hpx : 0 < p x
    · obtain ⟨htx, hlt⟩ := htpos x hpx
      rw [Real.log_div htx.ne' hpx.ne', Real.log_div htx.ne' (hpq x hpx).ne', hlt]; ring
    · rw [htz x hpx]; simp
  have G : ∀ x, phat x - t x ≤ phat x * Real.log (phat x / t x) := by
    intro x
    rcases eq_or_lt_of_le (hphat.1 x) with h | h
    · rw [← h]; simp [ht0 x]
    · have htx := (htpos x (hph x h)).1
      have hl := Real.log_le_sub_one_of_pos (div_pos htx h)
      have e : Real.log (phat x / t x) = -Real.log (t x / phat x) := by
        rw [← Real.log_inv, inv_div]
      rw [e]
      have : phat x * (t x / phat x - 1) = t x - phat x := by field_simp
      nlinarith
  have SG : ∑ x, (phat x - t x) ≤ ∑ x, phat x * Real.log (phat x / t x) :=
    Finset.sum_le_sum fun x _ => G x
  rw [Finset.sum_sub_distrib, hphat.2, htsum, sub_self] at SG
  rw [Finset.sum_congr rfl (fun x _ => E1 x), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hphat.2] at SG
  have S2 := Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => E2 x)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, htsum] at S2
  have hs1 : 0 < 1 + s := by linarith
  nlinarith



end
