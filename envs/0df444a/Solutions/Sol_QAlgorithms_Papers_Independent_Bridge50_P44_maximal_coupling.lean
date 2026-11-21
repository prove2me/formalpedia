-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P44.maximal_coupling
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T16:15:55.855584+00:00
-- url     : https://prove2.me/submissions/5c41e1f2-41d4-4db5-a599-ed9191154f59

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44

section
set_option autoImplicit false

namespace QAlgorithms.Papers.Independent.Bridge50.P44

theorem chk_maximal_coupling {Z : Type*} (p q : Z → ℝ)
    (hp : IsDiscreteLaw p) (hq : IsDiscreteLaw q) :
    ∃ j : Z × Z → ℝ, IsCoupling p q j ∧
      1 - discreteTV p q ≤ ∑' z, j (z,z) := by
  classical
  obtain ⟨hp0, hps, hp1⟩ := hp
  obtain ⟨hq0, hqs, hq1⟩ := hq
  set m : Z → ℝ := fun z => min (p z) (q z) with hm
  set a : Z → ℝ := fun z => p z - m z with ha
  set b : Z → ℝ := fun z => q z - m z with hb
  have hm0 : ∀ z, 0 ≤ m z := fun z => le_min (hp0 z) (hq0 z)
  have ha0 : ∀ z, 0 ≤ a z := fun z => sub_nonneg.2 (min_le_left _ _)
  have hb0 : ∀ z, 0 ≤ b z := fun z => sub_nonneg.2 (min_le_right _ _)
  have hms : Summable m :=
    Summable.of_nonneg_of_le hm0 (fun z => min_le_left _ _) hps
  have has : Summable a := hps.sub hms
  have hbs : Summable b := hqs.sub hms
  set s := ∑' z, m z with hs
  set t := ∑' z, a z with ht
  have htb : ∑' z, b z = t := by
    simp only [ha, hb, ht]
    rw [hqs.tsum_sub hms, hps.tsum_sub hms, hp1, hq1]
  have hts : t = 1 - s := by
    simp only [ht, ha]; rw [hps.tsum_sub hms, hp1]
  have hTV : discreteTV p q = t := by
    unfold discreteTV
    have : ∀ z, |p z - q z| = a z + b z := by
      intro z
      simp only [ha, hb, hm]
      rcases le_total (p z) (q z) with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
    simp only [this]
    rw [has.tsum_add hbs, htb]; ring
  have hzero : t = 0 → ∀ z, a z = 0 := by
    intro h z
    have := (hasSum_zero_iff_of_nonneg ha0).1 (by rw [← h]; exact has.hasSum)
    exact congrFun this z
  have hzero' : t = 0 → ∀ z, b z = 0 := by
    intro h z
    have := (hasSum_zero_iff_of_nonneg hb0).1 ((htb.trans h) ▸ hbs.hasSum)
    exact congrFun this z
  let j : Z × Z → ℝ := fun x => (if x.2 = x.1 then m x.1 else 0) + a x.1 * b x.2 / t
  have ht0 : 0 ≤ t := tsum_nonneg ha0
  have hj0 : ∀ x, 0 ≤ j x := fun x => by
    have h1 : 0 ≤ (if x.2 = x.1 then m x.1 else 0) := by split_ifs <;> simp [hm0]
    have h2 : 0 ≤ a x.1 * b x.2 / t := div_nonneg (mul_nonneg (ha0 _) (hb0 _)) ht0
    exact add_nonneg h1 h2
  let D : Z × Z → ℝ := fun x => if x.2 = x.1 then m x.1 else 0
  let g : Z → Z × Z := fun z => (z, z)
  have hg : Function.Injective g := fun x y h => (Prod.mk.inj h).1
  have hDs : Summable D := by
    rw [← hg.summable_iff (f := D)]
    · have e : (D ∘ g) = m := by funext z; simp [D, g]
      rw [e]; exact hms
    · intro x hx
      have : x.2 ≠ x.1 := fun h => hx ⟨x.1, by ext <;> simp [g, h]⟩
      simp [D, this]
  have hPs : Summable (fun x : Z × Z => a x.1 * b x.2 / t) :=
    (Summable.mul_of_nonneg has hbs (fun z => ha0 z) (fun z => hb0 z)).div_const t
  have hjs : Summable j := hDs.add hPs
  have hrow : ∀ z, ∑' w, j (z, w) = p z := by
    intro z
    have e1 : ∑' w, D (z, w) = m z := by
      rw [tsum_eq_single z]
      · simp [D]
      · intro w hw; simp [D, hw]
    have e2 : ∑' w, a z * b w / t = a z := by
      by_cases h : t = 0
      · simp [hzero h z, h]
      · rw [show (fun w => a z * b w / t) = fun w => (a z / t) * b w by
          funext w; ring, tsum_mul_left, htb]; exact div_mul_cancel₀ _ h
    have hsw : Summable (fun w => D (z, w)) := hDs.comp_injective (fun x y h => (Prod.mk.inj h).2)
    have hsw2 : Summable (fun w => a z * b w / t) := (hbs.mul_left (a z)).div_const t
    show ∑' w, (D (z, w) + a z * b w / t) = p z
    rw [hsw.tsum_add hsw2, e1, e2]; simp [ha]
  have hcol : ∀ w, ∑' z, j (z, w) = q w := by
    intro w
    have e1 : ∑' z, D (z, w) = m w := by
      rw [tsum_eq_single w]
      · simp [D]
      · intro z hz; simp [D, Ne.symm hz]
    have e2 : ∑' z, a z * b w / t = b w := by
      by_cases h : t = 0
      · simp [hzero' h w, h]
      · rw [show (fun z => a z * b w / t) = fun z => (b w / t) * a z by
          funext z; ring, tsum_mul_left]; exact div_mul_cancel₀ _ h
    have hsw : Summable (fun z => D (z, w)) := hDs.comp_injective (fun x y h => (Prod.mk.inj h).1)
    have hsw2 : Summable (fun z => a z * b w / t) := (has.mul_right (b w)).div_const t
    show ∑' z, (D (z, w) + a z * b w / t) = q w
    rw [hsw.tsum_add hsw2, e1, e2]; simp [hb]
  refine ⟨j, ⟨⟨hj0, hjs, ?_⟩, hrow, hcol⟩, ?_⟩
  · rw [hjs.tsum_prod, ]
    simp only [hrow]
    exact hp1
  · rw [hTV, hts]
    have hjd : Summable (fun z => j (z, z)) := hjs.comp_injective hg
    calc 1 - (1 - s) = s := by ring
      _ ≤ ∑' z, j (z, z) := by
        refine Summable.tsum_le_tsum (fun z => ?_) hms hjd
        have := hj0 (z, z)
        show m z ≤ (if z = z then m z else 0) + a z * b z / t
        have h2 : 0 ≤ a z * b z / t := div_nonneg (mul_nonneg (ha0 _) (hb0 _)) ht0
        simp only [if_true]; linarith

end QAlgorithms.Papers.Independent.Bridge50.P44
end

theorem solution : type_of% @QAlgorithms.Papers.Independent.Bridge50.P44.chk_maximal_coupling := @QAlgorithms.Papers.Independent.Bridge50.P44.chk_maximal_coupling
