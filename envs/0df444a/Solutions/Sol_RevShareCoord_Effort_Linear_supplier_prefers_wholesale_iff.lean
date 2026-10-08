-- Prove2me | solution 1 for RevShareCoord.Effort.Linear.supplier_prefers_wholesale_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:38:38.689654+00:00
-- url     : https://prove2.me/submissions/938bc483-a94d-46d6-b4c3-817b23c950f2

import Mathlib
import Definitions.Def_RevShareCoord_Effort_Linear

set_option autoImplicit false

namespace RevShareCoord.Effort.Linear

lemma p29f23a4a_profit_identity (τ φ w q e Q : ℝ) :
    retailerProfit τ φ w q e =
      retailerProfit τ φ w Q (effort τ φ Q) - (φ - φ ^ 2 * τ ^ 2) * (q - Q) ^ 2
        - (e - φ * τ * q) ^ 2 + (q - Q) * (φ - w - 2 * (φ - φ ^ 2 * τ ^ 2) * Q) := by
  unfold retailerProfit revenue price effort
  ring

lemma p29f23a4a_a_pos (τ φ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < φ - φ ^ 2 * τ ^ 2 := by
  have h1 : τ ^ 2 < 1 := by nlinarith
  have h2 : φ * τ ^ 2 < 1 := by nlinarith
  nlinarith

lemma p29f23a4a_residual_nonpos (τ φ w q : ℝ) (ha : 0 < φ - φ ^ 2 * τ ^ 2) (hq : 0 ≤ q) :
    (q - orderQty τ φ w) * (φ - w - 2 * (φ - φ ^ 2 * τ ^ 2) * orderQty τ φ w) ≤ 0 := by
  unfold orderQty
  split_ifs with h
  · have : φ - w - 2 * (φ - φ ^ 2 * τ ^ 2) * ((φ - w) / (2 * (φ - φ ^ 2 * τ ^ 2))) = 0 := by
      generalize φ - φ ^ 2 * τ ^ 2 = a at ha ⊢
      have hne : a ≠ 0 := ha.ne'
      field_simp
      ring
    rw [this, mul_zero]
  · push Not at h
    nlinarith

lemma p29f23a4a_orderQty_nonneg (τ φ w : ℝ) (ha : 0 < φ - φ ^ 2 * τ ^ 2) :
    0 ≤ orderQty τ φ w := by
  unfold orderQty
  split_ifs with h
  · apply div_nonneg <;> linarith
  · exact le_refl 0

lemma p29f23a4a_main_ineq (τ φ w q e : ℝ) (ha : 0 < φ - φ ^ 2 * τ ^ 2) (hq : 0 ≤ q) :
    retailerProfit τ φ w q e ≤
      retailerProfit τ φ w (orderQty τ φ w) (effort τ φ (orderQty τ φ w))
        - (φ - φ ^ 2 * τ ^ 2) * (q - orderQty τ φ w) ^ 2 - (e - φ * τ * q) ^ 2 := by
  rw [p29f23a4a_profit_identity τ φ w q e (orderQty τ φ w)]
  have := p29f23a4a_residual_nonpos τ φ w q ha hq
  linarith

lemma p29f23a4a_resp_iff (τ φ w : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) (x : ℝ × ℝ) :
    IsRetailerResponse τ φ w x ↔ x = (orderQty τ φ w, effort τ φ (orderQty τ φ w)) := by
  have ha := p29f23a4a_a_pos τ φ hτ0 hτ1 hφ0 hφ1
  have hQ := p29f23a4a_orderQty_nonneg τ φ w ha
  have hmem : (orderQty τ φ w, effort τ φ (orderQty τ φ w)) ∈ quadrant := by
    refine ⟨Set.mem_Ici.mpr hQ, Set.mem_Ici.mpr ?_⟩
    unfold effort
    have : 0 ≤ φ * τ := mul_nonneg hφ0.le hτ0
    exact mul_nonneg this hQ
  constructor
  · rintro ⟨hx, hmax⟩
    have h1 := hmax hmem
    simp only [Set.mem_ofPred_eq] at h1
    have hq : 0 ≤ x.1 := hx.1
    have h2 := p29f23a4a_main_ineq τ φ w x.1 x.2 ha hq
    have hsq1 : 0 ≤ (φ - φ ^ 2 * τ ^ 2) * (x.1 - orderQty τ φ w) ^ 2 :=
      mul_nonneg ha.le (sq_nonneg _)
    have hsq2 : 0 ≤ (x.2 - φ * τ * x.1) ^ 2 := sq_nonneg _
    have e1 : (φ - φ ^ 2 * τ ^ 2) * (x.1 - orderQty τ φ w) ^ 2 = 0 := by linarith
    have e2 : (x.2 - φ * τ * x.1) ^ 2 = 0 := by linarith
    have q_eq : x.1 = orderQty τ φ w := by
      rcases mul_eq_zero.mp e1 with h | h
      · linarith
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
        linarith
    have e_eq : x.2 = φ * τ * x.1 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e2
      linarith
    ext
    · exact q_eq
    · simp only [effort]
      rw [e_eq, q_eq]
  · rintro rfl
    refine ⟨hmem, ?_⟩
    intro y hy
    simp only [Set.mem_ofPred_eq]
    have hq : 0 ≤ y.1 := hy.1
    have h2 := p29f23a4a_main_ineq τ φ w y.1 y.2 ha hq
    have hsq1 : 0 ≤ (φ - φ ^ 2 * τ ^ 2) * (y.1 - orderQty τ φ w) ^ 2 :=
      mul_nonneg ha.le (sq_nonneg _)
    have hsq2 : 0 ≤ (y.2 - φ * τ * y.1) ^ 2 := sq_nonneg _
    linarith

lemma p29f23a4a_f_eq (τ c φ w : ℝ) (hD : (2 * (φ - φ ^ 2 * τ ^ 2)) ≠ 0) (hw : w ≤ φ) :
    supplierProfitAt τ c φ w =
      (1 - c) * ((φ - w) / (2 * (φ - φ ^ 2 * τ ^ 2)))
        - (1 + φ * (1 - 2 * τ ^ 2)) * ((φ - w) / (2 * (φ - φ ^ 2 * τ ^ 2))) ^ 2 := by
  unfold supplierProfitAt supplierProfit orderQty revenue price effort
  rcases lt_or_eq_of_le hw with h | h
  · rw [if_pos h]
    set q := (φ - w) / (2 * (φ - φ ^ 2 * τ ^ 2)) with hq
    have hw' : w = φ - 2 * (φ - φ ^ 2 * τ ^ 2) * q := by
      rw [hq]
      generalize 2 * (φ - φ ^ 2 * τ ^ 2) = D at hD ⊢
      field_simp
      ring
    clear_value q
    subst hw'
    ring
  · subst h
    simp

lemma p29f23a4a_f_ge (τ c φ w : ℝ) (hw : φ ≤ w) : supplierProfitAt τ c φ w = 0 := by
  unfold supplierProfitAt supplierProfit orderQty revenue price effort
  rw [if_neg (not_lt.mpr hw)]
  ring

lemma p29f23a4a_bound (τ c φ w : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hc1 : c < 1) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) :
    supplierProfitAt τ c φ w ≤ (1 - c) ^ 2 / (4 * (1 + φ * (1 - 2 * τ ^ 2))) := by
  have hτ2 : τ ^ 2 < 1 := by nlinarith
  have hDraw : 0 < 2 * (φ - φ ^ 2 * τ ^ 2) := by
    have := p29f23a4a_a_pos τ φ hτ0 hτ1 hφ0 hφ1; linarith
  have hK : 0 < 1 + φ * (1 - 2 * τ ^ 2) := by nlinarith
  rcases le_or_gt w φ with h | h
  · rw [p29f23a4a_f_eq τ c φ _ hDraw.ne' h]
    generalize (φ - w) / (2 * (φ - φ ^ 2 * τ ^ 2)) = q
    generalize 1 + φ * (1 - 2 * τ ^ 2) = K at hK ⊢
    rw [le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg (2 * K * q - (1 - c))]
  · rw [p29f23a4a_f_ge τ c φ w h.le]
    exact div_nonneg (sq_nonneg _) (by linarith)

lemma p29f23a4a_value_at (τ c φ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hc0 : 0 < c) (hc1 : c < 1) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) :
    supplierProfitAt τ c φ (wholesalePrice τ c φ) =
      (1 - c) ^ 2 / (4 * (1 + φ * (1 - 2 * τ ^ 2))) := by
  have hτ2 : τ ^ 2 < 1 := by nlinarith
  have hD : 0 < 1 + φ * (1 - 2 * τ ^ 2) := by nlinarith
  have hA : 0 < 1 - φ * τ ^ 2 := by nlinarith
  have hDne := hD.ne'
  have hφw : φ - wholesalePrice τ c φ =
      φ * (1 - c) * (1 - φ * τ ^ 2) / (1 + φ * (1 - 2 * τ ^ 2)) := by
    unfold wholesalePrice; rw [eq_div_iff hDne, sub_mul, div_mul_cancel₀ _ hDne]; ring
  have hlt : wholesalePrice τ c φ < φ := by
    have : 0 < φ - wholesalePrice τ c φ := by
      rw [hφw]; apply div_pos _ hD; apply mul_pos (mul_pos hφ0 (by linarith)) hA
    linarith
  have hq : orderQty τ φ (wholesalePrice τ c φ) =
      (1 - c) / (2 * (1 + φ * (1 - 2 * τ ^ 2))) := by
    unfold orderQty; rw [if_pos hlt, hφw]
    have : φ - φ ^ 2 * τ ^ 2 = φ * (1 - φ * τ ^ 2) := by ring
    rw [this]; field_simp
  unfold supplierProfitAt supplierProfit revenue price effort
  rw [hq]; unfold wholesalePrice
  field_simp; ring

lemma p29f23a4a_wp_nonneg (τ c φ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hc0 : 0 < c) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) : 0 ≤ wholesalePrice τ c φ := by
  have hτ2 : τ ^ 2 < 1 := by nlinarith
  have hA : 0 < 1 - φ * τ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hφ1 (sq_nonneg τ)]
  have hKraw : 0 < 1 + φ * (1 - 2 * τ ^ 2) := by nlinarith
  unfold wholesalePrice
  apply div_nonneg
  · apply mul_nonneg hφ0.le
    have h1 := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - τ ^ 2) hφ0.le
    nlinarith [mul_pos hc0 hA]
  · exact hKraw.le

end RevShareCoord.Effort.Linear

open RevShareCoord.Effort.Linear in
theorem solution (τ c : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hc0 : 0 < c) (hc1 : c < 1) :
    (∀ φ ∈ Set.Ioc (0 : ℝ) 1,
      IsGreatest (supplierOutcomes τ c φ) ((1 - c) ^ 2 / (4 * (1 + φ * (1 - 2 * τ ^ 2)))) ∧
      supplierValue τ c φ = (1 - c) ^ 2 / (4 * (1 + φ * (1 - 2 * τ ^ 2))) ∧
      0 ≤ wholesalePrice τ c φ ∧
      (∃ x : ℝ × ℝ, IsRetailerResponse τ φ (wholesalePrice τ c φ) x) ∧
      (∀ x : ℝ × ℝ, IsRetailerResponse τ φ (wholesalePrice τ c φ) x →
        supplierProfit τ c φ (wholesalePrice τ c φ) x.1 x.2 = supplierValue τ c φ)) ∧
    (1 / Real.sqrt 2 < τ →
      StrictMonoOn (supplierValue τ c) (Set.Ioc 0 1) ∧
      ∀ φ ∈ Set.Ioo (0 : ℝ) 1, supplierValue τ c φ < supplierValue τ c 1) ∧
    (τ = 1 / Real.sqrt 2 → ∀ φ ∈ Set.Ioc (0 : ℝ) 1, supplierValue τ c φ = (1 - c) ^ 2 / 4) ∧
    (τ < 1 / Real.sqrt 2 →
      StrictAntiOn (supplierValue τ c) (Set.Ioc 0 1) ∧
      Filter.Tendsto (supplierValue τ c) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((1 - c) ^ 2 / 4))) := by
  have hτ2 : τ ^ 2 < 1 := by nlinarith
  have hc : 0 < 1 - c := by linarith
  have hKpos : ∀ φ ∈ Set.Ioc (0 : ℝ) 1, 0 < 1 + φ * (1 - 2 * τ ^ 2) := by
    rintro φ ⟨h0, h1⟩; nlinarith
  have key : ∀ φ ∈ Set.Ioc (0 : ℝ) 1,
      IsGreatest (supplierOutcomes τ c φ) ((1 - c) ^ 2 / (4 * (1 + φ * (1 - 2 * τ ^ 2)))) ∧
      supplierValue τ c φ = (1 - c) ^ 2 / (4 * (1 + φ * (1 - 2 * τ ^ 2))) ∧
      0 ≤ wholesalePrice τ c φ ∧
      (∃ x : ℝ × ℝ, IsRetailerResponse τ φ (wholesalePrice τ c φ) x) ∧
      (∀ x : ℝ × ℝ, IsRetailerResponse τ φ (wholesalePrice τ c φ) x →
        supplierProfit τ c φ (wholesalePrice τ c φ) x.1 x.2 = supplierValue τ c φ) := by
    rintro φ ⟨hφ0, hφ1⟩
    have hresp := fun w x => p29f23a4a_resp_iff τ φ w hτ0 hτ1 hφ0 hφ1 x
    have hW0 := p29f23a4a_wp_nonneg τ c φ hτ0 hτ1 hc0 hφ0 hφ1
    have hval := p29f23a4a_value_at τ c φ hτ0 hτ1 hc0 hc1 hφ0 hφ1
    have hG : IsGreatest (supplierOutcomes τ c φ)
        ((1 - c) ^ 2 / (4 * (1 + φ * (1 - 2 * τ ^ 2)))) := by
      refine ⟨⟨wholesalePrice τ c φ, hW0, _, (hresp _ _).mpr rfl, ?_⟩, ?_⟩
      · rw [← hval]; rfl
      · rintro s ⟨w, _, x, hx, rfl⟩
        rw [(hresp w x).mp hx]
        exact p29f23a4a_bound τ c φ w hτ0 hτ1 hc1 hφ0 hφ1
    have hV : supplierValue τ c φ = (1 - c) ^ 2 / (4 * (1 + φ * (1 - 2 * τ ^ 2))) :=
      hG.csSup_eq
    refine ⟨hG, hV, hW0, ⟨_, (hresp _ _).mpr rfl⟩, ?_⟩
    intro x hx
    rw [(hresp _ x).mp hx, hV, ← hval]
    rfl
  have hV' : ∀ φ ∈ Set.Ioc (0 : ℝ) 1,
      supplierValue τ c φ = (1 - c) ^ 2 / (4 * (1 + φ * (1 - 2 * τ ^ 2))) :=
    fun φ hφ => (key φ hφ).2.1
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (τ * Real.sqrt 2) ^ 2 = 2 * τ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; ring
  have hc2 : 0 < (1 - c) ^ 2 := pow_pos hc 2
  refine ⟨key, ?_, ?_, ?_⟩
  · intro hgt
    have h1 : 1 < τ * Real.sqrt 2 := (div_lt_iff₀ hs2).mp hgt
    have hT : 1 < 2 * τ ^ 2 := by nlinarith
    have hmono : StrictMonoOn (supplierValue τ c) (Set.Ioc 0 1) := by
      intro a ha b hb hab
      rw [hV' a ha, hV' b hb]
      have hKa := hKpos a ha
      have hKb := hKpos b hb
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      have : b * (1 - 2 * τ ^ 2) < a * (1 - 2 * τ ^ 2) := by nlinarith
      nlinarith
    refine ⟨hmono, ?_⟩
    rintro φ ⟨h0, h1⟩
    exact hmono ⟨h0, h1.le⟩ ⟨one_pos, le_refl 1⟩ h1
  · intro heq φ hφ
    have h1 : τ * Real.sqrt 2 = 1 := by
      rw [heq]; field_simp
    have hT : 2 * τ ^ 2 = 1 := by rw [← hsq, h1]; norm_num
    rw [hV' φ hφ]
    have : 1 - 2 * τ ^ 2 = 0 := by linarith
    rw [this]; ring
  · intro hlt
    have h1 : τ * Real.sqrt 2 < 1 := (lt_div_iff₀ hs2).mp hlt
    have h0 : 0 ≤ τ * Real.sqrt 2 := mul_nonneg hτ0 hs2.le
    have hT : 2 * τ ^ 2 < 1 := by nlinarith
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      rw [hV' a ha, hV' b hb]
      have hKa := hKpos a ha
      have hKb := hKpos b hb
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      have : a * (1 - 2 * τ ^ 2) < b * (1 - 2 * τ ^ 2) := by nlinarith
      nlinarith
    · have hev : (fun φ : ℝ => (1 - c) ^ 2 / (4 * (1 + φ * (1 - 2 * τ ^ 2))))
          =ᶠ[nhdsWithin 0 (Set.Ioi 0)] supplierValue τ c := by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with φ hφ
        exact (hV' φ ⟨hφ.1, hφ.2.le⟩).symm
      refine Filter.Tendsto.congr' hev ?_
      have hcont : Filter.Tendsto (fun φ : ℝ => 4 * (1 + φ * (1 - 2 * τ ^ 2))) (nhds 0)
          (nhds (4 * (1 + 0 * (1 - 2 * τ ^ 2)))) := by
        apply Continuous.tendsto; fun_prop
      have h2 := (tendsto_const_nhds (x := (1 - c) ^ 2)).div hcont (by norm_num)
      have h3 := h2.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      have h4 : (1 - c) ^ 2 / (4 * (1 + 0 * (1 - 2 * τ ^ 2))) = (1 - c) ^ 2 / 4 := by ring
      rw [h4] at h3
      exact h3
