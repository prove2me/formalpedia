-- Prove2me | solution 1 for SupplyFlex.SupplierLed.theorem_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T05:39:10.8495+00:00
-- url     : https://prove2.me/submissions/e7334028-ad0d-4720-a764-80a1933aef75
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_LogConcaveOn
import Definitions.Def_SupplyFlex_SupplierLed_Setting
import Theorems.Thm_SupplyFlex_SupplierLed_theorem_2
import Theorems.Thm_SupplyFlex_SupplierLed_theorem_3
import Theorems.Thm_SupplyFlex_SupplierLed_theorem_3_tie
import Theorems.Thm_SupplyFlex_SupplierLed_eq_A1_16_paren
import Theorems.Thm_SupplyFlex_SupplierLed_eq_A1_18
import Theorems.Thm_SupplyFlex_SupplierLed_root_G_exists
import Theorems.Thm_SupplyFlex_SupplierLed_root_qc_exists
import Theorems.Thm_SupplyFlex_SupplierLed_qo_lt_qc

open MeasureTheory SupplyFlex.SupplierLed

namespace T6Aux


lemma f_nonneg (M : Model) (hM : M.Std) (x : ℝ) : 0 ≤ M.f x := by
  by_cases h : x ∈ supp M.abar
  · exact (hM.f_pos x h).le
  · rw [hM.f_zero x h]

lemma f_neg (M : Model) (hM : M.Std) (x : ℝ) (hx : x < 0) : M.f x = 0 :=
  hM.f_zero x (fun h => by linarith [h.1])

/-- Integrals against the demand law are integrals against `f`. -/
lemma integral_demandLaw (M : Model) (hM : M.Std) (g : ℝ → ℝ) :
    ∫ d, g d ∂(demandLaw M.f) = ∫ d, M.f d * g d := by
  unfold demandLaw
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (M.f x))
    hM.f_meas.ennreal_ofReal (Filter.Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top))]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun d => ?_))
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (f_nonneg M hM d)]

lemma integrable_fmin (M : Model) (hM : M.Std) (z : ℝ) :
    Integrable (fun d => M.f d * min z d) := by
  have hb : Integrable (fun d => |z| * M.f d + |d * M.f d|) :=
    (hM.f_int.1.const_mul _).add hM.mean_fin.abs
  refine hb.mono' ?_ (Filter.Eventually.of_forall (fun d => ?_))
  · exact (hM.f_meas.mul (measurable_const.min measurable_id)).aestronglyMeasurable
  · have h0 := f_nonneg M hM d
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, abs_mul, abs_of_nonneg h0]
    have : |min z d| ≤ |z| + |d| := by
      rcases le_total z d with h | h
      · rw [min_eq_left h]; linarith [abs_nonneg d]
      · rw [min_eq_right h]; linarith [abs_nonneg z]
    nlinarith

/-- `S(z) = ∫₀^z x f + z F̄(z)`. -/
lemma expSales_eq (M : Model) (hM : M.Std) (z : ℝ) (hz : 0 ≤ z) :
    SupplyChainTheory.expSales (demandLaw M.f) z =
      (∫ x in Set.Ioc 0 z, x * M.f x) + z * Fbar M.f z := by
  unfold SupplyChainTheory.expSales
  rw [integral_demandLaw M hM]
  have hi := integrable_fmin M hM z
  rw [← integral_add_compl (s := Set.Ioi (0:ℝ)) measurableSet_Ioi hi]
  have hcompl : ∫ x in (Set.Ioi (0:ℝ))ᶜ, M.f x * min z x = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Ioi, not_lt] at hx
    rcases hx.lt_or_eq with h | h
    · rw [f_neg M hM x h, zero_mul]
    · rw [h, min_eq_right hz, mul_zero]
  rw [hcompl, add_zero, ← Set.Ioc_union_Ioi_eq_Ioi hz,
    setIntegral_union (Set.Ioc_disjoint_Ioi (a := (0:ℝ)) (le_refl z)) (measurableSet_Ioi (a := z)) hi.integrableOn
      hi.integrableOn]
  have h1 : ∫ x in Set.Ioc 0 z, M.f x * min z x = ∫ x in Set.Ioc 0 z, x * M.f x := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    rw [min_eq_right hx.2, mul_comm]
  have h2 : ∫ x in Set.Ioi z, M.f x * min z x = z * Fbar M.f z := by
    unfold Fbar
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [min_eq_left (le_of_lt hx), mul_comm]
  rw [h1, h2]

lemma T_nonneg (M : Model) (hM : M.Std) (z : ℝ) : 0 ≤ ∫ x in Set.Ioc 0 z, x * M.f x :=
  setIntegral_nonneg measurableSet_Ioc (fun x hx => mul_nonneg hx.1.le (f_nonneg M hM x))

lemma T_mono (M : Model) (hM : M.Std) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Set.Ioc 0 a, x * M.f x ≤ ∫ x in Set.Ioc 0 b, x * M.f x := by
  refine setIntegral_mono_set hM.mean_fin.integrableOn ?_
    (Filter.Eventually.of_forall (Set.Ioc_subset_Ioc_right hab))
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall (fun x hx => ?_))
  exact mul_nonneg hx.1.le (f_nonneg M hM x)

lemma T_zero (M : Model) : ∫ x in Set.Ioc 0 (0:ℝ), x * M.f x = 0 := by simp

lemma buyerExPost_eq (M : Model) (hM : M.Std) (w z : ℝ) (hz : 0 ≤ z) :
    buyerExPost M w z = M.r * ((∫ x in Set.Ioc 0 z, x * M.f x) + z * Fbar M.f z) - w * z := by
  unfold buyerExPost; rw [expSales_eq M hM z hz]

lemma Fbar_le_one (M : Model) (hM : M.Std) (x : ℝ) : Fbar M.f x ≤ 1 := by
  unfold Fbar
  rw [← hM.f_int.2]
  exact setIntegral_le_integral hM.f_int.1 (Filter.Eventually.of_forall (f_nonneg M hM))

lemma Fbar_zero (M : Model) (hM : M.Std) : Fbar M.f 0 = 1 := by
  unfold Fbar
  rw [← hM.f_int.2, ← integral_add_compl (s := Set.Ioi (0:ℝ)) measurableSet_Ioi hM.f_int.1]
  have : ∫ x in (Set.Ioi (0:ℝ))ᶜ, M.f x = 0 := by
    rw [Set.compl_Ioi]
    rw [integral_Iic_eq_integral_Iio]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    exact f_neg M hM x hx
  rw [this, add_zero]

lemma r_pos (M : Model) (hM : M.Std) : 0 < M.r := by
  have := hM.assm1_r
  have : 0 < M.c / M.p := div_pos hM.c_pos hM.p_pos
  linarith

lemma qo_pos (M : Model) (hM : M.Std) (qo : ℝ) (hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c) :
    0 < qo := by
  rcases hqo.1.lt_or_eq with h | h
  · exact h
  · exfalso
    have h2 := hqo.2
    rw [← h] at h2
    unfold G at h2
    rw [Fbar_zero M hM] at h2
    have := hM.assm1_r
    rw [div_lt_iff₀ hM.p_pos] at this
    nlinarith

/-- `buyerExPost` as `r E[f · min(q, ·)] − w q`. -/
lemma buyerExPost_E (M : Model) (hM : M.Std) (w q : ℝ) :
    buyerExPost M w q = M.r * (∫ d, M.f d * min q d) - w * q := by
  unfold buyerExPost SupplyChainTheory.expSales; rw [integral_demandLaw M hM]

lemma kink_nonneg (a b d : ℝ) (hab : a < b) :
    0 ≤ 2 * min ((a + b) / 2) d - min a d - min b d := by
  simp only [min_def]; split_ifs <;> linarith

lemma kink_pos (a b d : ℝ) (h1 : a < d) (h2 : d < b) :
    0 < 2 * min ((a + b) / 2) d - min a d - min b d := by
  simp only [min_def]; split_ifs <;> linarith

lemma buyer_unique_aux (M : Model) (hM : M.Std) (w : ℝ) (hw : 0 < w) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b)
    (hma : ∀ q, 0 ≤ q → buyerExPost M w q ≤ buyerExPost M w a)
    (hmb : ∀ q, 0 ≤ q → buyerExPost M w q ≤ buyerExPost M w b) : False := by
  have hr := r_pos M hM
  set m := (a + b) / 2 with hm
  have hm0 : 0 ≤ m := by rw [hm]; linarith
  have e1 := hma m hm0
  have e2 := hmb a ha
  have e3 := hma b (by linarith)
  simp only [buyerExPost_E M hM] at e1 e2 e3
  set Ea := ∫ d, M.f d * min a d
  set Eb := ∫ d, M.f d * min b d
  set Em := ∫ d, M.f d * min m d
  have hk : ∫ d, M.f d * (2 * min m d - min a d - min b d) = 2 * Em - Ea - Eb := by
    have : (fun d => M.f d * (2 * min m d - min a d - min b d)) =
        fun d => (2 * (M.f d * min m d) - M.f d * min a d) - M.f d * min b d := by
      funext d; ring
    have i1 : Integrable (fun d => 2 * (M.f d * min m d)) := (integrable_fmin M hM m).const_mul 2
    have i2 : Integrable (fun d => 2 * (M.f d * min m d) - M.f d * min a d) :=
      i1.sub (integrable_fmin M hM a)
    rw [this, integral_sub i2 (integrable_fmin M hM b), integral_sub i1 (integrable_fmin M hM a),
      integral_const_mul]
  have hint : Integrable (fun d => M.f d * (2 * min m d - min a d - min b d)) := by
    have : (fun d => M.f d * (2 * min m d - min a d - min b d)) =
        fun d => (2 * (M.f d * min m d) - M.f d * min a d) - M.f d * min b d := by
      funext d; ring
    rw [this]
    exact (((integrable_fmin M hM m).const_mul 2).sub (integrable_fmin M hM a)).sub
      (integrable_fmin M hM b)
  have hnn : 0 ≤ fun d => M.f d * (2 * min m d - min a d - min b d) :=
    fun d => mul_nonneg (f_nonneg M hM d) (kink_nonneg a b d hab)
  have hle : 2 * Em - Ea - Eb ≤ 0 := by
    have : M.r * (2 * Em - Ea - Eb) ≤ 0 := by nlinarith
    by_contra hc; push_neg at hc; nlinarith
  have hzero : ∫ d, M.f d * (2 * min m d - min a d - min b d) = 0 := by
    rw [hk]; exact le_antisymm hle (hk ▸ integral_nonneg hnn)
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).1 hzero
  -- the support ends at or before `a`
  have habar : M.abar ≤ ENNReal.ofReal a := by
    by_contra hc
    push_neg at hc
    obtain ⟨t, ht0, hat, htb⟩ := ENNReal.lt_iff_exists_real_btwn.1 hc
    have hat' : a < t := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).1 hat
    set d0 := min t b
    have had0 : a < d0 := lt_min hat' hab
    have hvol : volume (Set.Ioo a d0) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hae] with d hd
      intro hdI
      have hsupp : d ∈ supp M.abar := by
        refine ⟨by linarith [hdI.1], ?_⟩
        calc ENNReal.ofReal d ≤ ENNReal.ofReal t :=
              ENNReal.ofReal_le_ofReal (le_trans hdI.2.le (min_le_left _ _))
          _ < M.abar := htb
      have := mul_pos (hM.f_pos d hsupp)
        (kink_pos a b d hdI.1 (lt_of_lt_of_le hdI.2 (min_le_right _ _)))
      simp only [Pi.zero_apply] at hd
      linarith
    rw [Real.volume_Ioo] at hvol
    have : 0 < d0 - a := by linarith
    exact absurd hvol (ENNReal.ofReal_pos.2 this).ne'
  have hfz : ∀ d, a ≤ d → M.f d = 0 := by
    intro d hd
    refine hM.f_zero d (fun h => ?_)
    have := h.2
    have : ENNReal.ofReal a ≤ ENNReal.ofReal d := ENNReal.ofReal_le_ofReal hd
    exact absurd (lt_of_lt_of_le h.2 (le_trans habar this)) (lt_irrefl _)
  have hEab : Eb = Ea := by
    have : ∀ d, M.f d * min b d = M.f d * min a d := by
      intro d
      rcases le_or_gt d a with h | h
      · rw [min_eq_right h, min_eq_right (by linarith)]
      · rw [hfz d h.le, zero_mul, zero_mul]
    simp only [Eb, Ea, this]
  rw [hEab] at e2 e3
  nlinarith

lemma buyer_unique (M : Model) (hM : M.Std) (w : ℝ) (hw : 0 < w) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hma : ∀ q, 0 ≤ q → buyerExPost M w q ≤ buyerExPost M w a)
    (hmb : ∀ q, 0 ≤ q → buyerExPost M w q ≤ buyerExPost M w b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact (buyer_unique_aux M hM w hw a b ha h hma hmb).elim
  · exact h
  · exact (buyer_unique_aux M hM w hw b a hb h hmb hma).elim

/-- With guaranteed fraction `1` the delivery equals the order. -/
lemma Z_b1 (M : Model) (k : Regime) (σ : Profile) (h : IsSPE M k σ) (w q y : ℝ) (α : Bool)
    (hadm : Admissible k w 1) (hq : 0 ≤ q) (hy : 0 ≤ y) : σ.Z w 1 q y α = q := by
  have := (h.1 w 1 q y α hadm hq hy).1.1
  rw [one_mul] at this
  exact le_antisymm this.2 this.1

lemma orderValue_b1 (M : Model) (k : Regime) (σ : Profile) (h : IsSPE M k σ) (w q : ℝ)
    (hadm : Admissible k w 1) (hq : 0 ≤ q) : orderValue M σ w 1 q = buyerExPost M w q := by
  unfold orderValue Eα
  have hy := (h.2.1 w 1 q hadm hq).1
  beta_reduce
  rw [Z_b1 M k σ h w q _ true hadm hq hy, Z_b1 M k σ h w q _ false hadm hq hy]
  ring

lemma prodValue_b1 (M : Model) (k : Regime) (σ : Profile) (h : IsSPE M k σ) (w q y : ℝ)
    (hadm : Admissible k w 1) (hq : 0 ≤ q) (hy : 0 ≤ y) :
    prodValue M σ w 1 q y = Eα M.p (fun α => supplierExPost M w y q α) := by
  unfold prodValue Eα
  beta_reduce
  rw [Z_b1 M k σ h w q y true hadm hq hy, Z_b1 M k σ h w q y false hadm hq hy]

/-- Supplier's half: offering `b = 1` replicates the price-only continuation. -/
lemma supplier_half (M : Model) (hM : M.Std) (σX σP : Profile) (hX : IsSPE M .flex σX)
    (hP : IsSPE M .priceOnly σP) : supplierProfit M σP ≤ supplierProfit M σX := by
  obtain ⟨hw, hb⟩ := hP.2.2.2.1
  have hb1 : σP.b = 1 := hb
  set w := σP.w
  have hadmX : Admissible .flex w 1 := ⟨hw, ⟨zero_le_one, le_refl 1⟩⟩
  have hadmP : Admissible .priceOnly w 1 := ⟨hw, rfl⟩
  obtain ⟨hQX0, hQX⟩ := hX.2.2.1 w 1 hadmX
  obtain ⟨hQP0, hQP⟩ := hP.2.2.1 w 1 hadmP
  have hQ : σP.Q w 1 = σX.Q w 1 := by
    refine buyer_unique M hM w hw _ _ hQP0 hQX0 (fun q hq => ?_) (fun q hq => ?_)
    · rw [← orderValue_b1 M _ σP hP w q hadmP hq, ← orderValue_b1 M _ σP hP w _ hadmP hQP0]
      exact hQP q hq
    · rw [← orderValue_b1 M _ σX hX w q hadmX hq, ← orderValue_b1 M _ σX hX w _ hadmX hQX0]
      exact hQX q hq
  have hYP0 := (hP.2.1 w 1 (σP.Q w 1) hadmP hQP0).1
  obtain ⟨hYX0, hYX⟩ := hX.2.1 w 1 (σX.Q w 1) hadmX hQX0
  have step : contractValue M σP w 1 ≤ contractValue M σX w 1 := by
    unfold contractValue
    rw [prodValue_b1 M _ σP hP w _ _ hadmP hQP0 hYP0]
    have := hYX (σP.Y w 1 (σP.Q w 1)) hYP0
    rw [prodValue_b1 M _ σX hX w _ _ hadmX hQX0 hYP0] at this
    rw [hQ] at this ⊢
    exact this
  unfold supplierProfit
  rw [hb1]
  exact le_trans step (hX.2.2.2.2 w 1 hadmX)

/-- Buyer's equilibrium profit from the on-path outcome. -/
lemma flex_profit (M : Model) (hM : M.Std) (σ : Profile) (hX : IsSPE M .flex σ) (κ β : ℝ)
    (hβ : 0 ≤ β) (hQ : σ.Q σ.w σ.b = κ) (hY : σ.Y σ.w σ.b κ = κ)
    (hZ : ∀ α : Bool, (α = true ∨ M.p < 1) →
      σ.Z σ.w σ.b κ κ α = κ * max (if α then 1 else 0) β)
    (hw : σ.w * (M.p + (1 - M.p) * β) =
      M.r * (M.p * Fbar M.f κ + (1 - M.p) * β * Fbar M.f (β * κ))) :
    buyerProfit M σ = M.r * (M.p * (∫ x in Set.Ioc 0 κ, x * M.f x) +
      (1 - M.p) * ∫ x in Set.Ioc 0 (β * κ), x * M.f x) := by
  have hadm := hX.2.2.2.1
  have hκ : 0 ≤ κ := hQ ▸ (hX.2.2.1 σ.w σ.b hadm).1
  have hmem := (hX.1 σ.w σ.b κ κ true hadm hκ hκ).1.1
  have hz1 : σ.Z σ.w σ.b κ κ true = κ := by
    have h1 := hZ true (Or.inl rfl)
    simp only [if_true] at h1
    apply le_antisymm hmem.2
    rw [h1]; exact le_mul_of_one_le_right hκ (le_max_left _ _)
  have hβκ : 0 ≤ β * κ := mul_nonneg hβ hκ
  unfold buyerProfit orderValue Eα
  beta_reduce
  rw [hQ, hY, hz1, buyerExPost_eq M hM _ _ hκ]
  rcases (hM.p_le_one).lt_or_eq with hp | hp
  · have hz0 : σ.Z σ.w σ.b κ κ false = β * κ := by
      rw [hZ false (Or.inr hp)]; simp only [Bool.false_eq_true, if_false]
      rw [max_eq_right hβ, mul_comm]
    rw [hz0, buyerExPost_eq M hM _ _ hβκ]
    linear_combination (-κ) * hw
  · rw [hp] at hw ⊢
    simp only [sub_self, zero_mul, add_zero, one_mul] at hw ⊢
    linear_combination (-κ) * hw

end T6Aux

open T6Aux in
theorem solution (M : Model) (hM : M.Std) (hlc : ConvexOptimization.LogConcaveOn Set.univ M.f) :
    (∃ σ : Profile, IsSPE M .flex σ) ∧ (∃ σ : Profile, IsSPE M .priceOnly σ) ∧
    ∀ σX σP : Profile, IsSPE M .flex σX → IsSPE M .priceOnly σP →
      buyerProfit M σP ≤ buyerProfit M σX ∧ supplierProfit M σP ≤ supplierProfit M σX := by
  have hr := r_pos M hM
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have hcp0 : 0 < M.c / M.p := div_pos hM.c_pos hp
  have hcps : M.c < M.p * M.s := by
    have := hM.assm1_s; rw [div_lt_iff₀ hp] at this; linarith
  have hs0 : 0 < M.s := by linarith [hM.assm1_s]
  -- the roots of (1)–(4)
  obtain ⟨qo, hqo0, hqoe⟩ := root_G_exists M hM (M.c / M.p) hcp0 hM.assm1_r.le
  have hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c :=
    ⟨hqo0, by rw [mul_right_comm, hqoe, div_mul_cancel₀ _ hp.ne']⟩
  have hqo_pos := qo_pos M hM qo hqo
  obtain ⟨qh, hqh⟩ : ∃ qh : ℝ, (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧
      (M.r < M.s → qh = 0) := by
    by_cases hsr : M.s ≤ M.r
    · obtain ⟨q, hq0, hq⟩ := root_G_exists M hM M.s hs0 hsr
      exact ⟨q, fun _ => ⟨hq0, hq⟩, fun h => absurd h (not_lt.2 hsr)⟩
    · exact ⟨0, fun h => absurd h hsr, fun _ => rfl⟩
  have hqh0 : 0 ≤ qh := by
    by_cases hsr : M.s ≤ M.r
    · exact (hqh.1 hsr).1
    · rw [hqh.2 (lt_of_not_ge hsr)]
  obtain ⟨qt, hqt⟩ : ∃ qt : ℝ, M.c + (1 - M.p) * M.s ≤ M.r →
      0 ≤ qt ∧ M.r * G M.f qt = M.c + (1 - M.p) * M.s := by
    by_cases h : M.c + (1 - M.p) * M.s ≤ M.r
    · obtain ⟨q, hq0, hq⟩ := root_G_exists M hM _ (by nlinarith [hM.c_pos]) h
      exact ⟨q, fun _ => ⟨hq0, hq⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  obtain ⟨qc, hqc⟩ : ∃ qc : ℝ, M.s < wo M qo qh → qh ≤ qc ∧
      M.r * (M.p * qc * Fbar M.f qc + (1 - M.p) * qh * Fbar M.f qh) =
        M.s * (M.p * qc + (1 - M.p) * qh) := by
    by_cases h : M.s < wo M qo qh
    · obtain ⟨q, hq⟩ := root_qc_exists M hM qo qh hqo hqh h
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  set qstar := if M.c + (1 - M.p) * M.s ≤ M.r then qt else 0 with hqs_def
  have hqstar : (M.c + (1 - M.p) * M.s ≤ M.r →
        0 ≤ qstar ∧ M.r * G M.f qstar = M.c + (1 - M.p) * M.s) ∧
      (M.r < M.c + (1 - M.p) * M.s → qstar = 0) := by
    constructor
    · intro h; rw [hqs_def, if_pos h]; exact hqt h
    · intro h; rw [hqs_def, if_neg (not_le.2 h)]
  have T3 := theorem_3 M hM qt qo qh qc hqt hqo hqh hqc
  have T2 := theorem_2 M hM qstar hqstar
  refine ⟨⟨_, T3.1.choose_spec.1⟩, ⟨_, T2.1.choose_spec.1⟩, ?_⟩
  intro σX σP hX hP
  refine ⟨?_, supplier_half M hM σX σP hX hP⟩
  -- price-only buyer profit
  set Tf : ℝ → ℝ := fun z => ∫ x in Set.Ioc 0 z, x * M.f x with hTf
  have hPprofit : buyerProfit M σP = M.r * Tf qstar := by
    obtain ⟨hQP, hYP, hwP, -⟩ := T2.2 σP hP
    obtain ⟨hw, hb⟩ := hP.2.2.2.1
    have hb1 : σP.b = 1 := hb
    have hqs0 : 0 ≤ qstar := hQP ▸ (hP.2.2.1 σP.w σP.b hP.2.2.2.1).1
    unfold buyerProfit
    rw [hb1] at hQP ⊢
    rw [hQP, orderValue_b1 M _ σP hP σP.w qstar ⟨hw, rfl⟩ hqs0, buyerExPost_eq M hM _ _ hqs0]
    rcases hqs0.lt_or_eq with hpos | hzero
    · rw [hwP hpos]; simp only [hTf]; ring
    · rw [← hzero]; simp [hTf]
  rw [hPprofit]
  have hTnn := T_nonneg M hM
  -- flex buyer profit, generic
  have hβ1 : ∀ x : ℝ, 0 ≤ x → (0:ℝ) < M.p + (1 - M.p) * x := fun x hx => by nlinarith
  have hwfor : ∀ σ : Profile, σ.w = wStar M qt qo qh qc →
      0 ≤ betaStar M qt qo qh qc →
      σ.w * (M.p + (1 - M.p) * betaStar M qt qo qh qc) =
        M.r * (M.p * Fbar M.f (kappaStar M qt qo qh qc) + (1 - M.p) * betaStar M qt qo qh qc *
          Fbar M.f (betaStar M qt qo qh qc * kappaStar M qt qo qh qc)) := by
    intro σ hσ hb
    rw [hσ, wStar, div_mul_cancel₀ _ (hβ1 _ hb).ne']
  have hwo_r : M.r < M.s → wo M qo qh ≤ M.s := by
    intro hrs
    rw [hqh.2 hrs, wo]
    simp only [mul_zero, zero_mul, add_zero]
    rw [show M.r * (M.p * qo * Fbar M.f qo) / (M.p * qo) = M.r * Fbar M.f qo by
      field_simp]
    nlinarith [Fbar_le_one M hM qo]
  have flexgen : ∀ σ : Profile, IsSPE M .flex σ → 0 ≤ betaStar M qt qo qh qc →
      (σ.w = wStar M qt qo qh qc ∧ σ.Q σ.w σ.b = kappaStar M qt qo qh qc ∧
        σ.Y σ.w σ.b (kappaStar M qt qo qh qc) = kappaStar M qt qo qh qc ∧
        ∀ α : Bool, (α = true ∨ M.p < 1) →
          σ.Z σ.w σ.b (kappaStar M qt qo qh qc) (kappaStar M qt qo qh qc) α =
            kappaStar M qt qo qh qc * max (if α then 1 else 0) (betaStar M qt qo qh qc)) →
      buyerProfit M σ = M.r * (M.p * Tf (kappaStar M qt qo qh qc) +
        (1 - M.p) * Tf (betaStar M qt qo qh qc * kappaStar M qt qo qh qc)) := by
    intro σ hσ hb h
    exact flex_profit M hM σ hσ _ _ hb h.2.1 h.2.2.1 h.2.2.2 (hwfor σ h.1 hb)
  have fin : ∀ V : ℝ, buyerProfit M σX = M.r * V → Tf qstar ≤ V →
      M.r * Tf qstar ≤ buyerProfit M σX := by
    intro V h1 h2; rw [h1]; exact mul_le_mul_of_nonneg_left h2 hr.le
  have A116 : M.s ≤ M.r → Tf qt ≤ M.p * Tf qo + (1 - M.p) * Tf qh :=
    fun hsr => eq_A1_16_paren M hM hlc qt qo qh hqt hqo hqh hsr
  have hcs_of : M.s ≤ M.r → M.c + (1 - M.p) * M.s ≤ M.r := fun hsr => by nlinarith
  -- Scenario 2 (κ* = q̌)
  have sc2 : M.s ≤ M.r → M.s < wo M qo qh → kappaStar M qt qo qh qc = qc →
      betaStar M qt qo qh qc = qh / qc →
      (σX.w = wStar M qt qo qh qc ∧ σX.Q σX.w σX.b = kappaStar M qt qo qh qc ∧
        σX.Y σX.w σX.b (kappaStar M qt qo qh qc) = kappaStar M qt qo qh qc ∧
        ∀ α : Bool, (α = true ∨ M.p < 1) →
          σX.Z σX.w σX.b (kappaStar M qt qo qh qc) (kappaStar M qt qo qh qc) α =
            kappaStar M qt qo qh qc * max (if α then 1 else 0) (betaStar M qt qo qh qc)) →
      M.r * Tf qstar ≤ buyerProfit M σX := by
    intro hsr hsw hk hb hdata
    have hqc' := hqc hsw
    have hlt := qo_lt_qc M hM qo qh qc hqo hqh hsw hqc'
    have hqc0 : 0 < qc := lt_trans hqo_pos hlt
    have hb0 : 0 ≤ betaStar M qt qo qh qc := by rw [hb]; exact div_nonneg hqh0 hqc0.le
    have hprof := flexgen σX hX hb0 hdata
    rw [hk, hb, div_mul_cancel₀ _ hqc0.ne'] at hprof
    refine fin _ hprof ?_
    rw [hqs_def, if_pos (hcs_of hsr)]
    have := T_mono M hM hlt.le
    have := A116 hsr
    simp only [hTf] at *
    nlinarith
  -- the main case analysis
  by_cases htie : M.s < wo M qo qh ∧
      qc * (M.p * M.s - M.c) = qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c)
  · -- the tie: s ≤ r necessarily
    have hsr : M.s ≤ M.r := by
      by_contra h; exact absurd (hwo_r (lt_of_not_ge h)) (not_le.2 htie.1)
    have hk : kappaStar M qt qo qh qc = qc := by
      unfold kappaStar; rw [if_neg (not_le.2 htie.1), if_pos htie.2.symm.le]
    have hb : betaStar M qt qo qh qc = qh / qc := by
      unfold betaStar
      rw [if_neg (not_lt.2 hsr), if_neg (fun h => by rw [htie.2] at h; exact lt_irrefl _ h.2), hk]
    rcases theorem_3_tie M hM qt qo qh qc hqt hqo hqh hqc htie σX hX with h | h
    · exact sc2 hsr htie.1 hk hb h
    · obtain ⟨h1, h2, h3, h4⟩ := h
      have hprof := flex_profit M hM σX hX qt 1 zero_le_one h2 h3
        (fun α hα => by
          rw [h4 α hα, max_eq_right (by split_ifs <;> norm_num), mul_one])
        (by rw [h1]; ring_nf)
      refine fin _ hprof ?_
      rw [hqs_def, if_pos (hcs_of hsr), one_mul]
      simp only [hTf]; nlinarith
  · have hu := T3.2 htie σX hX
    by_cases hrs : M.r < M.s
    · have hk : kappaStar M qt qo qh qc = qo := by
        unfold kappaStar; rw [if_pos (hwo_r hrs)]
      have hb : betaStar M qt qo qh qc = 0 := by unfold betaStar; rw [if_pos hrs]
      have hprof := flexgen σX hX (by rw [hb]) hu
      rw [hk, hb, zero_mul] at hprof
      refine fin _ hprof ?_
      have h0 : Tf 0 = 0 := by simp [hTf]
      rw [h0, mul_zero, add_zero]
      by_cases hcs : M.c + (1 - M.p) * M.s ≤ M.r
      · rw [hqs_def, if_pos hcs]
        exact eq_A1_18 M hM hlc qt qo hqt hqo hrs hcs
      · rw [hqs_def, if_neg hcs, h0]
        exact mul_nonneg hp.le (hTnn qo)
    · have hsr : M.s ≤ M.r := le_of_not_gt hrs
      by_cases hws : wo M qo qh ≤ M.s
      · have hk : kappaStar M qt qo qh qc = qo := by
          unfold kappaStar; rw [if_pos hws]
        have hb : betaStar M qt qo qh qc = qh / qo := by
          unfold betaStar
          rw [if_neg hrs, if_neg (fun h => not_lt.2 hws h.1), hk]
        have hprof := flexgen σX hX (by rw [hb]; exact div_nonneg hqh0 hqo0) hu
        rw [hk, hb, div_mul_cancel₀ _ hqo_pos.ne'] at hprof
        refine fin _ hprof ?_
        rw [hqs_def, if_pos (hcs_of hsr)]
        exact A116 hsr
      · have hsw : M.s < wo M qo qh := lt_of_not_ge hws
        by_cases hstr : qc * (M.p * M.s - M.c) < qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c)
        · have hk : kappaStar M qt qo qh qc = qt := by
            unfold kappaStar; rw [if_neg hws, if_neg (not_le.2 hstr)]
          have hb : betaStar M qt qo qh qc = 1 := by
            unfold betaStar; rw [if_neg hrs, if_pos ⟨hsw, hstr⟩]
          have hprof := flexgen σX hX (by rw [hb]; exact zero_le_one) hu
          rw [hk, hb, one_mul] at hprof
          refine fin _ hprof ?_
          rw [hqs_def, if_pos (hcs_of hsr)]
          simp only [hTf]; nlinarith
        · have hk : kappaStar M qt qo qh qc = qc := by
            unfold kappaStar; rw [if_neg hws, if_pos (le_of_not_gt hstr)]
          have hb : betaStar M qt qo qh qc = qh / qc := by
            unfold betaStar; rw [if_neg hrs, if_neg (fun h => hstr h.2), hk]
          exact sc2 hsr hsw hk hb hu
