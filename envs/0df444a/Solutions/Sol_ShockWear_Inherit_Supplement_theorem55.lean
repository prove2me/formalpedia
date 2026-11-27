-- Prove2me | solution 1 for ShockWear.Inherit.Supplement.theorem55
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:26:21.492668+00:00
-- url     : https://prove2.me/submissions/46ea8bb6-95c7-4213-b73d-a6fcedf0caf7

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model
import Definitions.Def_ShockWear_RandThreshold_Model
import Definitions.Def_ShockWear_Inherit_Supplement_TotalPositivity
import Definitions.Def_ShockWear_Inherit_Supplement_Density

open ShockWear
open ShockWear.Inherit
open ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem solution (lam : ℝ) (hlam : 0 < lam)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iic 0) = 0)
    (hF : IsPF2Function (fun x => (μ (Set.Iic x)).toReal))
    (g : ℝ → ℝ) (hg : IsDensity ν g) (hpg : IsPF2Function g) :
    ShockWear.RandThreshold.randP μ ν 0 = 1 ∧
    Antitone (ShockWear.RandThreshold.randP μ ν) ∧
    (∀ k, 0 ≤ ShockWear.RandThreshold.randP μ ν k) ∧
    IsPF2SeqFrom 0 (ShockWear.RandThreshold.randP μ ν) ∧
    IsIHR (ShockWear.RandThreshold.shockSurv lam (ShockWear.RandThreshold.randP μ ν)) := by
      have LA : ∀ f g h : ℝ → ℝ, Measurable f → Measurable g → Measurable h →
          (∀ e, 0 ≤ f e) → (∀ e, 0 ≤ g e) → (∀ e, 0 ≤ h e) → (∀ e, f e ≤ 1) → (∀ e, g e ≤ 1) →
          (∀ e, h e ≤ 1) → Integrable f → Integrable g → Integrable h →
          (∀ a b, f a * g b ≤ h ((a + b) / 2) ^ 2) →
          (∫ e, f e) * (∫ e, g e) ≤ (∫ e, h e) ^ 2 := by
        intro f g h hfm hgm hhm hf0 hg0 hh0 hf1 hg1 hh1 hfi hgi hhi hfgh
        -- Brunn–Minkowski for compact nonempty sets
        have BMc : ∀ (K L C : Set ℝ), IsCompact K → IsCompact L → K.Nonempty → L.Nonempty →
            (∀ a ∈ K, ∀ b ∈ L, (a + b) / 2 ∈ C) → volume K + volume L ≤ 2 * volume C := by
          intro K L C hK hL hKn hLn hKL
          set k := sSup K
          set l := sInf L
          have hk : k ∈ K := hK.sSup_mem hKn
          have hl : l ∈ L := hL.sInf_mem hLn
          have hkK : ∀ a ∈ K, a ≤ k := fun a ha => le_csSup hK.bddAbove ha
          have hlL : ∀ b ∈ L, l ≤ b := fun b hb => csInf_le hL.bddBelow hb
          set m := (k + l) / 2
          have h2 : ∀ S : Set ℝ, volume ((fun x => (1/2 : ℝ) * x) ⁻¹' S) = 2 * volume S := by
            intro S
            have := Real.volume_preimage_mul_left (a := (1/2 : ℝ)) (by norm_num) S
            rw [this]; congr 1; norm_num
          have hLs : volume L ≤ 2 * volume (C ∩ Set.Ici m) := by
            calc volume L ≤ volume ((fun b => k + b) ⁻¹' ((fun x => (1/2 : ℝ) * x) ⁻¹' (C ∩ Set.Ici m))) := by
                  refine measure_mono fun b hb => ?_
                  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ici]
                  refine ⟨?_, ?_⟩
                  · have := hKL k hk b hb; convert this using 1; ring
                  · have := hlL b hb; simp only [m]; linarith
              _ = 2 * volume (C ∩ Set.Ici m) := by rw [measure_preimage_add, h2]
          have hKs : volume K ≤ 2 * volume (C ∩ Set.Iic m) := by
            calc volume K ≤ volume ((fun a => a + l) ⁻¹' ((fun x => (1/2 : ℝ) * x) ⁻¹' (C ∩ Set.Iic m))) := by
                  refine measure_mono fun a ha => ?_
                  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Iic]
                  refine ⟨?_, ?_⟩
                  · have := hKL a ha l hl; convert this using 1; ring
                  · have := hkK a ha; simp only [m]; linarith
              _ = 2 * volume (C ∩ Set.Iic m) := by rw [measure_preimage_add_right, h2]
          have hsplit : volume (C ∩ Set.Iic m) + volume (C ∩ Set.Ici m) ≤ volume C := by
            have e1 : volume (C ∩ Set.Ici m) ≤ volume (C ∩ Set.Ioi m) := by
              calc volume (C ∩ Set.Ici m) ≤ volume ((C ∩ Set.Ioi m) ∪ {m}) := by
                    refine measure_mono fun x hx => ?_
                    rcases (Set.mem_Ici.mp hx.2).lt_or_eq with h | h
                    · exact Or.inl ⟨hx.1, h⟩
                    · exact Or.inr h.symm
                _ ≤ volume (C ∩ Set.Ioi m) + volume ({m} : Set ℝ) := measure_union_le _ _
                _ = volume (C ∩ Set.Ioi m) := by rw [Real.volume_singleton, add_zero]
            have e2 : C \ Set.Iic m = C ∩ Set.Ioi m := by ext x; simp
            calc _ ≤ volume (C ∩ Set.Iic m) + volume (C ∩ Set.Ioi m) := add_le_add le_rfl e1
              _ = volume C := by rw [← e2, measure_inter_add_sdiff _ measurableSet_Iic]
          calc volume K + volume L ≤ 2 * volume (C ∩ Set.Iic m) + 2 * volume (C ∩ Set.Ici m) :=
                add_le_add hKs hLs
            _ = 2 * (volume (C ∩ Set.Iic m) + volume (C ∩ Set.Ici m)) := by rw [mul_add]
            _ ≤ 2 * volume C := by gcongr
        -- Brunn–Minkowski for measurable nonempty finite-measure sets
        have BM : ∀ (A B C : Set ℝ), MeasurableSet A → MeasurableSet B → A.Nonempty → B.Nonempty →
            volume A ≠ ⊤ → volume B ≠ ⊤ →
            (∀ a ∈ A, ∀ b ∈ B, (a + b) / 2 ∈ C) → volume A + volume B ≤ 2 * volume C := by
          intro A B C hA hB hAn hBn hAt hBt hAB
          refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
          have hε2 : ((ε / 2 : NNReal) : ENNReal) ≠ 0 := by
            simp only [ne_eq, ENNReal.coe_eq_zero]; exact (half_pos hε).ne'
          obtain ⟨K, hKA, hK, hKlt⟩ := hA.exists_isCompact_lt_add hAt hε2
          obtain ⟨L, hLB, hL, hLlt⟩ := hB.exists_isCompact_lt_add hBt hε2
          obtain ⟨a0, ha0⟩ := hAn
          obtain ⟨b0, hb0⟩ := hBn
          have hK' : insert a0 K ⊆ A := Set.insert_subset ha0 hKA
          have hL' : insert b0 L ⊆ B := Set.insert_subset hb0 hLB
          have key := BMc (insert a0 K) (insert b0 L) C (hK.insert a0) (hL.insert b0)
            (Set.insert_nonempty _ _) (Set.insert_nonempty _ _)
            (fun a ha b hb => hAB a (hK' ha) b (hL' hb))
          have hmK : volume K ≤ volume (insert a0 K) := measure_mono (Set.subset_insert _ _)
          have hmL : volume L ≤ volume (insert b0 L) := measure_mono (Set.subset_insert _ _)
          have hεsum : ((ε / 2 : NNReal) : ENNReal) + ((ε / 2 : NNReal) : ENNReal) = (ε : ENNReal) := by
            rw [← ENNReal.coe_add, add_halves]
          calc volume A + volume B ≤ (volume K + ((ε / 2 : NNReal) : ENNReal)) +
                (volume L + ((ε / 2 : NNReal) : ENNReal)) := add_le_add hKlt.le hLlt.le
            _ = (volume K + volume L) + ε := by rw [← hεsum]; ring
            _ ≤ 2 * volume C + ε := by gcongr; exact (add_le_add hmK hmL).trans key
        have hIf : 0 ≤ ∫ e, f e := integral_nonneg hf0
        have hIg : 0 ≤ ∫ e, g e := integral_nonneg hg0
        have hIh : 0 ≤ ∫ e, h e := integral_nonneg hh0
        rcases hIf.lt_or_eq with hpf | hpf
        swap
        · rw [← hpf, zero_mul]; positivity
        rcases hIg.lt_or_eq with hpg | hpg
        swap
        · rw [← hpg, mul_zero]; positivity
        -- sup normalization
        have hbf : BddAbove (Set.range f) := ⟨1, by rintro _ ⟨e, rfl⟩; exact hf1 e⟩
        have hbg : BddAbove (Set.range g) := ⟨1, by rintro _ ⟨e, rfl⟩; exact hg1 e⟩
        set Mf := sSup (Set.range f) with hMf
        set Mg := sSup (Set.range g) with hMg
        have hfM : ∀ e, f e ≤ Mf := fun e => le_csSup hbf ⟨e, rfl⟩
        have hgM : ∀ e, g e ≤ Mg := fun e => le_csSup hbg ⟨e, rfl⟩
        have hMfpos : 0 < Mf := by
          by_contra hc
          push_neg at hc
          have : ∫ e, f e = 0 := by
            rw [integral_eq_zero_of_ae (Filter.Eventually.of_forall fun e => ?_)]
            exact le_antisymm ((hfM e).trans hc) (hf0 e)
          linarith
        have hMgpos : 0 < Mg := by
          by_contra hc
          push_neg at hc
          have : ∫ e, g e = 0 := by
            rw [integral_eq_zero_of_ae (Filter.Eventually.of_forall fun e => ?_)]
            exact le_antisymm ((hgM e).trans hc) (hg0 e)
          linarith
        set c := Real.sqrt (Mf * Mg) with hc
        have hcpos : 0 < c := Real.sqrt_pos.mpr (mul_pos hMfpos hMgpos)
        have hc2 : c ^ 2 = Mf * Mg := Real.sq_sqrt (mul_pos hMfpos hMgpos).le
        obtain ⟨f', hf'⟩ : ∃ f' : ℝ → ℝ, f' = fun e => f e / Mf := ⟨_, rfl⟩
        obtain ⟨g', hg'⟩ : ∃ g' : ℝ → ℝ, g' = fun e => g e / Mg := ⟨_, rfl⟩
        obtain ⟨h', hh'⟩ : ∃ h' : ℝ → ℝ, h' = fun e => h e / c := ⟨_, rfl⟩
        have hf'e : ∀ e, f' e = f e / Mf := fun e => by rw [hf']
        have hg'e : ∀ e, g' e = g e / Mg := fun e => by rw [hg']
        have hh'e : ∀ e, h' e = h e / c := fun e => by rw [hh']
        have hf'0 : ∀ e, 0 ≤ f' e := fun e => by rw [hf'e]; exact div_nonneg (hf0 e) hMfpos.le
        have hg'0 : ∀ e, 0 ≤ g' e := fun e => by rw [hg'e]; exact div_nonneg (hg0 e) hMgpos.le
        have hh'0 : ∀ e, 0 ≤ h' e := fun e => by rw [hh'e]; exact div_nonneg (hh0 e) hcpos.le
        have hf'1 : ∀ e, f' e ≤ 1 := fun e => by rw [hf'e]; exact (div_le_one hMfpos).mpr (hfM e)
        have hg'1 : ∀ e, g' e ≤ 1 := fun e => by rw [hg'e]; exact (div_le_one hMgpos).mpr (hgM e)
        have hf'ex : ∀ t < 1, ∃ e, t < f' e := by
          intro t ht
          obtain ⟨_, ⟨e, rfl⟩, he⟩ := exists_lt_of_lt_csSup (Set.range_nonempty f)
            (show t * Mf < Mf by nlinarith only [ht, hMfpos])
          exact ⟨e, by rw [hf'e]; exact (lt_div_iff₀ hMfpos).mpr he⟩
        have hg'ex : ∀ t < 1, ∃ e, t < g' e := by
          intro t ht
          obtain ⟨_, ⟨e, rfl⟩, he⟩ := exists_lt_of_lt_csSup (Set.range_nonempty g)
            (show t * Mg < Mg by nlinarith only [ht, hMgpos])
          exact ⟨e, by rw [hg'e]; exact (lt_div_iff₀ hMgpos).mpr he⟩
        have hmid : ∀ a b, f' a * g' b ≤ h' ((a + b) / 2) ^ 2 := by
          intro a b
          simp only [hf'e, hg'e, hh'e, div_pow, hc2]
          rw [div_mul_div_comm]
          exact div_le_div_of_nonneg_right (hfgh a b) (mul_pos hMfpos hMgpos).le
        have hf'i : Integrable f' := by rw [hf']; exact hfi.div_const _
        have hg'i : Integrable g' := by rw [hg']; exact hgi.div_const _
        have hh'i : Integrable h' := by rw [hh']; exact hhi.div_const _
        have hf'm : Measurable f' := by rw [hf']; exact hfm.div_const _
        have hg'm : Measurable g' := by rw [hg']; exact hgm.div_const _
        have hh'm : Measurable h' := by rw [hh']; exact hhm.div_const _
        -- level-set inequality
        have hlev : ∀ t ∈ Set.Ioi (0:ℝ), volume {a | t < f' a} + volume {a | t < g' a} ≤
            2 * volume {a | t < h' a} := by
          intro t ht
          have ht0 : 0 < t := ht
          rcases lt_or_ge t 1 with ht1 | ht1
          · have hfin : ∀ φ : ℝ → ℝ, Integrable φ → volume {a | t < φ a} ≠ ⊤ := by
              intro φ hφ
              refine (lt_of_le_of_lt (measure_mono fun a ha => ?_) (hφ.measure_norm_ge_lt_top ht0)).ne
              simp only [Set.mem_setOf_eq] at ha ⊢
              exact ha.le.trans (le_abs_self _)
            obtain ⟨a0, ha0⟩ := hf'ex t ht1
            obtain ⟨b0, hb0⟩ := hg'ex t ht1
            refine BM _ _ _ (measurableSet_lt measurable_const hf'm) (measurableSet_lt measurable_const hg'm)
              ⟨a0, ha0⟩ ⟨b0, hb0⟩ (hfin _ hf'i) (hfin _ hg'i) ?_
            intro a ha b hb
            simp only [Set.mem_setOf_eq] at ha hb ⊢
            have h1 : t ^ 2 < h' ((a + b) / 2) ^ 2 := by
              calc t ^ 2 = t * t := sq t
                _ < f' a * g' b := mul_lt_mul'' ha hb ht0.le ht0.le
                _ ≤ _ := hmid a b
            exact lt_of_pow_lt_pow_left₀ 2 (hh'0 _) h1
          · have e1 : {a | t < f' a} = ∅ := by
              ext a; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
              exact (hf'1 a).trans ht1
            have e2 : {a | t < g' a} = ∅ := by
              ext a; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
              exact (hg'1 a).trans ht1
            rw [e1, e2, measure_empty, zero_add]; positivity
        -- integrate the level-set inequality
        have hlc : ∀ φ : ℝ → ℝ, Measurable φ → (∀ e, 0 ≤ φ e) →
            ∫⁻ e, ENNReal.ofReal (φ e) = ∫⁻ t in Set.Ioi 0, volume {a | t < φ a} := fun φ hφ hφ0 =>
          lintegral_eq_lintegral_meas_lt volume (Filter.Eventually.of_forall hφ0) hφ.aemeasurable
        have hanti : ∀ φ : ℝ → ℝ, Measurable (fun t : ℝ => volume {a | t < φ a}) := by
          intro φ
          refine Antitone.measurable fun t1 t2 ht => measure_mono fun a ha => ?_
          simp only [Set.mem_setOf_eq] at ha ⊢; linarith
        have hlin : (∫⁻ e, ENNReal.ofReal (f' e)) + (∫⁻ e, ENNReal.ofReal (g' e)) ≤
            2 * ∫⁻ e, ENNReal.ofReal (h' e) := by
          have e1 := hlc f' hf'm hf'0
          have e2 := hlc g' hg'm hg'0
          have e3 := hlc h' hh'm hh'0
          have hlin0 : (∫⁻ t in Set.Ioi 0, volume {a | t < f' a}) + (∫⁻ t in Set.Ioi 0, volume {a | t < g' a}) ≤
              2 * ∫⁻ t in Set.Ioi 0, volume {a | t < h' a} := by
            calc _ = ∫⁻ t in Set.Ioi 0, (volume {a | t < f' a} + volume {a | t < g' a}) :=
                  (lintegral_add_left (hanti f') _).symm
              _ ≤ ∫⁻ t in Set.Ioi 0, 2 * volume {a | t < h' a} :=
                  setLIntegral_mono ((hanti h').const_mul _) hlev
              _ = _ := lintegral_const_mul _ (hanti h')
          calc _ = (∫⁻ t in Set.Ioi 0, volume {a | t < f' a}) + (∫⁻ t in Set.Ioi 0, volume {a | t < g' a}) := by
                rw [e1, e2]
            _ ≤ _ := hlin0
            _ = _ := by rw [e3]
        have hIf' : 0 ≤ ∫ e, f' e := integral_nonneg hf'0
        have hIg' : 0 ≤ ∫ e, g' e := integral_nonneg hg'0
        have hIh' : 0 ≤ ∫ e, h' e := integral_nonneg hh'0
        rw [← ofReal_integral_eq_lintegral_ofReal hf'i (Filter.Eventually.of_forall hf'0),
          ← ofReal_integral_eq_lintegral_ofReal hg'i (Filter.Eventually.of_forall hg'0),
          ← ofReal_integral_eq_lintegral_ofReal hh'i (Filter.Eventually.of_forall hh'0),
          ← ENNReal.ofReal_add hIf' hIg',
          show (2 : ENNReal) = ENNReal.ofReal 2 by simp,
          ← ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_le_ofReal_iff (by positivity)] at hlin
        have ef : ∫ e, f' e = (∫ e, f e) / Mf := by rw [hf']; exact integral_div _ _
        have eg : ∫ e, g' e = (∫ e, g e) / Mg := by rw [hg']; exact integral_div _ _
        have eh : ∫ e, h' e = (∫ e, h e) / c := by rw [hh']; exact integral_div _ _
        set p := ∫ e, f' e
        set q := ∫ e, g' e
        set r := ∫ e, h' e
        have hp : ∫ e, f e = Mf * p := by rw [ef]; field_simp
        have hq : ∫ e, g e = Mg * q := by rw [eg]; field_simp
        have hr : ∫ e, h e = c * r := by rw [eh]; field_simp
        have hp0 : 0 ≤ p := hIf'
        have hq0 : 0 ≤ q := hIg'
        have hpqr : p * q ≤ r ^ 2 := by
          have h2 : 0 ≤ (p + q) / 2 := by linarith only [hp0, hq0]
          have h1 : (p + q) / 2 ≤ r := by linarith only [hlin]
          have := mul_le_mul h1 h1 h2 (h2.trans h1)
          nlinarith only [this, sq_nonneg (p - q)]
        rw [hp, hq, hr, mul_pow, hc2]
        have : Mf * p * (Mg * q) = (Mf * Mg) * (p * q) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hpqr (mul_pos hMfpos hMgpos).le
      have LC : ∀ H : ℝ → ℝ, Monotone H → (∀ x, 0 ≤ H x) →
          (∀ x y, H x * H y ≤ H ((x + y) / 2) ^ 2) →
          ∀ s t d : ℝ, s ≤ t → 0 ≤ d → H s * H (t + d) ≤ H (s + d) * H t := by
        intro H hm h0 hmid s t d hst hd
        rcases (h0 s).lt_or_eq with hs | hs
        swap
        · rw [← hs, zero_mul]; exact mul_nonneg (h0 _) (h0 _)
        rcases hd.lt_or_eq with hd | hd
        swap
        · rw [← hd, add_zero, add_zero]
        have hpos : ∀ x, s ≤ x → 0 < H x := fun x hx => lt_of_lt_of_le hs (hm hx)
        set φ : ℝ → ℝ := fun x => Real.log (H x) with hφ
        have hmidφ : ∀ x y, s ≤ x → s ≤ y → φ x + φ y ≤ 2 * φ ((x + y) / 2) := by
          intro x y hx hy
          simp only [hφ]
          rw [← Real.log_mul (hpos x hx).ne' (hpos y hy).ne']
          have : Real.log (H ((x + y) / 2) ^ 2) = 2 * Real.log (H ((x + y) / 2)) := by
            rw [Real.log_pow]; norm_num
          rw [← this]
          exact Real.log_le_log (mul_pos (hpos x hx) (hpos y hy)) (hmid x y)
        have hmonoφ : ∀ x y, s ≤ x → x ≤ y → φ x ≤ φ y := fun x y hx hxy =>
          Real.log_le_log (hpos x hx) (hm hxy)
        have hD : ∀ x h, s ≤ x → 0 ≤ h → φ (x + h + h) - φ (x + h) ≤ φ (x + h) - φ x := by
          intro x h hx hh
          have := hmidφ x (x + h + h) hx (by linarith)
          have e : (x + (x + h + h)) / 2 = x + h := by ring
          rw [e] at this; linarith
        have hDj : ∀ j : ℕ, ∀ x h, s ≤ x → 0 ≤ h →
            φ (x + j * h + h) - φ (x + j * h) ≤ φ (x + h) - φ x := by
          intro j
          induction j with
          | zero => intro x h hx hh; simp
          | succ j ih =>
            intro x h hx hh
            have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
            have h1 := hD (x + j * h) h (by have := mul_nonneg hj hh; linarith only [this, hx]) hh
            have h2 := ih x h hx hh
            have e1 : x + ((j + 1 : ℕ) : ℝ) * h = x + j * h + h := by push_cast; ring
            rw [e1]; linarith
        have htel : ∀ (x h : ℝ) (n : ℕ), φ (x + n * h) - φ x =
            ∑ i ∈ Finset.range n, (φ (x + (i : ℝ) * h + h) - φ (x + (i : ℝ) * h)) := by
          intro x h n
          have := Finset.sum_range_sub (fun i : ℕ => φ (x + (i : ℝ) * h)) n
          simp only [Nat.cast_zero, zero_mul, add_zero] at this
          rw [← this]
          refine Finset.sum_congr rfl fun i _ => ?_
          have e : x + ((i + 1 : ℕ) : ℝ) * h = x + i * h + h := by push_cast; ring
          rw [e]
        set A := φ (s + d) - φ s with hA
        have hA0 : 0 ≤ A := by have := hmonoφ s (s + d) le_rfl (by linarith); linarith
        have hstep : ∀ n : ℕ, 0 < n → φ (t + d) - φ t ≤ A + A / n := by
          intro n hn
          have hn' : (0:ℝ) < n := by exact_mod_cast hn
          set h := d / n with hh
          have hh0 : 0 < h := div_pos hd hn'
          have hdn : d = n * h := by rw [hh]; field_simp
          set m := ⌊(t - s) / h⌋₊ with hmdef
          set r := (t - s) - m * h with hr
          have hm1 : (m : ℝ) ≤ (t - s) / h := Nat.floor_le (div_nonneg (by linarith) hh0.le)
          have hm2 : (t - s) / h < m + 1 := Nat.lt_floor_add_one _
          have hr0 : 0 ≤ r := by
            have := (le_div_iff₀ hh0).mp hm1; rw [hr]; linarith
          have hrh : r ≤ h := by
            have := (div_lt_iff₀ hh0).mp hm2; rw [hr]; linarith only [this]
          -- step 1
          have s1 : φ (t + n * h) - φ t ≤ φ (s + r + n * h) - φ (s + r) := by
            rw [htel t h n, htel (s + r) h n]
            refine Finset.sum_le_sum fun i _ => ?_
            have hi : (0:ℝ) ≤ i := Nat.cast_nonneg i
            have := hDj m (s + r + i * h) h (by have := mul_nonneg hi hh0.le; linarith only [this, hr0]) hh0.le
            have e : t + (i : ℝ) * h = s + r + i * h + m * h := by rw [hr]; ring
            rw [e]; exact this
          -- step 3
          have s3 : (n : ℝ) * (φ (s + n * h + h) - φ (s + n * h)) ≤ φ (s + n * h) - φ s := by
            rw [htel s h n]
            calc (n : ℝ) * (φ (s + n * h + h) - φ (s + n * h))
                = ∑ i ∈ Finset.range n, (φ (s + n * h + h) - φ (s + n * h)) := by simp [mul_sub]
              _ ≤ _ := by
                refine Finset.sum_le_sum fun i hi => ?_
                have hin : i ≤ n := (Finset.mem_range.mp hi).le
                have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg i
                have := hDj (n - i) (s + i * h) h (by have := mul_nonneg hi0 hh0.le; linarith only [this]) hh0.le
                have e : s + (i : ℝ) * h + ((n - i : ℕ) : ℝ) * h = s + n * h := by
                  rw [Nat.cast_sub hin]; ring
                rw [e] at this; exact this
          rw [← hdn] at s1 s3
          have s4 : φ (s + d + h) - φ (s + d) ≤ A / n := by
            rw [le_div_iff₀ hn']; linarith
          have m1 : φ (s + r + d) ≤ φ (s + d + h) := hmonoφ _ _ (by linarith) (by linarith)
          have m2 : φ s ≤ φ (s + r) := hmonoφ _ _ le_rfl (by linarith)
          linarith
        have key : φ (t + d) - φ t ≤ A := by
          by_contra hlt
          push Not at hlt
          set ε := φ (t + d) - φ t - A with hε
          have hε0 : 0 < ε := by linarith
          obtain ⟨n, hn⟩ := exists_nat_gt (A / ε)
          have hn0 : 0 < n := by
            have : (0:ℝ) < n := lt_of_le_of_lt (div_nonneg hA0 hε0.le) hn
            exact_mod_cast this
          have hn' : (0:ℝ) < n := by exact_mod_cast hn0
          have : A / n < ε := by
            rw [div_lt_iff₀ hn']; rw [div_lt_iff₀ hε0] at hn; linarith
          have := hstep n hn0
          linarith
        have hfin : φ s + φ (t + d) ≤ φ (s + d) + φ t := by linarith
        have := Real.exp_le_exp.mpr hfin
        rw [Real.exp_add, Real.exp_add] at this
        simp only [hφ] at this
        rwa [Real.exp_log (hpos s le_rfl), Real.exp_log (hpos _ (by linarith)),
          Real.exp_log (hpos _ (by linarith)), Real.exp_log (hpos _ hst)] at this
      have LD : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
          (hF : ∀ x y, (μ (Set.Iic x)).toReal * (μ (Set.Iic y)).toReal ≤
            (μ (Set.Iic ((x + y) / 2))).toReal ^ 2),
          ∃ ψ : ℝ → ℝ, Measurable ψ ∧
            (∀ e1 e2 : ℝ, 0 < e1 → 0 < e2 → ψ ((e1 + e2) / 2) ≤ (ψ e1 + ψ e2) / 2) ∧
            ∀ G : ℝ → ℝ, Measurable G → (∀ x, 0 ≤ G x) → (∀ x, G x ≤ 1) →
              ∫ a, G a ∂μ = ∫ e in Set.Ioi 0, Real.exp (-e) * G (ψ e) := by
        intro μ _ hμ hF
        set F : ℝ → ℝ := fun x => ProbabilityTheory.cdf μ x with hFdef
        have hFeq : ∀ x, (μ (Set.Iic x)).toReal = F x := by
          intro x; simp [hFdef, ProbabilityTheory.cdf_eq_real, measureReal_def]
        simp only [hFeq] at hF
        have hFmono : Monotone F := ProbabilityTheory.monotone_cdf μ
        have hF0 : ∀ x, 0 ≤ F x := ProbabilityTheory.cdf_nonneg μ
        have hF1 : ∀ x, F x ≤ 1 := ProbabilityTheory.cdf_le_one μ
        have hFneg : ∀ x, x < 0 → F x = 0 := by
          intro x hx
          rw [← hFeq]
          have : μ (Set.Iic x) = 0 := measure_mono_null (Set.Iic_subset_Iio.mpr hx) hμ
          simp [this]
        have hFtop : Filter.Tendsto F Filter.atTop (nhds 1) := ProbabilityTheory.tendsto_cdf_atTop μ
        have hFrc : ∀ x, ContinuousWithinAt F (Set.Ici x) x :=
          fun x => (ProbabilityTheory.cdf μ).right_continuous x
        let S : ℝ → Set ℝ := fun e => {a | Real.exp (-e) ≤ F a}
        have hSne : ∀ e, 0 < e → (S e).Nonempty := by
          intro e he
          have hlt : Real.exp (-e) < 1 := by
            calc Real.exp (-e) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
              _ = 1 := Real.exp_zero
          obtain ⟨a, ha⟩ := (hFtop.eventually (lt_mem_nhds hlt)).exists
          exact ⟨a, ha.le⟩
        have hSbdd : ∀ e, BddBelow (S e) := by
          intro e
          refine ⟨0, fun a ha => ?_⟩
          by_contra h
          push_neg at h
          have := hFneg a h
          simp only [S, Set.mem_setOf_eq, this] at ha
          linarith [Real.exp_pos (-e)]
        let ψ : ℝ → ℝ := fun e => if 0 < e then sInf (S e) else 0
        have hgal : ∀ e, 0 < e → ∀ x, ψ e ≤ x ↔ Real.exp (-e) ≤ F x := by
          intro e he x
          simp only [ψ, if_pos he]
          constructor
          · intro hx
            -- F (sInf S) ≥ exp(-e) by right continuity
            have hc : Real.exp (-e) ≤ F (sInf (S e)) := by
              have hlim : Filter.Tendsto F (nhdsWithin (sInf (S e)) (Set.Ioi (sInf (S e))))
                  (nhds (F (sInf (S e)))) :=
                ((hFrc _).mono Set.Ioi_subset_Ici_self).tendsto
              refine ge_of_tendsto hlim ?_
              filter_upwards [self_mem_nhdsWithin] with y hy
              obtain ⟨a, haS, hay⟩ := exists_lt_of_csInf_lt (hSne e he) hy
              exact le_trans haS (hFmono hay.le)
            exact hc.trans (hFmono hx)
          · intro hx
            exact csInf_le (hSbdd e) hx
        have hψmeas : Measurable ψ := by
          refine measurable_of_Iic fun x => ?_
          have : ψ ⁻¹' Set.Iic x = ({e | 0 < e} ∩ {e | Real.exp (-e) ≤ F x}) ∪
              ({e | e ≤ 0} ∩ {_e | (0:ℝ) ≤ x}) := by
            ext e
            simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff,
              Set.mem_setOf_eq]
            by_cases he : 0 < e
            · rw [hgal e he]; constructor
              · intro h; exact Or.inl ⟨he, h⟩
              · rintro (⟨_, h⟩ | ⟨h, _⟩)
                · exact h
                · linarith
            · have hψ0 : ψ e = 0 := by simp [ψ, he]
              rw [hψ0]; push_neg at he
              constructor
              · intro h; exact Or.inr ⟨he, h⟩
              · rintro (⟨h, _⟩ | ⟨_, h⟩)
                · linarith
                · exact h
          rw [this]
          exact (measurableSet_Ioi.inter (measurableSet_le (by fun_prop) measurable_const)).union
            (measurableSet_Iic.inter (by by_cases h : (0:ℝ) ≤ x <;> simp [h]))
        refine ⟨ψ, hψmeas, ?_, ?_⟩
        · intro e1 e2 h1 h2
          have hm : 0 < (e1 + e2) / 2 := by linarith
          rw [hgal _ hm]
          have a1 := (hgal e1 h1 (ψ e1)).mp le_rfl
          have a2 := (hgal e2 h2 (ψ e2)).mp le_rfl
          have hprod := hF (ψ e1) (ψ e2)
          have hexp : Real.exp (-((e1 + e2) / 2)) ^ 2 = Real.exp (-e1) * Real.exp (-e2) := by
            rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
          have hsq : Real.exp (-((e1 + e2) / 2)) ^ 2 ≤ F ((ψ e1 + ψ e2) / 2) ^ 2 := by
            rw [hexp]
            calc Real.exp (-e1) * Real.exp (-e2) ≤ F (ψ e1) * F (ψ e2) :=
                  mul_le_mul a1 a2 (Real.exp_pos _).le (hF0 _)
              _ ≤ _ := hprod
          exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (hF0 _) (by norm_num)).mp hsq
        · intro G hG hG0 hG1
          set m : Measure ℝ := (volume.restrict (Set.Ioi 0)).withDensity
            (fun e => ((Real.exp (-e)).toNNReal : ENNReal)) with hm
          have hmeas_dens : Measurable (fun e : ℝ => (Real.exp (-e)).toNNReal) := by fun_prop
          -- m (Ioi c) = exp(-c) for c ≥ 0, and same for Ici c
          have hmIoi : ∀ c : ℝ, 0 ≤ c → m (Set.Ioi c) = ENNReal.ofReal (Real.exp (-c)) := by
            intro c hc
            rw [hm, withDensity_apply _ measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
              Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi hc)]
            rw [← integral_exp_neg_Ioi c, ofReal_integral_eq_lintegral_ofReal]
            · rfl
            · have := exp_neg_integrableOn_Ioi c (zero_lt_one' ℝ)
              simp only [neg_mul, one_mul] at this
              exact this
            · exact Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
          have hmIci : ∀ c : ℝ, 0 < c → m (Set.Ici c) = ENNReal.ofReal (Real.exp (-c)) := by
            intro c hc
            rw [← hmIoi c hc.le]
            refine measure_congr ?_
            rw [hm]
            refine (Ioi_ae_eq_Ici (μ := (volume.restrict (Set.Ioi 0)).withDensity _)).symm
          have hmap : m.map ψ = μ := by
            haveI : IsFiniteMeasure m := by
              refine ⟨?_⟩
              have : m Set.univ ≤ m (Set.Ioi 0) := by
                rw [hm, withDensity_apply _ MeasurableSet.univ, withDensity_apply _ measurableSet_Ioi,
                  Measure.restrict_univ, Measure.restrict_restrict measurableSet_Ioi, Set.inter_self]
              rw [hmIoi 0 le_rfl] at this
              exact this.trans_lt ENNReal.ofReal_lt_top
            refine Measure.ext_of_Iic _ _ fun x => ?_
            rw [Measure.map_apply hψmeas measurableSet_Iic]
            have hmz : m (Set.Iic 0) = 0 := by
              rw [hm, withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
              have : Set.Iic (0:ℝ) ∩ Set.Ioi 0 = ∅ := by
                ext e; simp
              rw [this]; simp
            have hμx : μ (Set.Iic x) = ENNReal.ofReal (F x) := by
              rw [← hFeq, ENNReal.ofReal_toReal (measure_ne_top _ _)]
            rw [hμx]
            -- m (ψ⁻¹ Iic x) = m (ψ⁻¹ Iic x ∩ Ioi 0)
            have hsplit : m (ψ ⁻¹' Set.Iic x) = m (ψ ⁻¹' Set.Iic x ∩ Set.Ioi 0) := by
              have hS : MeasurableSet (ψ ⁻¹' Set.Iic x) := hψmeas measurableSet_Iic
              rw [hm, withDensity_apply _ hS, withDensity_apply _ (hS.inter measurableSet_Ioi),
                Measure.restrict_restrict hS, Measure.restrict_restrict (hS.inter measurableSet_Ioi),
                Set.inter_assoc, Set.inter_self]
            rw [hsplit]
            have hset : ψ ⁻¹' Set.Iic x ∩ Set.Ioi 0 = {e | 0 < e ∧ Real.exp (-e) ≤ F x} := by
              ext e
              simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioi,
                Set.mem_setOf_eq]
              constructor
              · rintro ⟨h, he⟩; exact ⟨he, (hgal e he x).mp h⟩
              · rintro ⟨he, h⟩; exact ⟨(hgal e he x).mpr h, he⟩
            rw [hset]
            rcases (hF0 x).lt_or_eq with hpos | hzero
            · set c := -Real.log (F x) with hc
              have hc0 : 0 ≤ c := by
                rw [hc, neg_nonneg]; exact Real.log_nonpos (hF0 x) (hF1 x)
              have hexpc : Real.exp (-c) = F x := by rw [hc, neg_neg, Real.exp_log hpos]
              have hiff : ∀ e, Real.exp (-e) ≤ F x ↔ c ≤ e := by
                intro e
                rw [← hexpc, Real.exp_le_exp]; constructor <;> intro h <;> linarith
              have hsub1 : Set.Ioi c ⊆ {e | 0 < e ∧ Real.exp (-e) ≤ F x} := by
                intro e he
                simp only [Set.mem_Ioi] at he
                exact ⟨by linarith, (hiff e).mpr he.le⟩
              have hsub2 : {e | 0 < e ∧ Real.exp (-e) ≤ F x} ⊆ Set.Ioi 0 ∩ Set.Ici c := by
                intro e ⟨he, h⟩; exact ⟨he, (hiff e).mp h⟩
              apply le_antisymm
              · calc _ ≤ m (Set.Ioi 0 ∩ Set.Ici c) := measure_mono hsub2
                  _ = ENNReal.ofReal (F x) := by
                    rcases hc0.lt_or_eq with hcp | hce
                    · rw [Set.inter_eq_right.mpr (Set.Ici_subset_Ioi.mpr hcp), hmIci c hcp, hexpc]
                    · rw [← hce, Set.inter_eq_left.mpr (Set.Ioi_subset_Ici_self), hmIoi 0 le_rfl,
                        ← hexpc, ← hce]
              · calc ENNReal.ofReal (F x) = m (Set.Ioi c) := by rw [hmIoi c hc0, hexpc]
                  _ ≤ _ := measure_mono hsub1
            · have : {e | 0 < e ∧ Real.exp (-e) ≤ F x} = ∅ := by
                ext e; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and,
                  not_le]
                intro _; rw [← hzero]; exact Real.exp_pos _
              rw [this, ← hzero]; simp
          rw [← hmap, integral_map hψmeas.aemeasurable hG.aestronglyMeasurable, hm,
            integral_withDensity_eq_integral_smul hmeas_dens]
          refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
          simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le]
      have hcompG : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (g : ℝ → ℝ), IsDensity ν g →
          IsPF2Function g →
          ∀ H : ℝ → ℝ, Monotone H → (∀ x, 0 ≤ H x) → (∀ x, H x ≤ 1) →
            (∀ (s t d : ℝ), s ≤ t → 0 ≤ d → H s * H (t + d) ≤ H (s + d) * H t) →
            ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
              (∫ x, H (x - 0) ∂ν) * (∫ x, H (x - (a + b)) ∂ν) ≤
                (∫ x, H (x - a) ∂ν) * (∫ x, H (x - b) ∂ν) := by
        intro ν _ g hg hpg
        intro H hHm hH0 hH1 hHlc a b ha hb
        obtain ⟨hgm, hg0, hνg⟩ := hg
        have hg2 : ∀ v v' z1 z2 : ℝ, v ≤ v' → z1 ≤ z2 →
            g (v - z2) * g (v' - z1) ≤ g (v - z1) * g (v' - z2) := by
          intro v v' z1 z2 hv hz
          rcases hv.lt_or_eq with hv | hv
          · rcases hz.lt_or_eq with hz | hz
            · have := hpg 2 (by norm_num) le_rfl ![v, v'] ![z1, z2] (fun _ => trivial) (fun _ => trivial)
                (Fin.strictMono_iff_lt_succ.mpr fun i => by fin_cases i; simpa using hv)
                (Fin.strictMono_iff_lt_succ.mpr fun i => by fin_cases i; simpa using hz)
              simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
                Matrix.head_cons, one_mul] at this
              linarith
            · subst hz; linarith [mul_comm (g (v - z1)) (g (v' - z1))]
          · subst hv; linarith [mul_comm (g (v - z1)) (g (v - z2))]
        have hgint : Integrable g := by
          have h1 : ν Set.univ = 1 := measure_univ
          rw [hνg, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
          refine ⟨hgm.aestronglyMeasurable, ?_⟩
          rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hg0), h1]
          exact ENNReal.one_lt_top
        have hHmeas : Measurable H := hHm.measurable
        -- ψ(y - z) = ∫ H(v - y) g(v - z) dv
        have hψ : ∀ y z : ℝ, (∫ x, H (x - (y - z)) ∂ν) = ∫ v, H (v - y) * g (v - z) := by
          intro y z
          rw [hνg, integral_withDensity_eq_integral_toReal_smul₀ (hgm.ennreal_ofReal)
            (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
          simp_rw [ENNReal.toReal_ofReal (hg0 _), smul_eq_mul]
          rw [← integral_add_right_eq_self (fun v => H (v - y) * g (v - z)) z]
          congr 1; ext x; rw [mul_comm]; congr 2 <;> ring
        have hint : ∀ y z : ℝ, Integrable (fun v => H (v - y) * g (v - z)) := by
          intro y z
          have : Integrable (fun v => g (v - z)) := hgint.comp_sub_right z
          refine this.bdd_mul (c := 1) (hHmeas.comp (by fun_prop)).aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (hH0 _)]; exact hH1 _
        -- composition with y1 = a, y2 = a + b, z1 = 0, z2 = a
        have key : ∀ y1 y2 z1 z2 : ℝ, y1 ≤ y2 → z1 ≤ z2 →
            (∫ v, H (v - y1) * g (v - z2)) * (∫ v, H (v - y2) * g (v - z1)) ≤
              (∫ v, H (v - y1) * g (v - z1)) * (∫ v, H (v - y2) * g (v - z2)) := by
          intro y1 y2 z1 z2 hy hz
          rw [← integral_prod_mul, ← integral_prod_mul]
          have hI1 := (hint y1 z2).mul_prod (hint y2 z1)
          have hI2 := (hint y1 z1).mul_prod (hint y2 z2)
          rw [← sub_nonneg, ← integral_sub hI2 hI1]
          set D : ℝ × ℝ → ℝ := fun p => H (p.1 - y1) * g (p.1 - z1) * (H (p.2 - y2) * g (p.2 - z2)) -
            H (p.1 - y1) * g (p.1 - z2) * (H (p.2 - y2) * g (p.2 - z1)) with hD
          have hDi : Integrable D (volume.prod volume) := hI2.sub hI1
          clear_value D
          have hswap : ∫ p, (D ∘ Prod.swap) p ∂(volume.prod volume) = ∫ p, D p ∂(volume.prod volume) :=
            integral_prod_swap D
          have hsum := integral_add hDi hDi.swap
          have h2 : 0 ≤ ∫ p, (D p + (D ∘ Prod.swap) p) ∂(volume.prod volume) := by
            refine integral_nonneg fun p => ?_
            obtain ⟨v, v'⟩ := p
            show 0 ≤ D (v, v') + D (v', v)
            rw [hD]
            have key2 : ∀ v v' : ℝ, v ≤ v' →
                0 ≤ H (v - y1) * g (v - z1) * (H (v' - y2) * g (v' - z2)) -
                  H (v - y1) * g (v - z2) * (H (v' - y2) * g (v' - z1)) +
                  (H (v' - y1) * g (v' - z1) * (H (v - y2) * g (v - z2)) -
                  H (v' - y1) * g (v' - z2) * (H (v - y2) * g (v - z1))) := by
              intro v v' hv
              have h1 : H (v - y2) * H (v' - y1) ≤ H (v - y1) * H (v' - y2) := by
                have := hHlc (v - y2) (v' - y2) (y2 - y1) (by linarith) (by linarith)
                simp only [show v' - y2 + (y2 - y1) = v' - y1 by ring,
                  show v - y2 + (y2 - y1) = v - y1 by ring] at this
                exact this
              have h2 := hg2 v v' z1 z2 hv hz
              have e : H (v - y1) * g (v - z1) * (H (v' - y2) * g (v' - z2)) -
                  H (v - y1) * g (v - z2) * (H (v' - y2) * g (v' - z1)) +
                  (H (v' - y1) * g (v' - z1) * (H (v - y2) * g (v - z2)) -
                  H (v' - y1) * g (v' - z2) * (H (v - y2) * g (v - z1))) =
                  (H (v - y1) * H (v' - y2) - H (v - y2) * H (v' - y1)) *
                    (g (v - z1) * g (v' - z2) - g (v - z2) * g (v' - z1)) := by ring
              rw [e]; exact mul_nonneg (by linarith) (by linarith)
            rcases le_total v v' with hv | hv
            · exact key2 v v' hv
            · exact (key2 v' v hv).trans_eq (by ring)
          rw [hsum, hswap] at h2
          linarith
        have := key a (a + b) 0 a (by linarith) ha
        rw [← hψ, ← hψ, ← hψ, ← hψ] at this
        simp only [sub_zero, sub_self, add_sub_cancel_left] at this
        simpa only [sub_zero] using this
      have hclosG : ∀ (μ : Measure ℝ) (ψe : ℝ → ℝ), Measurable ψe →
          (∀ e1 e2 : ℝ, 0 < e1 → 0 < e2 → ψe ((e1 + e2) / 2) ≤ (ψe e1 + ψe e2) / 2) →
          (∀ G : ℝ → ℝ, Measurable G → (∀ x, 0 ≤ G x) → (∀ x, G x ≤ 1) →
            ∫ a, G a ∂μ = ∫ e in Set.Ioi 0, Real.exp (-e) * G (ψe e)) →
          ∀ G : ℝ → ℝ, Monotone G → (∀ x, 0 ≤ G x) → (∀ x, G x ≤ 1) →
            (∀ x y, G x * G y ≤ G ((x + y) / 2) ^ 2) →
            ∀ x y, (∫ a, G (x - a) ∂μ) * (∫ a, G (y - a) ∂μ) ≤ (∫ a, G ((x + y) / 2 - a) ∂μ) ^ 2 := by
        intro μ ψe hψem hψec hrep
        intro G hGm hG0 hG1 hGmid x y
        have hGmeas : Measurable G := hGm.measurable
        have hr : ∀ z, ∫ a, G (z - a) ∂μ = ∫ e, (Set.Ioi (0:ℝ)).indicator
            (fun e => Real.exp (-e) * G (z - ψe e)) e := by
          intro z
          rw [hrep (fun a => G (z - a)) (hGmeas.comp (by fun_prop)) (fun _ => hG0 _) (fun _ => hG1 _),
            integral_indicator measurableSet_Ioi]
        rw [hr, hr, hr]
        have hm : ∀ z, Measurable ((Set.Ioi (0:ℝ)).indicator (fun e => Real.exp (-e) * G (z - ψe e))) :=
          fun z => (Measurable.mul (by fun_prop) (hGmeas.comp (by fun_prop))).indicator measurableSet_Ioi
        have h0 : ∀ z e, 0 ≤ (Set.Ioi (0:ℝ)).indicator (fun e => Real.exp (-e) * G (z - ψe e)) e := by
          intro z e
          by_cases he : e ∈ Set.Ioi (0:ℝ)
          · rw [Set.indicator_of_mem he]; exact mul_nonneg (Real.exp_pos _).le (hG0 _)
          · rw [Set.indicator_of_notMem he]
        have hle : ∀ z e, (Set.Ioi (0:ℝ)).indicator (fun e => Real.exp (-e) * G (z - ψe e)) e ≤ Real.exp (-e) := by
          intro z e
          by_cases he : e ∈ Set.Ioi (0:ℝ)
          · rw [Set.indicator_of_mem he]
            calc Real.exp (-e) * G (z - ψe e) ≤ Real.exp (-e) * 1 :=
                  mul_le_mul_of_nonneg_left (hG1 _) (Real.exp_pos _).le
              _ = _ := mul_one _
          · rw [Set.indicator_of_notMem he]; exact (Real.exp_pos _).le
        have h1 : ∀ z e, (Set.Ioi (0:ℝ)).indicator (fun e => Real.exp (-e) * G (z - ψe e)) e ≤ 1 := by
          intro z e
          by_cases he : e ∈ Set.Ioi (0:ℝ)
          · rw [Set.indicator_of_mem he]
            have : Real.exp (-e) ≤ 1 := by
              rw [Real.exp_le_one_iff]; simp only [Set.mem_Ioi] at he; linarith
            calc Real.exp (-e) * G (z - ψe e) ≤ 1 * 1 :=
                  mul_le_mul this (hG1 _) (hG0 _) zero_le_one
              _ = 1 := one_mul _
          · rw [Set.indicator_of_notMem he]; exact zero_le_one
        have hint : ∀ z, Integrable ((Set.Ioi (0:ℝ)).indicator (fun e => Real.exp (-e) * G (z - ψe e))) := by
          intro z
          refine (integrable_indicator_iff measurableSet_Ioi).mpr ?_
          refine (integrableOn_exp_neg_Ioi 0).mono' ?_ ?_
          · exact ((Measurable.mul (by fun_prop) (hGmeas.comp (by fun_prop)))).aestronglyMeasurable
          · refine Filter.Eventually.of_forall fun e => ?_
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hG0 _))]
            calc Real.exp (-e) * G (z - ψe e) ≤ Real.exp (-e) * 1 :=
                  mul_le_mul_of_nonneg_left (hG1 _) (Real.exp_pos _).le
              _ = _ := mul_one _
        refine LA _ _ _ (hm x) (hm y) (hm _) (h0 x) (h0 y) (h0 _) (h1 x) (h1 y) (h1 _)
          (hint x) (hint y) (hint _) ?_
        intro a b
        by_cases ha : a ∈ Set.Ioi (0:ℝ)
        · by_cases hb : b ∈ Set.Ioi (0:ℝ)
          · simp only [Set.mem_Ioi] at ha hb
            have hab : (a + b) / 2 ∈ Set.Ioi (0:ℝ) := by simp only [Set.mem_Ioi]; linarith
            rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ha), Set.indicator_of_mem (Set.mem_Ioi.mpr hb),
              Set.indicator_of_mem hab]
            have hc := hψec a b ha hb
            have hG' : G ((x - ψe a + (y - ψe b)) / 2) ≤ G ((x + y) / 2 - ψe ((a + b) / 2)) :=
              hGm (by linarith)
            have hGG := hGmid (x - ψe a) (y - ψe b)
            have hGsq : G ((x - ψe a + (y - ψe b)) / 2) ^ 2 ≤ G ((x + y) / 2 - ψe ((a + b) / 2)) ^ 2 :=
              pow_le_pow_left₀ (hG0 _) hG' 2
            have hexp : Real.exp (-a) * Real.exp (-b) = Real.exp (-((a + b) / 2)) ^ 2 := by
              rw [← Real.exp_add, sq, ← Real.exp_add]; congr 1; ring
            have hE : 0 ≤ Real.exp (-a) * Real.exp (-b) := by positivity
            calc Real.exp (-a) * G (x - ψe a) * (Real.exp (-b) * G (y - ψe b))
                = (Real.exp (-a) * Real.exp (-b)) * (G (x - ψe a) * G (y - ψe b)) := by ring
              _ ≤ (Real.exp (-a) * Real.exp (-b)) * G ((x + y) / 2 - ψe ((a + b) / 2)) ^ 2 :=
                  mul_le_mul_of_nonneg_left (hGG.trans hGsq) hE
              _ = _ := by rw [hexp]; ring
          · rw [Set.indicator_of_notMem hb, mul_zero]; positivity
        · rw [Set.indicator_of_notMem ha, zero_mul]; positivity
      have hprob : ∀ k, IsProbabilityMeasure (ShockWear.RandThreshold.convPow μ k) := by
        intro k
        induction k with
        | zero => simp only [ShockWear.RandThreshold.convPow]; infer_instance
        | succ k ih => simp only [ShockWear.RandThreshold.convPow]; infer_instance
      have hcdf_le : ∀ k x, ShockWear.RandThreshold.cdfPow μ (k + 1) x ≤
          ShockWear.RandThreshold.cdfPow μ k x := by
        intro k x
        have := hprob k
        unfold ShockWear.RandThreshold.cdfPow
        refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
        simp only [ShockWear.RandThreshold.convPow]
        rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Iic]
        calc ((ShockWear.RandThreshold.convPow μ k).prod μ) ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Set.Iic x)
            ≤ ((ShockWear.RandThreshold.convPow μ k).prod μ)
                (Set.Iic x ×ˢ Set.univ ∪ Set.univ ×ˢ Set.Iio 0) := by
              refine measure_mono ?_
              intro p hp
              simp only [Set.mem_preimage, Set.mem_Iic] at hp
              by_cases h : p.1 ≤ x
              · left; exact ⟨h, trivial⟩
              · right; refine ⟨trivial, ?_⟩; simp only [Set.mem_Iio]; linarith
          _ ≤ ((ShockWear.RandThreshold.convPow μ k).prod μ) (Set.Iic x ×ˢ Set.univ) +
              ((ShockWear.RandThreshold.convPow μ k).prod μ) (Set.univ ×ˢ Set.Iio 0) :=
              measure_union_le _ _
          _ = (ShockWear.RandThreshold.convPow μ k) (Set.Iic x) := by
              rw [Measure.prod_prod, Measure.prod_prod, hμ]; simp
      have hcdf_nn : ∀ k x, 0 ≤ ShockWear.RandThreshold.cdfPow μ k x := fun k x => ENNReal.toReal_nonneg
      have hcdf_le1 : ∀ k x, ShockWear.RandThreshold.cdfPow μ k x ≤ 1 := by
        intro k x
        have := hprob k
        unfold ShockWear.RandThreshold.cdfPow
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
      have hcdf_mono : ∀ k, Monotone (ShockWear.RandThreshold.cdfPow μ k) := by
        intro k a b hab
        have := hprob k
        unfold ShockWear.RandThreshold.cdfPow
        exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.mpr hab))
      have hcdf_int : ∀ k, Integrable (ShockWear.RandThreshold.cdfPow μ k) ν := by
        intro k
        refine Integrable.of_bound (hcdf_mono k).measurable.aestronglyMeasurable 1
          (Filter.Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hcdf_nn k x)]; exact hcdf_le1 k x
      have hP0 : ShockWear.RandThreshold.randP μ ν 0 = 1 := by
        unfold ShockWear.RandThreshold.randP
        have : ∀ᵐ x ∂ν, ShockWear.RandThreshold.cdfPow μ 0 x = 1 := by
          have hae : ∀ᵐ x ∂ν, x ∈ (Set.Iic (0:ℝ))ᶜ := by
            rw [ae_iff]; convert hν0 using 2; ext; simp
          filter_upwards [hae] with x hx
          simp only [Set.mem_compl_iff, Set.mem_Iic, not_le] at hx
          unfold ShockWear.RandThreshold.cdfPow
          simp only [ShockWear.RandThreshold.convPow]
          rw [Measure.dirac_apply' _ measurableSet_Iic]
          simp [hx.le]
        rw [integral_congr_ae this]; simp
      have hanti : Antitone (ShockWear.RandThreshold.randP μ ν) := by
        refine antitone_nat_of_succ_le fun k => ?_
        exact integral_mono (hcdf_int (k+1)) (hcdf_int k) (fun x => hcdf_le k x)
      have hnn : ∀ k, 0 ≤ ShockWear.RandThreshold.randP μ ν k := by
        intro k; exact integral_nonneg (hcdf_nn k)
      have hadj : ∀ j, ShockWear.RandThreshold.randP μ ν (j + 2) * ShockWear.RandThreshold.randP μ ν j ≤
          ShockWear.RandThreshold.randP μ ν (j + 1) * ShockWear.RandThreshold.randP μ ν (j + 1) := by
        have hstep : ∀ k x, ShockWear.RandThreshold.cdfPow μ (k + 1) x =
            ∫ a, ShockWear.RandThreshold.cdfPow μ k (x - a) ∂μ := by
          intro k x
          have := hprob k
          unfold ShockWear.RandThreshold.cdfPow
          simp only [ShockWear.RandThreshold.convPow]
          rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Iic,
            Measure.prod_apply_symm (measurable_add measurableSet_Iic)]
          have hmeas : Measurable fun a : ℝ => (ShockWear.RandThreshold.convPow μ k) (Set.Iic (x - a)) := by
            refine Antitone.measurable (fun a b hab => measure_mono (Set.Iic_subset_Iic.mpr (by linarith)))
          rw [integral_toReal hmeas.aemeasurable (Filter.Eventually.of_forall fun _ => measure_lt_top _ _)]
          congr 1
          refine lintegral_congr fun a => ?_
          congr 1
          ext w; simp only [Set.mem_preimage, Set.mem_Iic]; constructor <;> intro h <;> linarith
        set ψ : ℕ → ℝ → ℝ := fun k y => ∫ x, ShockWear.RandThreshold.cdfPow μ k (x - y) ∂ν with hψ
        have hψmeas2 : ∀ k (y : ℝ), Measurable (fun p : ℝ × ℝ => ShockWear.RandThreshold.cdfPow μ k (p.1 - y - p.2)) :=
          fun k y => (hcdf_mono k).measurable.comp (by fun_prop)
        have hψint : ∀ k y, Integrable (fun x => ShockWear.RandThreshold.cdfPow μ k (x - y)) ν := by
          intro k y
          refine Integrable.of_bound ((hcdf_mono k).measurable.comp (by fun_prop)).aestronglyMeasurable 1
            (Filter.Eventually.of_forall fun x => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (hcdf_nn _ _)]; exact hcdf_le1 _ _
        have hψnn : ∀ k y, 0 ≤ ψ k y := fun k y => integral_nonneg fun x => hcdf_nn _ _
        have hψle1 : ∀ k y, ψ k y ≤ 1 := by
          intro k y
          calc ψ k y ≤ ∫ x, (1:ℝ) ∂ν := integral_mono (hψint k y) (integrable_const _) (fun x => hcdf_le1 _ _)
            _ = 1 := by simp
        have hψanti : ∀ k, Antitone (ψ k) := by
          intro k a b hab
          exact integral_mono (hψint k b) (hψint k a) (fun x => hcdf_mono k (by linarith))
        have hψstep : ∀ k y, ψ (k + 1) y = ∫ a, ψ k (y + a) ∂μ := by
          intro k y
          simp only [hψ]
          simp_rw [hstep k]
          have hI : Integrable (fun p : ℝ × ℝ => ShockWear.RandThreshold.cdfPow μ k (p.1 - y - p.2)) (ν.prod μ) := by
            refine Integrable.of_bound (hψmeas2 k y).aestronglyMeasurable 1
              (Filter.Eventually.of_forall fun x => ?_)
            rw [Real.norm_eq_abs, abs_of_nonneg (hcdf_nn _ _)]; exact hcdf_le1 _ _
          rw [integral_integral_swap hI]
          congr 1; ext a; congr 1; ext x; congr 1; ring
        have hP : ∀ k, ShockWear.RandThreshold.randP μ ν k = ψ k 0 := by
          intro k; simp [hψ, ShockWear.RandThreshold.randP]
        -- (i) PF₂ of the cdf is preserved by convolution (Barlow–Proschan 1965, Thm 5.3), stated
        -- in log-concave form: H s * H (t + d) ≤ H (s + d) * H t for s ≤ t, 0 ≤ d.
        have hFk : ∀ k (s t d : ℝ), s ≤ t → 0 ≤ d →
            ShockWear.RandThreshold.cdfPow μ k s * ShockWear.RandThreshold.cdfPow μ k (t + d) ≤
              ShockWear.RandThreshold.cdfPow μ k (s + d) * ShockWear.RandThreshold.cdfPow μ k t := by
          have hFmid : ∀ x y, (μ (Set.Iic x)).toReal * (μ (Set.Iic y)).toReal ≤
                (μ (Set.Iic ((x + y) / 2))).toReal ^ 2 := by
            intro x y
            wlog hxy : x < y generalizing x y
            · rcases (not_lt.mp hxy).lt_or_eq with h | h
              · have := this y x h; rw [add_comm y x] at this; linarith
              · rw [h, show (x + x) / 2 = x by ring, sq]
            set m := (x + y) / 2
            have hmy : m < y := by simp only [m]; linarith
            have h0m : (0:ℝ) < m - x := by simp only [m]; linarith
            have := hF 2 (by norm_num) le_rfl ![m, y] ![0, m - x] (fun _ => trivial) (fun _ => trivial)
              (Fin.strictMono_iff_lt_succ.mpr fun i => by fin_cases i; simpa using hmy)
              (Fin.strictMono_iff_lt_succ.mpr fun i => by fin_cases i; simpa using h0m)
            simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.head_cons, one_mul, sub_zero, sub_sub_cancel] at this
            have e : y - (m - x) = m := by simp only [m]; ring
            rw [e] at this
            rw [sq]; linarith
          obtain ⟨ψe, hψem, hψec, hrep⟩ := LD μ hμ hFmid
          obtain ⟨ψe, hψem, hψec, hrep⟩ := LD μ hμ hFmid
          have hFmidk : ∀ k x y, ShockWear.RandThreshold.cdfPow μ k x * ShockWear.RandThreshold.cdfPow μ k y ≤
              ShockWear.RandThreshold.cdfPow μ k ((x + y) / 2) ^ 2 := by
            intro k
            induction k with
            | zero =>
              intro x y
              have h0 : ∀ z, ShockWear.RandThreshold.cdfPow μ 0 z = if 0 ≤ z then 1 else 0 := by
                intro z
                unfold ShockWear.RandThreshold.cdfPow
                simp only [ShockWear.RandThreshold.convPow]
                rw [Measure.dirac_apply' _ measurableSet_Iic]
                by_cases hz : 0 ≤ z
                · simp [hz]
                · simp [hz]
              rw [h0, h0, h0]
              by_cases hx : 0 ≤ x
              · by_cases hy : 0 ≤ y
                · have : 0 ≤ (x + y) / 2 := by linarith only [hx, hy]
                  rw [if_pos hx, if_pos hy, if_pos this]; norm_num
                · rw [if_neg hy, mul_zero]; exact sq_nonneg _
              · rw [if_neg hx, zero_mul]; exact sq_nonneg _
            | succ k ih =>
              intro x y
              rw [hstep, hstep, hstep]
              exact hclosG μ ψe hψem hψec hrep _ (hcdf_mono k) (hcdf_nn k) (hcdf_le1 k) ih x y
          intro k
          exact LC _ (hcdf_mono k) (hcdf_nn k) (hFmidk k)
        -- (ii) basic composition formula: integrating a PF₂ function against the PF₂ density g of ν
        -- yields a log-concave function of the shift.
        have hcomp := hcompG ν g hg hpg
        have hcore : ∀ k a b, 0 ≤ a → 0 ≤ b → ψ k 0 * ψ k (a + b) ≤ ψ k a * ψ k b :=
          fun k a b ha hb => hcomp _ (hcdf_mono k) (hcdf_nn k) (hcdf_le1 k) (hFk k) a b ha hb
        intro j
        have hae : ∀ᵐ a ∂μ, 0 ≤ a := by
          rw [ae_iff]; convert hμ using 2; ext; simp
        have hm : ∀ k, Measurable (ψ k) := fun k => (hψanti k).measurable
        have hbI : ∀ k (c : ℝ), Integrable (fun a => c * ψ k a) μ := by
          intro k c
          exact (Integrable.of_bound (hm k).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hψnn _ _)]; exact hψle1 _ _)).const_mul c
        have hbI' : ∀ k (a : ℝ), Integrable (fun b => ψ k (a + b)) μ := by
          intro k a
          exact Integrable.of_bound ((hm k).comp (by fun_prop)).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hψnn _ _)]; exact hψle1 _ _)
        rw [hP, hP, hP, hψstep (j+1), hψstep j]
        simp only [zero_add]
        simp_rw [hψstep j]
        rw [← integral_mul_const, ← integral_mul_const]
        have hinner : ∀ a, 0 ≤ a → (∫ b, ψ j (a + b) ∂μ) * ψ j 0 ≤ ψ j a * ∫ b, ψ j b ∂μ := by
          intro a ha
          rw [← integral_mul_const, ← integral_const_mul]
          refine integral_mono_ae ((hbI' j a).mul_const _) (by simpa using hbI j (ψ j a)) ?_
          filter_upwards [hae] with b hb
          have := hcore j a b ha hb
          linarith [mul_comm (ψ j 0) (ψ j (a + b))]
        have hA : Measurable (fun a => ∫ b, ψ j (a + b) ∂μ) := by
          refine Antitone.measurable (fun a a' haa => integral_mono (hbI' j a') (hbI' j a) (fun b => hψanti j (by linarith)))
        refine integral_mono_ae ?_ ?_ ?_
        · refine Integrable.of_bound (hA.mul_const _).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun a => ?_)
          have h1 : 0 ≤ ∫ b, ψ j (a + b) ∂μ := integral_nonneg fun b => hψnn _ _
          have h2 : ∫ b, ψ j (a + b) ∂μ ≤ 1 := by
            calc _ ≤ ∫ b, (1:ℝ) ∂μ := integral_mono (hbI' j a) (integrable_const _) (fun b => hψle1 _ _)
              _ = 1 := by simp
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 (hψnn _ _))]
          nlinarith [hψnn j 0, hψle1 j 0]
        · simpa [mul_comm] using hbI j (∫ b, ψ j b ∂μ)
        · filter_upwards [hae] with a ha
          exact hinner a ha
      have hpf2 : IsPF2SeqFrom 0 (ShockWear.RandThreshold.randP μ ν) := by
        intro j k _ hjk
        induction k, hjk using Nat.le_induction with
        | base => exact le_rfl
        | succ k hk ih =>
          set Q := ShockWear.RandThreshold.randP μ ν
          have h2 := hadj k
          rcases (hnn (k + 1)).lt_or_eq with hpos | hzero
          · have hk0 : 0 < Q k := lt_of_lt_of_le hpos (hanti (Nat.le_succ k))
            have e1 : Q (k + 1 + 1) = Q (k + 2) := rfl
            rw [e1]
            have a1 : Q (k + 2) * Q j * Q k ≤ Q (k + 1) * Q (k + 1) * Q j :=
              by nlinarith [hnn j, hnn (k+2)]
            have a2 : Q (k + 1) * Q (k + 1) * Q j ≤ Q (k + 1) * (Q (j + 1) * Q k) :=
              by nlinarith [hnn j]
            have a3 : Q (k + 2) * Q j * Q k ≤ Q (j + 1) * Q (k + 1) * Q k := by nlinarith
            exact le_of_mul_le_mul_right a3 hk0
          · have hz : Q (k + 1 + 1) = 0 := le_antisymm (hzero ▸ hanti (Nat.le_succ (k + 1))) (hnn _)
            rw [hz, zero_mul]; exact mul_nonneg (hnn _) (hnn _)
      have g21_pw_nonneg : ∀ (lam t : ℝ), 0 ≤ lam → 0 ≤ t → ∀ (k : ℕ), 0 ≤ ShockWear.RandThreshold.poisW lam t k := by
        intro lam t hlam ht k
        unfold ShockWear.RandThreshold.poisW
        have : 0 ≤ lam * t := mul_nonneg hlam ht
        positivity
      have g21_pw_summable : ∀ (lam t : ℝ), Summable (fun k => ShockWear.RandThreshold.poisW lam t k) := by
        intro lam t
        unfold ShockWear.RandThreshold.poisW
        have := (Real.summable_pow_div_factorial (lam * t)).mul_left (Real.exp (-(lam * t)))
        refine this.congr (fun k => ?_)
        ring
      have g21_pw_add : ∀ (lam t x : ℝ) (n : ℕ),
          ShockWear.RandThreshold.poisW lam (t + x) n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ShockWear.RandThreshold.poisW lam t p.1 * ShockWear.RandThreshold.poisW lam x p.2 := by
        intro lam t x n
        unfold ShockWear.RandThreshold.poisW
        have h1 : (lam * (t + x)) = lam * t + lam * x := by ring
        rw [h1, (Commute.all (lam * t) (lam * x)).add_pow', Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        obtain ⟨i, j⟩ := p
        simp only at hp ⊢
        subst hp
        have hc : ((i + j).choose i : ℝ) * (i.factorial : ℝ) * (j.factorial : ℝ) = ((i + j).factorial : ℝ) := by
          have := Nat.add_choose_mul_factorial_mul_factorial i j
          rw [Nat.choose_symm_add]
          exact_mod_cast this
        have hi : (i.factorial : ℝ) ≠ 0 := by positivity
        have hj : (j.factorial : ℝ) ≠ 0 := by positivity
        have hij : ((i + j).factorial : ℝ) ≠ 0 := by positivity
        rw [neg_add, Real.exp_add]
        rw [nsmul_eq_mul]
        rw [← hc]
        have hch : ((i + j).choose i : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.choose_pos (Nat.le_add_right i j)).ne'
        field_simp
      have g21_lc_pos : ∀ (q : ℕ → ℝ), (∀ k, 0 ≤ q k) →
          (∀ j k, j ≤ k → q (k + 1) * q j ≤ q (j + 1) * q k) →
          ∀ (a c : ℕ), 0 < q a → 0 < q c → ∀ m, a ≤ m → m ≤ c → 0 < q m := by
        intro q hnn hpf a c ha hc m ham hmc
        induction m, ham using Nat.le_induction with
        | base => exact ha
        | succ m hm ih =>
          have h := hpf m (c - 1) (by omega)
          have hc1 : c - 1 + 1 = c := by omega
          rw [hc1] at h
          have h0 : 0 < q c * q m := mul_pos hc (ih (by omega))
          have h2 : 0 < q (m + 1) * q (c - 1) := lt_of_lt_of_le h0 h
          rcases (hnn (m + 1)).lt_or_eq with h3 | h3
          · exact h3
          · rw [← h3] at h2; simp at h2
      have g21_lc_gen : ∀ (q : ℕ → ℝ), (∀ k, 0 ≤ q k) →
          (∀ j k, j ≤ k → q (k + 1) * q j ≤ q (j + 1) * q k) →
          ∀ (a b : ℕ), a ≤ b → ∀ (j : ℕ), q (b + j) * q a ≤ q (a + j) * q b := by
        intro q hnn hpf a b hab j
        rcases (hnn a).lt_or_eq with ha | ha
        swap
        · rw [← ha]; simp only [mul_zero]; exact mul_nonneg (hnn _) (hnn _)
        rcases (hnn (b + j)).lt_or_eq with hb | hb
        swap
        · rw [← hb]; simp only [zero_mul]; exact mul_nonneg (hnn _) (hnn _)
        have hpos := g21_lc_pos q hnn hpf a (b + j) ha hb
        have key : ∀ i, i ≤ j → q (b + i) * q a ≤ q (a + i) * q b := by
          intro i
          induction i with
          | zero => intro _; simp [mul_comm]
          | succ i ih =>
            intro hi
            have IH := ih (by omega)
            have h1 := hpf (a + i) (b + i) (by omega)
            have pa : 0 < q (a + i) := hpos _ (by omega) (by omega)
            have pb : 0 < q (b + i) := hpos _ (by omega) (by omega)
            have e1 : b + (i + 1) = b + i + 1 := by omega
            have e2 : a + (i + 1) = a + i + 1 := by omega
            rw [e1, e2]
            have hm := mul_le_mul h1 IH (mul_nonneg (hnn _) (hnn _)) (mul_nonneg (hnn _) (hnn _))
            have hp : 0 < q (a + i) * q (b + i) := mul_pos pa pb
            have h3 : (q (b + i + 1) * q a) * (q (a + i) * q (b + i))
                ≤ (q (a + i + 1) * q b) * (q (a + i) * q (b + i)) := by linear_combination hm
            exact le_of_mul_le_mul_right h3 hp
        exact key j le_rfl
      have g21_pow_cross : ∀ (u v : ℝ), 0 ≤ u → u ≤ v → ∀ (a b : ℕ), a ≤ b →
          v ^ a * u ^ b ≤ u ^ a * v ^ b := by
        intro u v hu huv a b hab
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
        rw [pow_add, pow_add]
        have hv : 0 ≤ v := hu.trans huv
        have h1 : u ^ d ≤ v ^ d := pow_le_pow_left₀ hu huv d
        have h2 : 0 ≤ v ^ a * u ^ a := by positivity
        calc v ^ a * (u ^ a * u ^ d) = (v ^ a * u ^ a) * u ^ d := by ring
          _ ≤ (v ^ a * u ^ a) * v ^ d := mul_le_mul_of_nonneg_left h1 h2
          _ = u ^ a * (v ^ a * v ^ d) := by ring
      have g21_w_cross : ∀ (lam s t : ℝ), 0 ≤ lam → 0 ≤ s → s ≤ t → ∀ (a b : ℕ), a ≤ b →
          ShockWear.RandThreshold.poisW lam t a * ShockWear.RandThreshold.poisW lam s b ≤ ShockWear.RandThreshold.poisW lam s a * ShockWear.RandThreshold.poisW lam t b := by
        intro lam s t hlam hs hst a b hab
        unfold ShockWear.RandThreshold.poisW
        have hc := g21_pow_cross (lam * s) (lam * t) (mul_nonneg hlam hs)
          (mul_le_mul_of_nonneg_left hst hlam) a b hab
        have hC : 0 ≤ Real.exp (-(lam * t)) * Real.exp (-(lam * s)) / ((a.factorial : ℝ) * (b.factorial : ℝ)) := by
          positivity
        calc Real.exp (-(lam * t)) * (lam * t) ^ a / (a.factorial : ℝ) *
              (Real.exp (-(lam * s)) * (lam * s) ^ b / (b.factorial : ℝ))
            = (Real.exp (-(lam * t)) * Real.exp (-(lam * s)) / ((a.factorial : ℝ) * (b.factorial : ℝ))) *
                ((lam * t) ^ a * (lam * s) ^ b) := by ring
          _ ≤ (Real.exp (-(lam * t)) * Real.exp (-(lam * s)) / ((a.factorial : ℝ) * (b.factorial : ℝ))) *
                ((lam * s) ^ a * (lam * t) ^ b) := mul_le_mul_of_nonneg_left hc hC
          _ = Real.exp (-(lam * s)) * (lam * s) ^ a / (a.factorial : ℝ) *
              (Real.exp (-(lam * t)) * (lam * t) ^ b / (b.factorial : ℝ)) := by ring
      have g21_norm_summable : ∀ {f : ℕ → ℝ}, Summable f → Summable (fun k => ‖f k‖) := by
        intro f hf
        simpa only [Real.norm_eq_abs] using hf.abs
      have g21_term_summable : ∀ (lam t : ℝ), 0 ≤ lam → 0 ≤ t → ∀ (r : ℕ → ℝ),
          (∀ k, 0 ≤ r k) → (∀ k, r k ≤ 1) → Summable (fun k => r k * ShockWear.RandThreshold.poisW lam t k) := by
        intro lam t hlam ht r hr0 hr1
        exact Summable.of_nonneg_of_le (fun k => mul_nonneg (hr0 k) (g21_pw_nonneg lam t hlam ht k))
          (fun k => by simpa using mul_le_mul_of_nonneg_right (hr1 k) (g21_pw_nonneg lam t hlam ht k))
          (g21_pw_summable lam t)
      have g21_symm_le : ∀ (A B : ℕ × ℕ → ℝ), Summable A → Summable B →
          (∀ z : ℕ × ℕ, A z + A z.swap ≤ B z + B z.swap) → ∑' z, A z ≤ ∑' z, B z := by
        intro A B hA hB hpt
        have hAs : ∑' z, A z = ∑' z : ℕ × ℕ, A z.swap := ((Equiv.prodComm ℕ ℕ).tsum_eq A).symm
        have hBs : ∑' z, B z = ∑' z : ℕ × ℕ, B z.swap := ((Equiv.prodComm ℕ ℕ).tsum_eq B).symm
        have hA2 : ∑' z : ℕ × ℕ, (A z + A z.swap) = 2 * ∑' z, A z := by
          rw [hA.tsum_add hA.prod_symm, ← hAs]; ring
        have hB2 : ∑' z : ℕ × ℕ, (B z + B z.swap) = 2 * ∑' z, B z := by
          rw [hB.tsum_add hB.prod_symm, ← hBs]; ring
        have hle : ∑' z : ℕ × ℕ, (A z + A z.swap) ≤ ∑' z : ℕ × ℕ, (B z + B z.swap) :=
          Summable.tsum_le_tsum hpt (hA.add hA.prod_symm) (hB.add hB.prod_symm)
        linarith
      have g21_pt : ∀ (lam : ℝ), 0 ≤ lam → ∀ (q : ℕ → ℝ), (∀ k, 0 ≤ q k) →
          (∀ j k, j ≤ k → q (k + 1) * q j ≤ q (j + 1) * q k) →
          ∀ (j : ℕ) (s t : ℝ), 0 ≤ s → s ≤ t → ∀ (a b : ℕ),
          q (j + a) * ShockWear.RandThreshold.poisW lam t a * (q b * ShockWear.RandThreshold.poisW lam s b) +
              q (j + b) * ShockWear.RandThreshold.poisW lam t b * (q a * ShockWear.RandThreshold.poisW lam s a) ≤
          q (j + a) * ShockWear.RandThreshold.poisW lam s a * (q b * ShockWear.RandThreshold.poisW lam t b) +
              q (j + b) * ShockWear.RandThreshold.poisW lam s b * (q a * ShockWear.RandThreshold.poisW lam t a) := by
        intro lam hlam q hnn hpf j s t hs hst a b
        have hid : (q (j + a) * ShockWear.RandThreshold.poisW lam s a * (q b * ShockWear.RandThreshold.poisW lam t b) +
            q (j + b) * ShockWear.RandThreshold.poisW lam s b * (q a * ShockWear.RandThreshold.poisW lam t a)) -
            (q (j + a) * ShockWear.RandThreshold.poisW lam t a * (q b * ShockWear.RandThreshold.poisW lam s b) +
            q (j + b) * ShockWear.RandThreshold.poisW lam t b * (q a * ShockWear.RandThreshold.poisW lam s a)) =
            (q (j + a) * q b - q (j + b) * q a) *
              (ShockWear.RandThreshold.poisW lam s a * ShockWear.RandThreshold.poisW lam t b - ShockWear.RandThreshold.poisW lam t a * ShockWear.RandThreshold.poisW lam s b) := by ring
        have hprod : 0 ≤ (q (j + a) * q b - q (j + b) * q a) *
              (ShockWear.RandThreshold.poisW lam s a * ShockWear.RandThreshold.poisW lam t b - ShockWear.RandThreshold.poisW lam t a * ShockWear.RandThreshold.poisW lam s b) := by
          rcases le_total a b with hab | hab
          · have h1 := g21_lc_gen q hnn hpf a b hab j
            have h2 := g21_w_cross lam s t hlam hs hst a b hab
            rw [add_comm b j, add_comm a j] at h1
            exact mul_nonneg (by linarith) (by linarith)
          · have h1 := g21_lc_gen q hnn hpf b a hab j
            have h2 := g21_w_cross lam s t hlam hs hst b a hab
            rw [add_comm b j, add_comm a j] at h1
            exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
        linarith
      have g21_H_cross : ∀ (lam : ℝ), 0 ≤ lam → ∀ (q : ℕ → ℝ), (∀ k, 0 ≤ q k) →
          (∀ k, q k ≤ 1) →
          (∀ j k, j ≤ k → q (k + 1) * q j ≤ q (j + 1) * q k) →
          ∀ (j : ℕ) (s t : ℝ), 0 ≤ s → s ≤ t →
          (∑' i, q (j + i) * ShockWear.RandThreshold.poisW lam t i) * (∑' b, q b * ShockWear.RandThreshold.poisW lam s b) ≤
            (∑' i, q (j + i) * ShockWear.RandThreshold.poisW lam s i) * (∑' b, q b * ShockWear.RandThreshold.poisW lam t b) := by
        intro lam hlam q hnn hq1 hpf j s t hs hst
        have ht : 0 ≤ t := hs.trans hst
        have hr0 : ∀ k, 0 ≤ q (j + k) := fun k => hnn _
        have hr1 : ∀ k, q (j + k) ≤ 1 := fun k => hq1 _
        have sf1 := g21_term_summable lam t hlam ht (fun k => q (j + k)) hr0 hr1
        have sg1 := g21_term_summable lam s hlam hs _ hnn hq1
        have sf2 := g21_term_summable lam s hlam hs (fun k => q (j + k)) hr0 hr1
        have sg2 := g21_term_summable lam t hlam ht _ hnn hq1
        have e1 : (∑' i, q (j + i) * ShockWear.RandThreshold.poisW lam t i) * (∑' b, q b * ShockWear.RandThreshold.poisW lam s b) =
            ∑' z : ℕ × ℕ, (q (j + z.1) * ShockWear.RandThreshold.poisW lam t z.1) * (q z.2 * ShockWear.RandThreshold.poisW lam s z.2) :=
          tsum_mul_tsum_of_summable_norm (g21_norm_summable sf1) (g21_norm_summable sg1)
        have e2 : (∑' i, q (j + i) * ShockWear.RandThreshold.poisW lam s i) * (∑' b, q b * ShockWear.RandThreshold.poisW lam t b) =
            ∑' z : ℕ × ℕ, (q (j + z.1) * ShockWear.RandThreshold.poisW lam s z.1) * (q z.2 * ShockWear.RandThreshold.poisW lam t z.2) :=
          tsum_mul_tsum_of_summable_norm (g21_norm_summable sf2) (g21_norm_summable sg2)
        have m1 : Summable (fun z : ℕ × ℕ => (q (j + z.1) * ShockWear.RandThreshold.poisW lam t z.1) * (q z.2 * ShockWear.RandThreshold.poisW lam s z.2)) :=
          summable_mul_of_summable_norm (f := fun i => q (j + i) * ShockWear.RandThreshold.poisW lam t i)
            (g := fun b => q b * ShockWear.RandThreshold.poisW lam s b) (g21_norm_summable sf1) (g21_norm_summable sg1)
        have m2 : Summable (fun z : ℕ × ℕ => (q (j + z.1) * ShockWear.RandThreshold.poisW lam s z.1) * (q z.2 * ShockWear.RandThreshold.poisW lam t z.2)) :=
          summable_mul_of_summable_norm (f := fun i => q (j + i) * ShockWear.RandThreshold.poisW lam s i)
            (g := fun b => q b * ShockWear.RandThreshold.poisW lam t b) (g21_norm_summable sf2) (g21_norm_summable sg2)
        rw [e1, e2]
        refine g21_symm_le _ _ m1 m2 ?_
        rintro ⟨a, b⟩
        exact g21_pt lam hlam q hnn hpf j s t hs hst a b
      have g21_shift : ∀ (lam : ℝ), 0 ≤ lam → ∀ (q : ℕ → ℝ), (∀ k, 0 ≤ q k) →
          (∀ k, q k ≤ 1) → ∀ (x t : ℝ), 0 ≤ x → 0 ≤ t →
          ∑' n, q n * ShockWear.RandThreshold.poisW lam (x + t) n = ∑' j, ShockWear.RandThreshold.poisW lam x j * (∑' i, q (j + i) * ShockWear.RandThreshold.poisW lam t i) := by
        intro lam hlam q hnn hq1 x t hx ht
        set g : ℕ × ℕ → ℝ := fun p => q (p.1 + p.2) * (ShockWear.RandThreshold.poisW lam x p.1 * ShockWear.RandThreshold.poisW lam t p.2) with hg
        have hprodS : Summable (fun p : ℕ × ℕ => ShockWear.RandThreshold.poisW lam x p.1 * ShockWear.RandThreshold.poisW lam t p.2) :=
          summable_mul_of_summable_norm (g21_norm_summable (g21_pw_summable lam x))
            (g21_norm_summable (g21_pw_summable lam t))
        have hgS : Summable g := by
          refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hprodS
          · exact mul_nonneg (hnn _) (mul_nonneg (g21_pw_nonneg lam x hlam hx _) (g21_pw_nonneg lam t hlam ht _))
          · have := mul_nonneg (g21_pw_nonneg lam x hlam hx p.1) (g21_pw_nonneg lam t hlam ht p.2)
            simpa [hg] using mul_le_mul_of_nonneg_right (hq1 (p.1 + p.2)) this
        have h1 : ∑' n, q n * ShockWear.RandThreshold.poisW lam (x + t) n =
            ∑' n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, g kl := by
          congr 1; ext n
          rw [g21_pw_add, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p hp => ?_)
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
          simp only [hg, hp]
        have h2 : ∑' n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, g kl = ∑' p, g p := by
          conv_lhs => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
          rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq g]
          exact (((Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).summable_iff.mpr hgS).tsum_sigma'
            (fun n ↦ (hasSum_fintype _).summable)).symm
        rw [h1, h2, hgS.tsum_prod]
        congr 1; ext j
        rw [← tsum_mul_left]
        congr 1; ext i
        simp only [hg]; ring
      have g21_H_le : ∀ (lam : ℝ), 0 ≤ lam → ∀ (q : ℕ → ℝ), (∀ k, 0 ≤ q k) →
          (∀ k, q k ≤ 1) → ∀ (j : ℕ) (t : ℝ), 0 ≤ t →
          0 ≤ (∑' i, q (j + i) * ShockWear.RandThreshold.poisW lam t i) ∧ (∑' i, q (j + i) * ShockWear.RandThreshold.poisW lam t i) ≤ ∑' i, ShockWear.RandThreshold.poisW lam t i := by
        intro lam hlam q hnn hq1 j t ht
        constructor
        · exact tsum_nonneg (fun i => mul_nonneg (hnn _) (g21_pw_nonneg lam t hlam ht i))
        · refine Summable.tsum_le_tsum (fun i => ?_)
            (g21_term_summable lam t hlam ht _ (fun k => hnn _) (fun k => hq1 _)) (g21_pw_summable lam t)
          simpa using mul_le_mul_of_nonneg_right (hq1 (j + i)) (g21_pw_nonneg lam t hlam ht i)
      have g21_core : ∀ (lam : ℝ), 0 ≤ lam → ∀ (q : ℕ → ℝ), (∀ k, 0 ≤ q k) →
          (∀ k, q k ≤ 1) →
          (∀ j k, j ≤ k → q (k + 1) * q j ≤ q (j + 1) * q k) →
          ∀ (x s t : ℝ), 0 ≤ x → 0 ≤ s → s ≤ t →
          (∑' n, q n * ShockWear.RandThreshold.poisW lam (x + t) n) * (∑' n, q n * ShockWear.RandThreshold.poisW lam s n) ≤
            (∑' n, q n * ShockWear.RandThreshold.poisW lam (x + s) n) * (∑' n, q n * ShockWear.RandThreshold.poisW lam t n) := by
        intro lam hlam q hnn hq1 hpf x s t hx hs hst
        have ht : 0 ≤ t := hs.trans hst
        rw [g21_shift lam hlam q hnn hq1 x t hx ht, g21_shift lam hlam q hnn hq1 x s hx hs,
          ← tsum_mul_right, ← tsum_mul_right]
        set S := ∑' n, q n * ShockWear.RandThreshold.poisW lam s n
        set T := ∑' n, q n * ShockWear.RandThreshold.poisW lam t n
        have hS0 : 0 ≤ S := tsum_nonneg (fun i => mul_nonneg (hnn _) (g21_pw_nonneg lam s hlam hs i))
        have hT0 : 0 ≤ T := tsum_nonneg (fun i => mul_nonneg (hnn _) (g21_pw_nonneg lam t hlam ht i))
        have sumL : Summable (fun j => ShockWear.RandThreshold.poisW lam x j * (∑' i, q (j + i) * ShockWear.RandThreshold.poisW lam t i) * S) := by
          refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
            (((g21_pw_summable lam x).mul_right (∑' i, ShockWear.RandThreshold.poisW lam t i)).mul_right S)
          · exact mul_nonneg (mul_nonneg (g21_pw_nonneg lam x hlam hx j)
              (g21_H_le lam hlam q hnn hq1 j t ht).1) hS0
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (g21_H_le lam hlam q hnn hq1 j t ht).2 (g21_pw_nonneg lam x hlam hx j)) hS0
        have sumR : Summable (fun j => ShockWear.RandThreshold.poisW lam x j * (∑' i, q (j + i) * ShockWear.RandThreshold.poisW lam s i) * T) := by
          refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
            (((g21_pw_summable lam x).mul_right (∑' i, ShockWear.RandThreshold.poisW lam s i)).mul_right T)
          · exact mul_nonneg (mul_nonneg (g21_pw_nonneg lam x hlam hx j)
              (g21_H_le lam hlam q hnn hq1 j s hs).1) hT0
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (g21_H_le lam hlam q hnn hq1 j s hs).2 (g21_pw_nonneg lam x hlam hx j)) hT0
        refine Summable.tsum_le_tsum (fun j => ?_) sumL sumR
        have := g21_H_cross lam hlam q hnn hq1 hpf j s t hs hst
        have hw := g21_pw_nonneg lam x hlam hx j
        calc ShockWear.RandThreshold.poisW lam x j * (∑' i, q (j + i) * ShockWear.RandThreshold.poisW lam t i) * S
              = ShockWear.RandThreshold.poisW lam x j * ((∑' i, q (j + i) * ShockWear.RandThreshold.poisW lam t i) * S) := by ring
          _ ≤ ShockWear.RandThreshold.poisW lam x j * ((∑' i, q (j + i) * ShockWear.RandThreshold.poisW lam s i) * T) := mul_le_mul_of_nonneg_left this hw
          _ = ShockWear.RandThreshold.poisW lam x j * (∑' i, q (j + i) * ShockWear.RandThreshold.poisW lam s i) * T := by ring
      have ihr : ∀ (P : ℕ → ℝ), P 0 = 1 → Antitone P → (∀ k, 0 ≤ P k) → IsPF2SeqFrom 0 P →
          IsIHR (ShockWear.RandThreshold.shockSurv lam P) := by
        intro P hP0 hanti hnn hpf
        intro x hx s t hs hst
        have ht : 0 ≤ t := hs.trans hst
        have hP1 : ∀ k, P k ≤ 1 := fun k => hP0 ▸ hanti (Nat.zero_le k)
        have hpf' : ∀ j k, j ≤ k → P (k + 1) * P j ≤ P (j + 1) * P k :=
          fun j k hjk => hpf j k (Nat.zero_le j) hjk
        unfold ShockWear.RandThreshold.shockSurv
        rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
        exact g21_core lam hlam.le P hnn hP1 hpf' x s t hx.le hs hst
      exact ⟨hP0, hanti, hnn, hpf2, ihr _ hP0 hanti hnn hpf2⟩
