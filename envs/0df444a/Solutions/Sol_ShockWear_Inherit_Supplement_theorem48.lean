-- Prove2me | solution 1 for ShockWear.Inherit.Supplement.theorem48
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:44.988858+00:00
-- url     : https://prove2.me/submissions/1c79bb08-3e17-4321-8c40-ce17ec3c12f6

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model
import Definitions.Def_ShockWear_Inherit_Supplement_TotalPositivity
import Definitions.Def_ShockWear_Inherit_Supplement_Density

open ShockWear
open ShockWear.Inherit
open ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem solution (lam : ℝ) (hlam : 0 < lam)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (f : ℝ → ℝ) (hf : IsDensity μ f) (hpf : IsPF2Function f) (x : ℝ) :
    IsPF2SeqFrom 1 (failProb (fun k => ShockWear.CumDamage.cdfPow μ k x)) ∧
    IsPF2Dens (shockDens lam (fun k => ShockWear.CumDamage.cdfPow μ k x)) := by
      open Finset Nat in
      have hcore : ∀ (a : ℕ → ℝ), (∀ k, 0 ≤ a k) → (∀ k, a k ≤ 1) →
          (∀ n i j, n ≤ i → a (i+j) * a n ≤ a (n+j) * a i) →
          ∀ (X S T : ℝ), 0 ≤ X → 0 ≤ S → S ≤ T →
          (∑' k, a k * (X+T)^k / (k ! : ℝ)) * (∑' k, a k * S^k / (k ! : ℝ)) ≤
          (∑' k, a k * (X+S)^k / (k ! : ℝ)) * (∑' k, a k * T^k / (k ! : ℝ)) := by
        intro a ha0 ha1 hlc X S T hX hS hST
        have hdiag : ∀ F : ℕ × ℕ → ℝ, Summable F →
            ∑' p, F p = ∑' n, ∑ kl ∈ antidiagonal n, F kl := by
          intro F hF
          rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq F]
          have hs := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff (f := F)).mpr hF
          exact (hs.tsum_sigma' (fun n => (hasSum_fintype _).summable)).trans (by
            congr 1; ext n
            rw [← Finset.sum_finset_coe, tsum_fintype]
            rfl)
        have hT : 0 ≤ T := hS.trans hST
        have hnorm : ∀ (b : ℕ → ℝ), (∀ k, 0 ≤ b k) → (∀ k, b k ≤ 1) → ∀ v, 0 ≤ v →
            Summable (fun k => ‖b k * v^k / (k ! : ℝ)‖) := by
          intro b hb0 hb1 v hv
          refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
            (Real.summable_pow_div_factorial v)
          have hbk := hb0 k
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          have : b k * v^k ≤ 1 * v^k := mul_le_mul_of_nonneg_right (hb1 k) (by positivity)
          rw [one_mul] at this
          exact div_le_div_of_nonneg_right this (by positivity)
        have hsum : ∀ (b : ℕ → ℝ), (∀ k, 0 ≤ b k) → (∀ k, b k ≤ 1) → ∀ v, 0 ≤ v →
            Summable (fun k => b k * v^k / (k ! : ℝ)) := fun b hb0 hb1 v hv =>
          (hnorm b hb0 hb1 v hv).of_norm
        set Gf : ℝ → ℝ := fun v => ∑' k, a k * v^k / (k ! : ℝ) with hGf
        set Hf : ℕ → ℝ → ℝ := fun j v => ∑' i, a (j+i) * v^i / (i ! : ℝ) with hHf
        have hHf0 : ∀ j v, 0 ≤ v → 0 ≤ Hf j v := fun j v hv =>
          tsum_nonneg (fun i => by have := ha0 (j+i); positivity)
        have hHfle : ∀ j v, 0 ≤ v → Hf j v ≤ ∑' i, v^i / (i ! : ℝ) := fun j v hv =>
          Summable.tsum_le_tsum (fun i => by
            have : a (j+i) * v^i ≤ 1 * v^i := mul_le_mul_of_nonneg_right (ha1 _) (by positivity)
            rw [one_mul] at this
            exact div_le_div_of_nonneg_right this (by positivity))
            (hsum (fun i => a (j+i)) (fun i => ha0 _) (fun i => ha1 _) v hv)
            (Real.summable_pow_div_factorial v)
        -- (E) expansion
        have hE : ∀ Y V, 0 ≤ Y → 0 ≤ V → Gf (Y+V) = ∑' j, Y^j / (j ! : ℝ) * Hf j V := by
          intro Y V hY hV
          set F : ℕ × ℕ → ℝ := fun p => Y^p.1 / (p.1 ! : ℝ) * (a (p.1+p.2) * V^p.2 / (p.2 ! : ℝ))
            with hFdef
          have hF : Summable F := by
            have hprod : Summable (fun p : ℕ × ℕ => Y^p.1 / (p.1 ! : ℝ) * (V^p.2 / (p.2 ! : ℝ))) := by
              refine summable_mul_of_summable_norm (f := fun j : ℕ => Y^j / (j ! : ℝ))
                (g := fun i : ℕ => V^i / (i ! : ℝ)) ?_ ?_
              · simpa [Real.norm_eq_abs, abs_of_nonneg, hY, hV, div_nonneg, pow_nonneg] using
                  Real.summable_pow_div_factorial Y
              · simpa [Real.norm_eq_abs, abs_of_nonneg, hY, hV, div_nonneg, pow_nonneg] using
                  Real.summable_pow_div_factorial V
            refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hprod
            · have := ha0 (p.1+p.2); simp only [hFdef]; positivity
            · simp only [hFdef]
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have : a (p.1+p.2) * V^p.2 ≤ 1 * V^p.2 :=
                mul_le_mul_of_nonneg_right (ha1 _) (by positivity)
              rw [one_mul] at this
              exact div_le_div_of_nonneg_right this (by positivity)
          have h1 : ∑' p, F p = ∑' j, Y^j / (j ! : ℝ) * Hf j V := by
            rw [hF.tsum_prod]
            congr 1; ext j
            simp only [hFdef, hHf]
            rw [tsum_mul_left]
          rw [← h1, hdiag F hF]
          simp only [hGf]
          congr 1; ext n
          rw [(Commute.all Y V).add_pow' n, Finset.mul_sum, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro kl hkl
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
          simp only [hFdef]
          rw [hkl, nsmul_eq_mul]
          have hfac : ((n.choose kl.1 : ℕ) : ℝ) * (kl.1 ! : ℝ) * (kl.2 ! : ℝ) = (n ! : ℝ) := by
            rw [← hkl, Nat.choose_symm_add]; exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial kl.1 kl.2
          have h1' : (kl.1 ! : ℝ) ≠ 0 := by positivity
          have h2' : (kl.2 ! : ℝ) ≠ 0 := by positivity
          have h3' : ((n.choose kl.1 : ℕ) : ℝ) ≠ 0 := by
            have := Nat.choose_pos (n := n) (k := kl.1) (by omega)
            positivity
          rw [← hfac]
          field_simp
        have hpow : ∀ n d : ℕ, S^(n+d) * T^n ≤ T^(n+d) * S^n := by
          intro n d
          rw [pow_add, pow_add]
          have h1 : S^d ≤ T^d := pow_le_pow_left₀ hS hST d
          have h2 : 0 ≤ S^n * T^n := by positivity
          nlinarith
        have hC : ∀ j, Hf j T * Gf S ≤ Hf j S * Gf T := by
          intro j
          have hb0 : ∀ i, 0 ≤ a (j+i) := fun i => ha0 _
          have hb1 : ∀ i, a (j+i) ≤ 1 := fun i => ha1 _
          let u : ℕ × ℕ → ℝ := fun p => (a (j+p.1) * T^p.1 / (p.1 ! : ℝ)) *
            (a p.2 * S^p.2 / (p.2 ! : ℝ))
          let v : ℕ × ℕ → ℝ := fun p => (a (j+p.1) * S^p.1 / (p.1 ! : ℝ)) *
            (a p.2 * T^p.2 / (p.2 ! : ℝ))
          have hu1 : Hf j T * Gf S = ∑' p, u p :=
            tsum_mul_tsum_of_summable_norm (f := fun i => a (j+i) * T^i / (i ! : ℝ))
              (g := fun k => a k * S^k / (k ! : ℝ)) (hnorm _ hb0 hb1 T hT) (hnorm a ha0 ha1 S hS)
          have hv1 : Hf j S * Gf T = ∑' p, v p :=
            tsum_mul_tsum_of_summable_norm (f := fun i => a (j+i) * S^i / (i ! : ℝ))
              (g := fun k => a k * T^k / (k ! : ℝ)) (hnorm _ hb0 hb1 S hS) (hnorm a ha0 ha1 T hT)
          have hus : Summable u :=
            summable_mul_of_summable_norm (f := fun i => a (j+i) * T^i / (i ! : ℝ))
              (g := fun k => a k * S^k / (k ! : ℝ)) (hnorm _ hb0 hb1 T hT) (hnorm a ha0 ha1 S hS)
          have hvs : Summable v :=
            summable_mul_of_summable_norm (f := fun i => a (j+i) * S^i / (i ! : ℝ))
              (g := fun k => a k * T^k / (k ! : ℝ)) (hnorm _ hb0 hb1 S hS) (hnorm a ha0 ha1 T hT)
          let w : ℕ × ℕ → ℝ := fun p => u p - v p
          have hws : Summable w := hus.sub hvs
          have hwsum : ∑' p, w p = ∑' p, u p - ∑' p, v p := hus.tsum_sub hvs
          have hswap : ∑' p, w (Prod.swap p) = ∑' p, w p :=
            (Equiv.prodComm ℕ ℕ).tsum_eq w
          have hws' : Summable (fun p => w (Prod.swap p)) :=
            (Equiv.prodComm ℕ ℕ).summable_iff.mpr hws
          have hterm : ∀ p : ℕ × ℕ, w p + w (Prod.swap p) ≤ 0 := by
            rintro ⟨i, n⟩
            have heq : w (i, n) + w (Prod.swap (i, n)) =
                (a (j+i) * a n - a (j+n) * a i) * (T^i * S^n - S^i * T^n) /
                  ((i ! : ℝ) * (n ! : ℝ)) := by
              simp only [w, u, v, Prod.swap]
              have h1' : (i ! : ℝ) ≠ 0 := by positivity
              have h2' : (n ! : ℝ) ≠ 0 := by positivity
              field_simp
              ring
            rw [heq]
            apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
            rcases le_total n i with hni | hin
            · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hni
              have h1 := hlc n (n+d) j hni
              have h2 := hpow n d
              have e1 : a (j + (n+d)) = a (n + d + j) := by rw [add_comm]
              have e2 : a (j + n) = a (n + j) := by rw [add_comm]
              rw [e1, e2]
              apply mul_nonpos_of_nonpos_of_nonneg <;> nlinarith
            · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hin
              have h1 := hlc i (i+d) j hin
              have h2 := hpow i d
              have e1 : a (j + (i+d)) = a (i + d + j) := by rw [add_comm]
              have e2 : a (j + i) = a (i + j) := by rw [add_comm]
              rw [e1, e2]
              apply mul_nonpos_of_nonneg_of_nonpos <;> nlinarith
          have hneg : ∑' p, w p ≤ 0 := by
            have : ∑' p, (w p + w (Prod.swap p)) ≤ 0 := tsum_nonpos hterm
            rw [hws.tsum_add hws', hswap] at this
            linarith
          rw [hu1, hv1]; linarith
        -- assembly
        have hET := hE X T hX hT
        have hES := hE X S hX hS
        have hsumH : ∀ V, 0 ≤ V → Summable (fun j => X^j / (j ! : ℝ) * Hf j V) := by
          intro V hV
          refine Summable.of_nonneg_of_le (fun j => mul_nonneg (by positivity) (hHf0 j V hV))
            (fun j => mul_le_mul_of_nonneg_left (hHfle j V hV) (by positivity))
            ((Real.summable_pow_div_factorial X).mul_right _)
        show Gf (X+T) * Gf S ≤ Gf (X+S) * Gf T
        rw [hET, hES, ← tsum_mul_right, ← tsum_mul_right]
        refine Summable.tsum_le_tsum (fun j => ?_) ((hsumH T hT).mul_right _) ((hsumH S hS).mul_right _)
        have := hC j
        have hXj : 0 ≤ X^j / (j ! : ℝ) := by positivity
        nlinarith
      set P : ℕ → ℝ := fun k => ShockWear.CumDamage.cdfPow μ k x with hP
      have hA : (∀ k, 0 ≤ failProb P (k+1)) ∧ (∀ k, failProb P (k+1) ≤ 1) ∧
          IsPF2SeqFrom 1 (failProb P) := by
        have hprob : ∀ k, IsProbabilityMeasure (ShockWear.CumDamage.convPow μ k) := by
          intro k
          induction k with
          | zero => simp only [ShockWear.CumDamage.convPow]; infer_instance
          | succ k ih => simp only [ShockWear.CumDamage.convPow]; infer_instance
        have hmono : ∀ k, ShockWear.CumDamage.convPow μ (k+1) (Set.Iic x) ≤
            ShockWear.CumDamage.convPow μ k (Set.Iic x) := by
          intro k
          have := hprob k
          show Measure.conv (ShockWear.CumDamage.convPow μ k) μ (Set.Iic x) ≤ _
          rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Iic]
          calc ((ShockWear.CumDamage.convPow μ k).prod μ) ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Set.Iic x)
              ≤ ((ShockWear.CumDamage.convPow μ k).prod μ)
                  (Set.Iic x ×ˢ Set.univ ∪ Set.univ ×ˢ Set.Iio 0) := by
                apply measure_mono
                intro p hp
                simp only [Set.mem_preimage, Set.mem_Iic] at hp
                by_cases h : p.2 < 0
                · right; exact ⟨trivial, h⟩
                · left; exact ⟨by simp only [Set.mem_Iic]; linarith [not_lt.mp h], trivial⟩
            _ ≤ _ := measure_union_le _ _
            _ = ShockWear.CumDamage.convPow μ k (Set.Iic x) := by
                rw [Measure.prod_prod, Measure.prod_prod, hμ]; simp
        have hle : ∀ k, ShockWear.CumDamage.cdfPow μ (k+1) x ≤ ShockWear.CumDamage.cdfPow μ k x := by
          intro k
          have := hprob k
          exact ENNReal.toReal_mono (measure_ne_top _ _) (hmono k)
        have hle1 : ∀ k, ShockWear.CumDamage.cdfPow μ k x ≤ 1 := by
          intro k
          have := hprob k
          unfold ShockWear.CumDamage.cdfPow
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
        have hnn : ∀ k, 0 ≤ ShockWear.CumDamage.cdfPow μ k x := fun k => ENNReal.toReal_nonneg
        refine ⟨fun k => ?_, fun k => ?_, ?_⟩
        · show 0 ≤ P k - P (k+1)
          have := hle k; simp only [hP]; linarith
        · show P k - P (k+1) ≤ 1
          have := hle1 k; have := hnn (k+1); simp only [hP]; linarith
        · have hprob : ∀ k, IsProbabilityMeasure (ShockWear.CumDamage.convPow μ k) := by
            intro k
            induction k with
            | zero => simp only [ShockWear.CumDamage.convPow]; infer_instance
            | succ k ih => simp only [ShockWear.CumDamage.convPow]; infer_instance
          obtain ⟨G, hGdef⟩ : ∃ G : ℕ → ℝ → ℝ≥0∞,
              G = fun k y => ShockWear.CumDamage.convPow μ k (Set.Iic y) := ⟨_, rfl⟩
          have hconv : ∀ k y, G (k+1) y = ∫⁻ v, G k (y - v) ∂μ := by
            intro k x
            have := hprob k
            simp only [hGdef, ShockWear.CumDamage.convPow]
            rw [← lintegral_indicator_one measurableSet_Iic, Measure.lintegral_conv]
            · rw [lintegral_lintegral_swap]
              · congr 1; funext y
                rw [← lintegral_indicator_one measurableSet_Iic]
                congr 1; funext a
                simp only [Set.indicator, Set.mem_Iic, Pi.one_apply]
                congr 1; apply propext; constructor <;> intro h <;> linarith
              · exact ((measurable_one.indicator measurableSet_Iic).comp measurable_add).aemeasurable
            · exact measurable_one.indicator measurableSet_Iic
          have hae : ∀ᵐ y ∂μ, 0 ≤ y := by
            rw [ae_iff]
            have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext a; simp
            rw [this, hμ]
          have hfin : ∀ k y, G k y ≠ ⊤ := by
            intro k y; have := hprob k; rw [hGdef]; exact measure_ne_top _ _
          have hG1 : ∀ k y, G k y ≤ 1 := by
            intro k y; have := hprob k; rw [hGdef]; exact prob_le_one
          have hGle : ∀ k y, G (k+1) y ≤ G k y := by
            intro k y
            rw [hconv]
            calc ∫⁻ v, G k (y - v) ∂μ ≤ ∫⁻ _v, G k y ∂μ := by
                  apply lintegral_mono_ae
                  filter_upwards [hae] with v hv
                  rw [hGdef]
                  exact measure_mono (Set.Iic_subset_Iic.mpr (by linarith))
              _ = _ := by simp
          have hGmeas : ∀ k, Measurable (G k) := fun k =>
            (show Monotone (G k) from fun a b hab => by
              rw [hGdef]; exact measure_mono (Set.Iic_subset_Iic.mpr hab)).measurable
          have hG0 : ∀ z, G 0 z = if 0 ≤ z then 1 else 0 := by
            intro z
            simp [hGdef, ShockWear.CumDamage.convPow, Measure.dirac_apply' _ measurableSet_Iic,
              Set.indicator]
          have hGneg : ∀ k y, y < 0 → G k y = 0 := by
            intro k y hy
            induction k with
            | zero => rw [hG0, if_neg (not_le.mpr hy)]
            | succ k ih => exact le_antisymm ((hGle k y).trans ih.le) bot_le
          obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ → ℝ → ℝ≥0∞, Q = fun k y => G k y - G (k+1) y := ⟨_, rfl⟩
          have hQmeas : ∀ k, Measurable (Q k) := fun k => by
            rw [hQdef]; exact (hGmeas k).sub (hGmeas (k+1))
          have hQneg : ∀ k y, y < 0 → Q k y = 0 := by
            intro k y hy; rw [hQdef]; simp only [hGneg k y hy, zero_tsub]
          have hQfin : ∀ k y, Q k y ≠ ⊤ := by
            intro k y; rw [hQdef]; exact ne_top_of_le_ne_top (hfin k y) tsub_le_self
          have hsub : ∀ (g : ℝ → ℝ≥0∞), Measurable g → ∀ y : ℝ, Measurable (fun v : ℝ => g (y - v)) :=
            fun g hg y => hg.comp (measurable_const.sub measurable_id)
          have hQrec : ∀ k y, Q (k+1) y = ∫⁻ v, Q k (y - v) ∂μ := by
            intro k y
            rw [hQdef]
            simp only
            rw [hconv k y, hconv (k+1) y, lintegral_sub (hsub _ (hGmeas (k+1)) y) (by rw [← hconv]; exact hfin _ _)
              (Filter.Eventually.of_forall (fun v => hGle k (y - v)))]
          obtain ⟨R0, hR0def⟩ : ∃ R0 : ℝ → ℝ≥0∞, R0 = fun z => 1 - G 0 z := ⟨_, rfl⟩
          have hR0meas : Measurable R0 := by rw [hR0def]; exact measurable_const.sub (hGmeas 0)
          have hQ0 : ∀ y, 0 ≤ y → Q 0 y = ∫⁻ v, R0 (y - v) ∂μ := by
            intro y hy
            rw [hQdef, hR0def]
            simp only
            rw [lintegral_sub (hsub _ (hGmeas 0) y)
              (by rw [← hconv]; exact hfin _ _)
              (Filter.Eventually.of_forall (fun v => hG1 0 (y - v))), lintegral_one, measure_univ,
              ← hconv 0 y, hG0 y, if_pos hy]
          obtain ⟨Fd, hFddef⟩ : ∃ Fd : ℝ → ℝ≥0∞, Fd = fun v => ENNReal.ofReal (f v) := ⟨_, rfl⟩
          have hFd : AEMeasurable Fd volume := by rw [hFddef]; exact hf.1.ennreal_ofReal
          have hrepr : ∀ g : ℝ → ℝ≥0∞, Measurable g → ∀ y,
              ∫⁻ v, g (y - v) ∂μ = ∫⁻ w, Fd (y - w) * g w := by
            intro g hg y
            have hμd : μ = volume.withDensity Fd := by rw [hFddef]; exact hf.2.2
            rw [hμd, lintegral_withDensity_eq_lintegral_mul₀ hFd
              (hsub g hg y).aemeasurable]
            rw [← lintegral_sub_left_eq_self (fun w => Fd (y - w) * g w) y]
            congr 1; funext v; simp
          have hK : ∀ w1 w2 : ℝ, w1 ≤ w2 → ∀ u1 u2 : ℝ, u1 ≤ u2 →
              Fd (w1 - u2) * Fd (w2 - u1) ≤ Fd (w1 - u1) * Fd (w2 - u2) := by
            intro w1 w2 hw u1 u2 hu
            rcases hw.lt_or_eq with hw | rfl
            · rcases hu.lt_or_eq with hu | rfl
              · have h := hpf 2 (by norm_num) le_rfl ![w1, w2] ![u1, u2] (fun _ => trivial)
                  (fun _ => trivial)
                  (Fin.strictMono_iff_lt_succ.mpr (fun i => by fin_cases i; simpa using hw))
                  (Fin.strictMono_iff_lt_succ.mpr (fun i => by fin_cases i; simpa using hu))
                simp [Matrix.det_fin_two] at h
                rw [hFddef]
                simp only
                rw [← ENNReal.ofReal_mul (hf.2.1 _), ← ENNReal.ofReal_mul (hf.2.1 _)]
                exact ENNReal.ofReal_le_ofReal (by linarith)
              · exact le_rfl
            · exact le_of_eq (mul_comm _ _)
          have hkey : ∀ α β γ δ : ℝ≥0∞, β ≤ α → δ ≤ γ → α*δ + β*γ ≤ α*γ + β*δ := by
            intro α β γ δ h1 h2
            obtain ⟨a, rfl⟩ := exists_add_of_le h1
            obtain ⟨c, rfl⟩ := exists_add_of_le h2
            calc (β + a) * δ + β * (δ + c) = (β*δ + β*c + a*δ + β*δ) := by ring
              _ ≤ (β*δ + β*c + a*δ + β*δ) + a*c := le_self_add
              _ = (β + a) * (δ + c) + β * δ := by ring
          have hBCF : ∀ K1 K2 L1 L2 : ℝ → ℝ≥0∞, AEMeasurable K1 → AEMeasurable K2 →
              AEMeasurable L1 → AEMeasurable L2 →
              (∀ u1 u2 : ℝ, u1 ≤ u2 → K1 u2 * K2 u1 ≤ K1 u1 * K2 u2) →
              (∀ u1 u2 : ℝ, u1 ≤ u2 → L2 u1 * L1 u2 ≤ L1 u1 * L2 u2) →
              (∫⁻ w, K1 w * L2 w) * (∫⁻ w, K2 w * L1 w) ≤
                (∫⁻ w, K2 w * L2 w) * (∫⁻ w, K1 w * L1 w) := by
            intro K1 K2 L1 L2 hK1 hK2 hL1 hL2 hKK hLL
            have m12 : AEMeasurable (fun w => K1 w * L2 w) := hK1.mul hL2
            have m21 : AEMeasurable (fun w => K2 w * L1 w) := hK2.mul hL1
            have m22 : AEMeasurable (fun w => K2 w * L2 w) := hK2.mul hL2
            have m11 : AEMeasurable (fun w => K1 w * L1 w) := hK1.mul hL1
            have e1 := (lintegral_prod_mul (μ := volume) (ν := volume) m12 m21).symm
            have e2 := (lintegral_prod_mul (μ := volume) (ν := volume) m21 m12).symm
            have e3 := (lintegral_prod_mul (μ := volume) (ν := volume) m22 m11).symm
            have e4 := (lintegral_prod_mul (μ := volume) (ν := volume) m11 m22).symm
            have hle : (∫⁻ w, K1 w * L2 w) * (∫⁻ w, K2 w * L1 w) +
                (∫⁻ w, K2 w * L1 w) * (∫⁻ w, K1 w * L2 w) ≤
                (∫⁻ w, K2 w * L2 w) * (∫⁻ w, K1 w * L1 w) +
                (∫⁻ w, K1 w * L1 w) * (∫⁻ w, K2 w * L2 w) := by
              have a1 : AEMeasurable (fun z : ℝ × ℝ => K1 z.1 * L2 z.1 * (K2 z.2 * L1 z.2))
                  (volume.prod volume) :=
                (m12.comp_fst (ν := volume)).mul (m21.comp_snd (μ := volume))
              have a2 : AEMeasurable (fun z : ℝ × ℝ => K2 z.1 * L2 z.1 * (K1 z.2 * L1 z.2))
                  (volume.prod volume) :=
                (m22.comp_fst (ν := volume)).mul (m11.comp_snd (μ := volume))
              rw [e1, e2, e3, e4, ← lintegral_add_left' a1, ← lintegral_add_left' a2]
              apply lintegral_mono
              rintro ⟨y, y'⟩
              simp only
              rcases le_total y y' with h | h
              · have := hkey (K1 y * K2 y') (K1 y' * K2 y) (L1 y * L2 y') (L2 y * L1 y')
                  (hKK y y' h) (hLL y y' h)
                calc K1 y * L2 y * (K2 y' * L1 y') + K2 y * L1 y * (K1 y' * L2 y')
                    = (K1 y * K2 y') * (L2 y * L1 y') + (K1 y' * K2 y) * (L1 y * L2 y') := by ring
                  _ ≤ _ := this
                  _ = _ := by ring
              · have := hkey (K1 y' * K2 y) (K1 y * K2 y') (L1 y' * L2 y) (L2 y' * L1 y)
                  (hKK y' y h) (hLL y' y h)
                calc K1 y * L2 y * (K2 y' * L1 y') + K2 y * L1 y * (K1 y' * L2 y')
                    = (K1 y' * K2 y) * (L2 y' * L1 y) + (K1 y * K2 y') * (L1 y' * L2 y) := by ring
                  _ ≤ _ := this
                  _ = _ := by ring
            rw [mul_comm (∫⁻ w, K2 w * L1 w), mul_comm (∫⁻ w, K1 w * L1 w), ← two_mul,
              ← two_mul] at hle
            exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).mp hle
          have hKm : ∀ w0 : ℝ, AEMeasurable (fun w => Fd (w0 - w)) volume := fun w0 =>
            hFd.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume w0)
          have hTP : ∀ n m, n ≤ m → ∀ w1 w2 : ℝ, w1 ≤ w2 → Q m w1 * Q n w2 ≤ Q m w2 * Q n w1 := by
            intro n
            induction n with
            | zero =>
              intro m hm w1 w2 hw
              rcases lt_or_ge w1 0 with h1 | h1
              · rw [hQneg m w1 h1, zero_mul]; exact bot_le
              cases m with
              | zero => exact le_of_eq (by ring)
              | succ m =>
                rw [hQrec m w1, hQrec m w2, hQ0 w2 (h1.trans hw), hQ0 w1 h1, hrepr _ (hQmeas m),
                  hrepr _ (hQmeas m), hrepr _ hR0meas, hrepr _ hR0meas]
                refine hBCF (fun w => Fd (w1 - w)) (fun w => Fd (w2 - w)) R0 (Q m) (hKm w1) (hKm w2)
                  hR0meas.aemeasurable (hQmeas m).aemeasurable (fun u1 u2 hu => hK w1 w2 hw u1 u2 hu) ?_
                intro u1 u2 hu
                by_cases hu2 : u2 < 0
                · rw [hQneg m u1 (lt_of_le_of_lt hu hu2), zero_mul]; exact bot_le
                · have : R0 u2 = 0 := by
                    rw [hR0def]; simp only; rw [hG0, if_pos (not_lt.mp hu2), tsub_self]
                  rw [this, mul_zero]; exact bot_le
            | succ n ih =>
              intro m hm w1 w2 hw
              obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              rcases lt_or_ge w1 0 with h1 | h1
              · rw [hQneg _ w1 h1, zero_mul]; exact bot_le
              rw [hQrec m w1, hQrec m w2, hQrec n w1, hQrec n w2, hrepr _ (hQmeas m),
                hrepr _ (hQmeas m), hrepr _ (hQmeas n), hrepr _ (hQmeas n)]
              exact hBCF (fun w => Fd (w1 - w)) (fun w => Fd (w2 - w)) (Q n) (Q m) (hKm w1) (hKm w2)
                (hQmeas n).aemeasurable (hQmeas m).aemeasurable (fun u1 u2 hu => hK w1 w2 hw u1 u2 hu)
                (fun u1 u2 hu => (ih m (by omega) u1 u2 hu).trans_eq (mul_comm _ _))
          have htr : ∀ i, failProb P (i+1) = (Q i x).toReal := by
            intro i
            show P i - P (i+1) = _
            rw [hQdef]
            simp only
            rw [ENNReal.toReal_sub_of_le (hGle i x) (hfin i x), hP, hGdef]
            rfl
          intro j k hj hjk
          obtain ⟨n, rfl⟩ : ∃ n, j = n+1 := ⟨j-1, by omega⟩
          obtain ⟨m, rfl⟩ : ∃ m, k = m+1 := ⟨k-1, by omega⟩
          rw [htr, htr, htr, htr]
          have hE : Q (m+1) x * Q n x ≤ Q (n+1) x * Q m x := by
            rw [hQrec m x, hQrec n x, ← lintegral_mul_const _ (hsub _ (hQmeas m) x),
              ← lintegral_mul_const _ (hsub _ (hQmeas n) x)]
            apply lintegral_mono_ae
            filter_upwards [hae] with v hv
            exact (hTP n m (by omega) (x - v) x (by linarith)).trans_eq (mul_comm _ _)
          rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul]
          exact ENNReal.toReal_mono (ENNReal.mul_ne_top (hQfin _ _) (hQfin _ _)) hE
      obtain ⟨hA0, hA1, hApf⟩ := hA
      refine ⟨hApf, ?_⟩
      set a : ℕ → ℝ := fun k => failProb P (k+1) with ha
      have hstep : ∀ n i, n ≤ i → a (i+1) * a n ≤ a (n+1) * a i := by
        intro n i hni
        exact hApf (n+1) (i+1) (by omega) (by omega)
      have ha0 : ∀ k, 0 ≤ a k := hA0
      have hz0 : ∀ m, 0 < a m → a (m+1) = 0 → ∀ q, m+1 ≤ q → a q = 0 := by
        intro m hm h1 q hq
        have := hstep m (q-1) (by omega)
        have e : q - 1 + 1 = q := by omega
        rw [e, h1, zero_mul] at this
        have hq0 := ha0 q
        rcases (mul_nonpos_iff.mp this) with ⟨_, h⟩ | ⟨h, _⟩
        · linarith
        · linarith
      have hz : ∀ d m, 0 < a m → a (m+d+1) = 0 → ∀ q, m+d+1 ≤ q → a q = 0 := by
        intro d
        induction d with
        | zero => intro m hm h1 q hq; exact hz0 m hm h1 q hq
        | succ d ih =>
          intro m hm h1 q hq
          rcases (ha0 (m+1)).lt_or_eq with hpos | hzero
          · exact ih (m+1) hpos (by rw [show m+1+d+1 = m+(d+1)+1 by omega]; exact h1) q (by omega)
          · exact hz0 m hm hzero.symm q (by omega)
      have hgen : ∀ n i j, n ≤ i → a (i+j) * a n ≤ a (n+j) * a i := by
        intro n i j hni
        induction j with
        | zero => simp [mul_comm]
        | succ j ih =>
          have g1 := hstep (n+j) (i+j) (by omega)
          rcases (ha0 (n+j)).lt_or_eq with hF | hF
          · have hA' := ha0 (i+j+1)
            have hC' := ha0 (n+j+1)
            have hB' := ha0 n
            have h3 : a (n+j) * (a (i+(j+1)) * a n) ≤ a (n+j) * (a (n+(j+1)) * a i) := by
              have e1 : i + (j+1) = i+j+1 := by omega
              have e2 : n + (j+1) = n+j+1 := by omega
              rw [e1, e2]
              calc a (n+j) * (a (i+j+1) * a n) = (a (i+j+1) * a (n+j)) * a n := by ring
                _ ≤ (a (n+j+1) * a (i+j)) * a n := mul_le_mul_of_nonneg_right g1 hB'
                _ = a (n+j+1) * (a (i+j) * a n) := by ring
                _ ≤ a (n+j+1) * (a (n+j) * a i) := mul_le_mul_of_nonneg_left ih hC'
                _ = a (n+j) * (a (n+j+1) * a i) := by ring
            exact le_of_mul_le_mul_left h3 hF
          · rcases (ha0 n).lt_or_eq with hB | hB
            · cases j with
              | zero => simp at hF; linarith
              | succ d =>
                have := hz d n hB (by rw [show n+d+1 = n+(d+1) by omega]; exact hF.symm)
                  (i + (d+1+1)) (by omega)
                rw [this, zero_mul]
                exact mul_nonneg (ha0 _) (ha0 _)
            · rw [← hB, mul_zero]
              exact mul_nonneg (ha0 _) (ha0 _)
      have hrepr : ∀ t, shockDens lam P t =
          lam * (Real.exp (-(lam * t)) * ∑' k, a k * (lam * t)^k / ((Nat.factorial k : ℕ) : ℝ)) := by
        intro t
        simp only [shockDens, ShockWear.CumDamage.poisW, ha]
        congr 1
        rw [← tsum_mul_left]
        exact tsum_congr (fun k => by ring)
      intro y hy s t hs hst
      rw [hrepr, hrepr, hrepr, hrepr]
      have hc := hcore a hA0 hA1 hgen (lam * y) (lam * s) (lam * t) (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hst hlam.le)
      have e1 : lam * (y + t) = lam * y + lam * t := by ring
      have e2 : lam * (y + s) = lam * y + lam * s := by ring
      rw [e1, e2]
      have hexp : Real.exp (-(lam * y + lam * t)) * Real.exp (-(lam * s)) =
          Real.exp (-(lam * y + lam * s)) * Real.exp (-(lam * t)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have hE0 : 0 ≤ Real.exp (-(lam * y + lam * t)) * Real.exp (-(lam * s)) := by positivity
      calc lam * (Real.exp (-(lam * y + lam * t)) * ∑' k, a k * (lam * y + lam * t)^k / ((Nat.factorial k : ℕ) : ℝ)) *
            (lam * (Real.exp (-(lam * s)) * ∑' k, a k * (lam * s)^k / ((Nat.factorial k : ℕ) : ℝ)))
          = lam^2 * (Real.exp (-(lam * y + lam * t)) * Real.exp (-(lam * s))) *
            ((∑' k, a k * (lam * y + lam * t)^k / ((Nat.factorial k : ℕ) : ℝ)) *
              (∑' k, a k * (lam * s)^k / ((Nat.factorial k : ℕ) : ℝ))) := by ring
        _ ≤ lam^2 * (Real.exp (-(lam * y + lam * t)) * Real.exp (-(lam * s))) *
            ((∑' k, a k * (lam * y + lam * s)^k / ((Nat.factorial k : ℕ) : ℝ)) *
              (∑' k, a k * (lam * t)^k / ((Nat.factorial k : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hc (by positivity)
        _ = _ := by rw [hexp]; ring
