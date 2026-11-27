-- Prove2me | solution 1 for ShockWear.Inherit.Supplement.theorem54
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:25:41.685386+00:00
-- url     : https://prove2.me/submissions/fa42e3e9-e1a4-4b7a-9be4-61c7eefc26c4

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
    (f g : ℝ → ℝ) (hf : IsDensity μ f) (hg : IsDensity ν g)
    (hpf : IsPF2Function f) (hpg : IsPF2Function g) :
    IsPF2SeqFrom 1 (failProb (ShockWear.RandThreshold.randP μ ν)) ∧
    IsPF2Dens (shockDens lam (ShockWear.RandThreshold.randP μ ν)) := by
      set P := ShockWear.RandThreshold.randP μ ν with hPdef
      -- generalized log-concavity from the one-step condition
      have hgen : ∀ q : ℕ → ℝ, (∀ k, 0 ≤ q k) →
          (∀ j k, j ≤ k → q (k+1) * q j ≤ q (j+1) * q k) →
          ∀ a m n, m ≤ n → q (n + a) * q m ≤ q (m + a) * q n := by
        intro q hq h1
        -- positivity on intervals
        have hint : ∀ d a, 0 < q a → 0 < q (a + d) → ∀ i, a ≤ i → i ≤ a + d → 0 < q i := by
          intro d
          induction d with
          | zero => intro a ha _ i h1 h2; have : i = a := by omega
                    subst this; exact ha
          | succ d ih =>
            intro a ha hb i hi1 hi2
            have hstep := h1 a (a + d) (by omega)
            have hprod : 0 < q (a+1) * q (a+d) := by
              have := mul_pos (show 0 < q (a + d + 1) from by simpa [add_assoc] using hb) ha
              linarith
            have ha1 : 0 < q (a+1) := by
              rcases (hq (a+1)).lt_or_eq with h | h
              · exact h
              · rw [← h] at hprod; simp at hprod
            rcases Nat.eq_or_lt_of_le hi1 with h | h
            · subst h; exact ha
            · exact ih (a+1) ha1 (by rw [show a + 1 + d = a + (d+1) by omega]; exact hb) i (by omega) (by omega)
        intro a
        induction a with
        | zero => intro m n _; simp [mul_comm]
        | succ a ih =>
          intro m n hmn
          rcases (hq m).lt_or_eq with hm | hm
          swap
          · rw [← hm]; simp; exact mul_nonneg (hq _) (hq _)
          rcases (hq (n + (a+1))).lt_or_eq with hn | hn
          swap
          · rw [← hn]; simp; exact mul_nonneg (hq _) (hq _)
          have hpos : ∀ i, m ≤ i → i ≤ n + (a+1) → 0 < q i := by
            intro i h1 h2
            exact hint (n + (a+1) - m) m hm (by rw [show m + (n + (a+1) - m) = n + (a+1) by omega]; exact hn) i h1 (by omega)
          have hA := ih m n hmn
          have hB := h1 (m + a) (n + a) (by omega)
          have p1 : 0 < q (m + a) := hpos _ (by omega) (by omega)
          have p2 : 0 < q (n + a) := hpos _ (by omega) (by omega)
          have := mul_le_mul hA hB (mul_nonneg (hq _) (hq _)) (mul_nonneg (hq _) (hq _))
          have key : (q (n + (a+1)) * q m) * (q (m+a) * q (n+a)) ≤ (q (m + (a+1)) * q n) * (q (m+a) * q (n+a)) := by
            rw [show n + (a+1) = n + a + 1 by omega, show m + (a+1) = m + a + 1 by omega]
            nlinarith [this]
          exact le_of_mul_le_mul_right key (mul_pos p1 p2)

      have hcore : ∀ q : ℕ → ℝ, (∀ k, 0 ≤ q k) → (∀ k, q k ≤ 1) →
          (∀ j k, j ≤ k → q (k+1) * q j ≤ q (j+1) * q k) →
          ∀ X S T : ℝ, 0 ≤ X → 0 ≤ S → S ≤ T →
          (∑' n, q n * ((X + T) ^ n / (n.factorial : ℝ))) * (∑' n, q n * (S ^ n / (n.factorial : ℝ))) ≤
          (∑' n, q n * ((X + S) ^ n / (n.factorial : ℝ))) * (∑' n, q n * (T ^ n / (n.factorial : ℝ))) := by
        intro q hq hq1 h1 X S T hX hS hST
        have hT : 0 ≤ T := le_trans hS hST
        have hg := hgen q hq h1
        have hE : ∀ v : ℝ, 0 ≤ v → ∀ n : ℕ, 0 ≤ v ^ n / (n.factorial : ℝ) := fun v hv n => by positivity
        have sumE : ∀ v : ℝ, 0 ≤ v → Summable (fun n : ℕ => q n * (v ^ n / (n.factorial : ℝ))) := by
          intro v hv
          refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hq n) (hE v hv n)) (fun n => ?_)
            (Real.summable_pow_div_factorial v)
          have := hE v hv n
          nlinarith [hq1 n]
        obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑' a : ℕ, X ^ a / (a.factorial : ℝ) := ⟨_, rfl⟩
        obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ, r = fun b => ∑' a : ℕ, q (a + b) * (X ^ a / (a.factorial : ℝ)) :=
          ⟨_, rfl⟩
        have sumRa : ∀ b, Summable (fun a : ℕ => q (a + b) * (X ^ a / (a.factorial : ℝ))) := by
          intro b
          refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hq _) (hE X hX n)) (fun n => ?_)
            (Real.summable_pow_div_factorial X)
          have := hE X hX n
          nlinarith [hq1 (n + b)]
        have hr0 : ∀ b, 0 ≤ r b := fun b => by
          rw [hr]; exact tsum_nonneg (fun a => mul_nonneg (hq _) (hE X hX a))
        have hr1 : ∀ b, r b ≤ M := by
          intro b
          rw [hr, hM]
          refine Summable.tsum_le_tsum (fun a => ?_) (sumRa b) (Real.summable_pow_div_factorial X)
          have := hE X hX a
          nlinarith [hq1 (a + b)]
        have sumR : ∀ v : ℝ, 0 ≤ v → Summable (fun b : ℕ => r b * (v ^ b / (b.factorial : ℝ))) := by
          intro v hv
          refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hr0 n) (hE v hv n)) (fun n => ?_)
            ((Real.summable_pow_div_factorial v).mul_left M)
          exact mul_le_mul_of_nonneg_right (hr1 n) (hE v hv n)
        have taylor : ∀ v : ℝ, 0 ≤ v →
            ∑' n, q n * ((X + v) ^ n / (n.factorial : ℝ)) = ∑' b, r b * (v ^ b / (b.factorial : ℝ)) := by
          intro v hv
          obtain ⟨G, hG⟩ : ∃ G : ℕ × ℕ → ℝ, G = fun p => q (p.2 + p.1) * (X ^ p.2 / (p.2.factorial : ℝ)) *
              (v ^ p.1 / (p.1.factorial : ℝ)) := ⟨_, rfl⟩
          have G0 : ∀ p, 0 ≤ G p := by
            intro p; rw [hG]; exact mul_nonneg (mul_nonneg (hq _) (hE X hX _)) (hE v hv _)
          have sG : Summable G := by
            have sP : Summable (fun p : ℕ × ℕ => (v ^ p.1 / (p.1.factorial : ℝ)) *
                (X ^ p.2 / (p.2.factorial : ℝ))) := by
              have h1 : Summable (fun a : ℕ => v ^ a / (a.factorial : ℝ)) :=
                Real.summable_pow_div_factorial v
              have h2 : Summable (fun a : ℕ => X ^ a / (a.factorial : ℝ)) :=
                Real.summable_pow_div_factorial X
              exact h1.mul_of_nonneg h2 (fun n => hE v hv n) (fun n => hE X hX n)
            refine Summable.of_nonneg_of_le G0 (fun p => ?_) sP
            rw [hG]; dsimp only
            have h1' := hE X hX p.2
            have h2' := hE v hv p.1
            have := hq1 (p.2 + p.1)
            have := hq (p.2 + p.1)
            nlinarith [mul_nonneg h1' h2']
          have e1 : ∑' b, r b * (v ^ b / (b.factorial : ℝ)) = ∑' p, G p := by
            rw [sG.tsum_prod' (fun b => sG.prod_factor b)]
            congr 1; funext b; rw [hr, hG]; dsimp only; rw [← tsum_mul_right]
          have e2 : ∑' p, G p = ∑' n, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, G p := by
            rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq G]
            have hs : Summable (fun c : (Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n) =>
                G (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd c)) :=
              (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).summable_iff.mpr sG
            rw [Summable.tsum_sigma' (fun n => (hasSum_fintype _).summable) hs]
            congr 1; funext n
            rw [tsum_fintype]
            exact Finset.sum_coe_sort _ _
          have e3 : ∀ n, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, G p = q n * ((X + v) ^ n / (n.factorial : ℝ)) := by
            intro n
            rw [add_comm X v, Commute.add_pow' (Commute.all v X), Finset.sum_div, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun p hp => ?_)
            rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
            obtain ⟨a, b⟩ := p
            dsimp only at hp
            subst hp
            rw [hG]; dsimp only
            rw [nsmul_eq_mul, add_comm a b]
            have hc : ((b + a).choose a : ℝ) * (b.factorial : ℝ) * (a.factorial : ℝ) = ((b + a).factorial : ℝ) := by
              exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial b a
            have hca : ((b + a).choose a : ℝ) = (Nat.choose (b + a) a : ℝ) := rfl
            rw [← hc]
            have hb : (0:ℝ) < (b.factorial : ℝ) := by positivity
            have ha : (0:ℝ) < (a.factorial : ℝ) := by positivity
            have hch : (0:ℝ) < ((b + a).choose a : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
            field_simp
          rw [e1, e2]; congr 1; funext n; rw [e3]
        have hrq : ∀ b c, b ≤ c → 0 ≤ r b * q c - r c * q b := by
          intro b c hbc
          have e : r b * q c - r c * q b =
              ∑' a : ℕ, (q (a + b) * q c - q (a + c) * q b) * (X ^ a / (a.factorial : ℝ)) := by
            rw [hr]
            dsimp only
            rw [← tsum_mul_right, ← tsum_mul_right,
              ← Summable.tsum_sub ((sumRa b).mul_right _) ((sumRa c).mul_right _)]
            congr 1; funext a; ring
          rw [e]
          refine tsum_nonneg (fun a => mul_nonneg ?_ (hE X hX a))
          have := hg a b c hbc
          rw [add_comm c a, add_comm b a] at this
          linarith
        have hST' : ∀ b c, b ≤ c → 0 ≤ S ^ b * T ^ c - T ^ b * S ^ c := by
          intro b c hbc
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hbc
          have : S ^ d ≤ T ^ d := pow_le_pow_left₀ hS hST d
          have h2 : S ^ b * T ^ (b + d) - T ^ b * S ^ (b + d) = (S ^ b * T ^ b) * (T ^ d - S ^ d) := by ring
          rw [h2]
          exact mul_nonneg (mul_nonneg (pow_nonneg hS _) (pow_nonneg hT _)) (by linarith)
        have hterm : ∀ b c, 0 ≤ (r b * q c - r c * q b) * (S ^ b * T ^ c - T ^ b * S ^ c) := by
          intro b c
          rcases le_total b c with h | h
          · exact mul_nonneg (hrq b c h) (hST' b c h)
          · have := mul_nonneg (hrq c b h) (hST' c b h)
            nlinarith [this]
        rw [taylor T hT, taylor S hS]
        obtain ⟨A, hA⟩ : ∃ A : ℕ × ℕ → ℝ, A = fun p => (r p.1 * (T ^ p.1 / (p.1.factorial : ℝ))) *
          (q p.2 * (S ^ p.2 / (p.2.factorial : ℝ))) := ⟨_, rfl⟩
        obtain ⟨B, hB⟩ : ∃ B : ℕ × ℕ → ℝ, B = fun p => (r p.1 * (S ^ p.1 / (p.1.factorial : ℝ))) *
          (q p.2 * (T ^ p.2 / (p.2.factorial : ℝ))) := ⟨_, rfl⟩
        have keyalg : ∀ (rb rc qb qc Sb Sc Tb Tc fb fc : ℝ), 0 < fb → 0 < fc →
            0 ≤ (rb*qc - rc*qb)*(Sb*Tc - Tb*Sc) →
            rb*(Tb/fb)*(qc*(Sc/fc)) + rc*(Tc/fc)*(qb*(Sb/fb)) ≤
              rb*(Sb/fb)*(qc*(Tc/fc)) + rc*(Sc/fc)*(qb*(Tb/fb)) := by
          intro rb rc qb qc Sb Sc Tb Tc fb fc hfb hfc h
          rw [← sub_nonneg]
          have e : rb*(Sb/fb)*(qc*(Tc/fc)) + rc*(Sc/fc)*(qb*(Tb/fb)) -
              (rb*(Tb/fb)*(qc*(Sc/fc)) + rc*(Tc/fc)*(qb*(Sb/fb))) =
              (rb*qc - rc*qb)*(Sb*Tc - Tb*Sc) / (fb*fc) := by
            field_simp; ring
          rw [e]; positivity
        have sA0 : Summable (fun p : ℕ × ℕ => (r p.1 * (T ^ p.1 / (p.1.factorial : ℝ))) *
            (q p.2 * (S ^ p.2 / (p.2.factorial : ℝ)))) :=
          Summable.mul_of_nonneg (f := fun b => r b * (T ^ b / (b.factorial : ℝ)))
            (g := fun n => q n * (S ^ n / (n.factorial : ℝ))) (sumR T hT) (sumE S hS)
            (fun n => mul_nonneg (hr0 n) (hE T hT n)) (fun n => mul_nonneg (hq n) (hE S hS n))
        have sB0 : Summable (fun p : ℕ × ℕ => (r p.1 * (S ^ p.1 / (p.1.factorial : ℝ))) *
            (q p.2 * (T ^ p.2 / (p.2.factorial : ℝ)))) :=
          Summable.mul_of_nonneg (f := fun b => r b * (S ^ b / (b.factorial : ℝ)))
            (g := fun n => q n * (T ^ n / (n.factorial : ℝ))) (sumR S hS) (sumE T hT)
            (fun n => mul_nonneg (hr0 n) (hE S hS n)) (fun n => mul_nonneg (hq n) (hE T hT n))
        have eA : (∑' b, r b * (T ^ b / (b.factorial : ℝ))) * (∑' n, q n * (S ^ n / (n.factorial : ℝ)))
            = ∑' p, A p := by
          rw [hA]; exact (sumR T hT).tsum_mul_tsum (sumE S hS) sA0
        have eB : (∑' b, r b * (S ^ b / (b.factorial : ℝ))) * (∑' n, q n * (T ^ n / (n.factorial : ℝ)))
            = ∑' p, B p := by
          rw [hB]; exact (sumR S hS).tsum_mul_tsum (sumE T hT) sB0
        have sA : Summable A := by rw [hA]; exact sA0
        have sB : Summable B := by rw [hB]; exact sB0
        have swA : ∑' p, A (Prod.swap p) = ∑' p, A p := (Equiv.prodComm ℕ ℕ).tsum_eq A
        have swB : ∑' p, B (Prod.swap p) = ∑' p, B p := (Equiv.prodComm ℕ ℕ).tsum_eq B
        have sA' : Summable (fun p => A (Prod.swap p)) := (Equiv.prodComm ℕ ℕ).summable_iff.mpr sA
        have sB' : Summable (fun p => B (Prod.swap p)) := (Equiv.prodComm ℕ ℕ).summable_iff.mpr sB
        have hle : ∑' p, (A p + A (Prod.swap p)) ≤ ∑' p, (B p + B (Prod.swap p)) := by
          refine Summable.tsum_le_tsum (fun p => ?_) (sA.add sA') (sB.add sB')
          obtain ⟨b, c⟩ := p
          have hb : (0:ℝ) < (b.factorial : ℝ) := by positivity
          have hc : (0:ℝ) < (c.factorial : ℝ) := by positivity
          rw [hA, hB]
          exact keyalg _ _ _ _ _ _ _ _ _ _ hb hc (hterm b c)
        rw [Summable.tsum_add sA sA', Summable.tsum_add sB sB', swA, swB] at hle
        rw [eA, eB]
        linarith
      have hprob : ∀ k, IsProbabilityMeasure (ShockWear.RandThreshold.convPow μ k) := by
        intro k
        induction k with
        | zero => simp only [ShockWear.RandThreshold.convPow]; infer_instance
        | succ k ih => simp only [ShockWear.RandThreshold.convPow]; infer_instance
      have hcdf : ∀ k x, 0 ≤ ShockWear.RandThreshold.cdfPow μ k x ∧
          ShockWear.RandThreshold.cdfPow μ k x ≤ 1 := by
        intro k x
        unfold ShockWear.RandThreshold.cdfPow
        refine ⟨ENNReal.toReal_nonneg, ?_⟩
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
      have hP01 : ∀ k, 0 ≤ P k ∧ P k ≤ 1 := by
        intro k
        refine ⟨integral_nonneg (fun x => (hcdf k x).1), ?_⟩
        have := integral_mono_of_nonneg (μ := ν) (f := fun x => ShockWear.RandThreshold.cdfPow μ k x)
          (g := fun _ => (1:ℝ)) (Filter.Eventually.of_forall (fun x => (hcdf k x).1))
          (integrable_const 1) (Filter.Eventually.of_forall (fun x => (hcdf k x).2))
        simpa [hPdef, ShockWear.RandThreshold.randP] using this
      have hmono : ∀ k x, ShockWear.RandThreshold.cdfPow μ (k+1) x ≤
          ShockWear.RandThreshold.cdfPow μ k x := by
        intro k x
        unfold ShockWear.RandThreshold.cdfPow
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        simp only [ShockWear.RandThreshold.convPow]
        rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Iic]
        calc (ShockWear.RandThreshold.convPow μ k).prod μ ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Set.Iic x)
            ≤ (ShockWear.RandThreshold.convPow μ k).prod μ
                (Set.Iic x ×ˢ Set.univ ∪ Set.univ ×ˢ Set.Iio 0) := by
              apply measure_mono
              intro p hp
              simp only [Set.mem_preimage, Set.mem_Iic] at hp
              simp only [Set.mem_union, Set.mem_prod, Set.mem_Iic, Set.mem_univ, and_true,
                Set.mem_Iio, true_and]
              by_contra h
              push Not at h
              linarith [h.1, h.2]
          _ ≤ (ShockWear.RandThreshold.convPow μ k).prod μ (Set.Iic x ×ˢ Set.univ) +
              (ShockWear.RandThreshold.convPow μ k).prod μ (Set.univ ×ˢ Set.Iio 0) := measure_union_le _ _
          _ = ShockWear.RandThreshold.convPow μ k (Set.Iic x) := by
              rw [Measure.prod_prod, Measure.prod_prod, hμ]; simp
      have hint : ∀ k, Integrable (fun x => ShockWear.RandThreshold.cdfPow μ k x) ν := by
        intro k
        have hm : Monotone (fun x => ShockWear.RandThreshold.cdfPow μ k x) := by
          intro a b hab
          unfold ShockWear.RandThreshold.cdfPow
          exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.mpr hab))
        refine (integrable_const (1:ℝ)).mono' hm.measurable.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun x => ?_))
        rw [Real.norm_eq_abs, abs_of_nonneg (hcdf k x).1]; exact (hcdf k x).2
      have hP1 : IsPF2SeqFrom 1 (failProb P) := by
        obtain ⟨G, hGdef⟩ : ∃ G : ℕ → ℝ → ℝ≥0∞,
            G = fun k y => ShockWear.RandThreshold.convPow μ k (Set.Iic y) := ⟨_, rfl⟩
        have hconv : ∀ k y, G (k+1) y = ∫⁻ v, G k (y - v) ∂μ := by
          intro k x
          have := hprob k
          simp only [hGdef, ShockWear.RandThreshold.convPow]
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
          simp [hGdef, ShockWear.RandThreshold.convPow, Measure.dirac_apply' _ measurableSet_Iic,
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
        have hKg : ∀ w1 w2 : ℝ, w1 ≤ w2 → ∀ y1 y2 : ℝ, y1 ≤ y2 →
            g (w1 - y2) * g (w2 - y1) ≤ g (w1 - y1) * g (w2 - y2) := by
          intro w1 w2 hw u1 u2 hu
          rcases hw.lt_or_eq with hw | rfl
          · rcases hu.lt_or_eq with hu | rfl
            · have h := hpg 2 (by norm_num) le_rfl ![w1, w2] ![u1, u2] (fun _ => trivial)
                (fun _ => trivial)
                (Fin.strictMono_iff_lt_succ.mpr (fun i => by fin_cases i; simpa using hw))
                (Fin.strictMono_iff_lt_succ.mpr (fun i => by fin_cases i; simpa using hu))
              simp [Matrix.det_fin_two] at h
              linarith
            · exact le_rfl
          · exact le_of_eq (mul_comm _ _)
        obtain ⟨Gd, hGddef⟩ : ∃ Gd : ℝ → ℝ≥0∞, Gd = fun v => ENNReal.ofReal (g v) := ⟨_, rfl⟩
        have hGd : AEMeasurable Gd volume := by rw [hGddef]; exact hg.1.ennreal_ofReal
        have hGdtop : ∀ x, Gd x ≠ ⊤ := fun x => by rw [hGddef]; exact ENNReal.ofReal_ne_top
        have hνd : ν = volume.withDensity Gd := by rw [hGddef]; exact hg.2.2
        have hμd : μ = volume.withDensity Fd := by rw [hFddef]; exact hf.2.2
        obtain ⟨h, hhdef⟩ : ∃ h : ℝ → ℝ≥0∞, h = fun u => ∫⁻ x, Gd x * Fd (x - u) := ⟨_, rfl⟩
        have hhm : AEMeasurable h volume := by
          rw [hhdef]
          refine AEMeasurable.lintegral_prod_right' (μ := volume) (ν := volume)
            (f := fun p : ℝ × ℝ => Gd p.2 * Fd (p.2 - p.1)) ?_
          refine (hGd.comp_snd).mul ?_
          have := hFd.comp_quasiMeasurePreserving
            (quasiMeasurePreserving_neg_add (volume : Measure ℝ) (volume : Measure ℝ))
          convert this using 1
          funext p; simp [neg_add_eq_sub]
        have hh2 : ∀ u, h u = ∫⁻ v, Gd (u + v) ∂μ := by
          intro u
          rw [hμd, lintegral_withDensity_eq_lintegral_mul₀ hFd
              (show AEMeasurable (fun v => Gd (u + v)) volume from
                hGd.comp_quasiMeasurePreserving (quasiMeasurePreserving_add_left volume u))]
          rw [hhdef]
          simp only [Pi.mul_apply]
          rw [← lintegral_sub_right_eq_self (fun v => Fd v * Gd (u + v)) u]
          congr 1; funext x
          rw [mul_comm, show u + (x - u) = x by ring]
        have hLL : ∀ u1 u2 : ℝ, u1 ≤ u2 → Gd u1 * h u2 ≤ h u1 * Gd u2 := by
          intro u1 u2 hu
          rw [hh2, hh2, ← lintegral_const_mul' _ _ (hGdtop u1),
            ← lintegral_mul_const' _ _ (hGdtop u2)]
          apply lintegral_mono_ae
          filter_upwards [hae] with v hv
          have hK := hKg (u1 + v) (u2 + v) (by linarith) 0 v hv
          simp only [add_sub_cancel_right, sub_zero] at hK
          rw [hGddef]
          simp only
          rw [← ENNReal.ofReal_mul (hg.2.1 _), ← ENNReal.ofReal_mul (hg.2.1 _)]
          exact ENNReal.ofReal_le_ofReal (by linarith)
        have hI0 : ∀ k, ∫⁻ x, Q k x ∂ν = ∫⁻ w, Q k w * Gd w := by
          intro k
          rw [hνd, lintegral_withDensity_eq_lintegral_mul₀ hGd (hQmeas k).aemeasurable]
          congr 1; funext w; simp only [Pi.mul_apply]; ring
        have hI1 : ∀ k, ∫⁻ x, Q (k+1) x ∂ν = ∫⁻ w, Q k w * h w := by
          intro k
          rw [hνd, lintegral_withDensity_eq_lintegral_mul₀ hGd (hQmeas _).aemeasurable]
          have e1 : ∀ x, (Gd * Q (k+1)) x = ∫⁻ w, Gd x * (Fd (x - w) * Q k w) := by
            intro x
            simp only [Pi.mul_apply]
            rw [hQrec k x, hrepr _ (hQmeas k) x, lintegral_const_mul' _ _ (hGdtop x)]
          simp_rw [e1]
          rw [lintegral_lintegral_swap]
          · congr 1; funext w
            rw [hhdef]; simp only
            rw [mul_comm, ← lintegral_mul_const' _ _ (hQfin k w)]
            congr 1; funext x; ring
          · exact hGd.comp_fst.mul ((hFd.comp_quasiMeasurePreserving
              (quasiMeasurePreserving_sub (volume : Measure ℝ) (volume : Measure ℝ))).mul
              (hQmeas k).aemeasurable.comp_snd)
        have hQle1 : ∀ k x, Q k x ≤ 1 := fun k x => by
          rw [hQdef]; exact tsub_le_self.trans (hG1 k x)
        have hfinI : ∀ k, ∫⁻ x, Q k x ∂ν ≠ ⊤ := by
          intro k
          refine ne_top_of_le_ne_top (b := ∫⁻ _x, (1 : ℝ≥0∞) ∂ν) (by simp) ?_
          exact lintegral_mono (fun x => hQle1 k x)
        have hPG : ∀ j, P j = ∫ x, (G j x).toReal ∂ν := fun j => by rw [hGdef]; rfl
        have hintG : ∀ j, Integrable (fun x => (G j x).toReal) ν := by
          intro j
          have := hint j
          rw [hGdef]; exact this
        have hPk : ∀ k, failProb P (k+1) = (∫⁻ x, Q k x ∂ν).toReal := by
          intro k
          show P k - P (k+1) = _
          rw [hPG, hPG, ← integral_sub (hintG k) (hintG (k+1)),
            ← integral_toReal (hQmeas k).aemeasurable
              (Filter.Eventually.of_forall (fun x => lt_top_iff_ne_top.mpr (hQfin k x)))]
          congr 1; funext x
          rw [hQdef]; simp only
          rw [ENNReal.toReal_sub_of_le (hGle k x) (hfin k x)]
        intro j k hj hjk
        obtain ⟨n, rfl⟩ : ∃ n, j = n+1 := ⟨j-1, by omega⟩
        obtain ⟨m, rfl⟩ : ∃ m, k = m+1 := ⟨k-1, by omega⟩
        have hnm : n ≤ m := by omega
        rw [hPk, hPk, hPk, hPk, ← ENNReal.toReal_mul, ← ENNReal.toReal_mul]
        refine ENNReal.toReal_mono (ENNReal.mul_ne_top (hfinI _) (hfinI _)) ?_
        rw [hI1 m, hI0 n, hI1 n, hI0 m]
        have := hBCF (Q n) (Q m) h Gd (hQmeas n).aemeasurable (hQmeas m).aemeasurable hhm hGd
          (fun u1 u2 hu => by
            rw [mul_comm (Q n u2), mul_comm (Q n u1)]; exact hTP n m hnm u1 u2 hu) hLL
        rw [mul_comm (∫⁻ w, Q m w * h w), mul_comm (∫⁻ w, Q n w * h w)]
        exact this
      have hqnn : ∀ k, 0 ≤ failProb P (k+1) := by
        intro k
        simp only [failProb, hPdef, ShockWear.RandThreshold.randP]
        have := integral_mono (hint (k+1)) (hint k) (fun x => hmono k x)
        linarith
      have hqle : ∀ k, failProb P (k+1) ≤ 1 := by
        intro k
        simp only [failProb]
        linarith [(hP01 k).2, (hP01 (k+1)).1]
      refine ⟨hP1, ?_⟩
      have hstep : ∀ j k, j ≤ k → failProb P (k+1+1) * failProb P (j+1) ≤
          failProb P (j+1+1) * failProb P (k+1) := fun j k hjk => hP1 (j+1) (k+1) (by omega) (by omega)
      have hrep : ∀ u : ℝ, shockDens lam P u = lam * (Real.exp (-(lam * u)) *
          ∑' k, failProb P (k+1) * ((lam * u) ^ k / (k.factorial : ℝ))) := by
        intro u
        unfold shockDens ShockWear.CumDamage.poisW
        rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
        congr 1; funext k; ring
      intro x hx s t hs hst
      rw [hrep, hrep, hrep, hrep]
      have hc := hcore (fun k => failProb P (k+1)) hqnn hqle hstep (lam * x) (lam * s) (lam * t)
        (by positivity) (by positivity) (mul_le_mul_of_nonneg_left hst hlam.le)
      simp only [mul_add] at hc ⊢
      have e1 : Real.exp (-(lam * x + lam * t)) * Real.exp (-(lam * s)) =
          Real.exp (-(lam * x + lam * s)) * Real.exp (-(lam * t)) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      have hpos : 0 ≤ lam * lam * (Real.exp (-(lam * x + lam * t)) * Real.exp (-(lam * s))) := by positivity
      have := mul_le_mul_of_nonneg_left hc hpos
      calc _ = lam * lam * (Real.exp (-(lam * x + lam * t)) * Real.exp (-(lam * s))) *
            ((∑' n, failProb P (n+1) * ((lam * x + lam * t) ^ n / (n.factorial : ℝ))) *
              (∑' n, failProb P (n+1) * ((lam * s) ^ n / (n.factorial : ℝ)))) := by ring
        _ ≤ lam * lam * (Real.exp (-(lam * x + lam * t)) * Real.exp (-(lam * s))) *
            ((∑' n, failProb P (n+1) * ((lam * x + lam * s) ^ n / (n.factorial : ℝ))) *
              (∑' n, failProb P (n+1) * ((lam * t) ^ n / (n.factorial : ℝ)))) := this
        _ = _ := by rw [e1]; ring
