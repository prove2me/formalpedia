-- Prove2me | solution 1 for OfflineCensoredPricing.Identifiability.lemma_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T18:05:14.942577+00:00
-- url     : https://prove2.me/submissions/74ecbc9d-3200-40b1-a54d-951f031a9876
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model
import Definitions.Def_OfflineCensoredPricing_Identifiability_D2ACD
import Theorems.Thm_OfflineCensoredPricing_Identifiability_proposition_2
import Theorems.Thm_OfflineCensoredPricing_Identifiability_lemma_1
import Theorems.Thm_OfflineCensoredPricing_Identifiability_lemma_D_1
import Theorems.Thm_OfflineCensoredPricing_Identifiability_lemma_D_2
import Theorems.Thm_UnderstandingML_hoeffding_inequality

open MeasureTheory Set OfflineCensoredPricing.Identifiability

namespace OCPLem2Aux

/-! ### Elementary Lipschitz bounds on `[0, p̄]` -/

lemma lip_qpsi (ψ : ℝ → ℝ) (B Lψ pb : ℝ) (hB : ∀ q, 0 ≤ q → q ≤ pb → |ψ q| ≤ B)
    (hL : ∀ q a, |ψ q - ψ a| ≤ Lψ * |q - a|) (q a : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ pb)
    (ha0 : 0 ≤ a) (ha1 : a ≤ pb) :
    |q * ψ q - a * ψ a| ≤ (B + pb * Lψ) * |q - a| := by
  have e : q * ψ q - a * ψ a = (q - a) * ψ q + a * (ψ q - ψ a) := by ring
  rw [e]
  have h1 : |(q - a) * ψ q| ≤ |q - a| * B := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB q hq0 hq1) (abs_nonneg _)
  have h2 : |a * (ψ q - ψ a)| ≤ pb * (Lψ * |q - a|) := by
    rw [abs_mul, abs_of_nonneg ha0]
    exact mul_le_mul ha1 (hL q a) (abs_nonneg _) (le_trans ha0 ha1)
  calc |(q - a) * ψ q + a * (ψ q - ψ a)| ≤ |(q - a) * ψ q| + |a * (ψ q - ψ a)| := abs_add_le _ _
    _ ≤ |q - a| * B + pb * (Lψ * |q - a|) := add_le_add h1 h2
    _ = (B + pb * Lψ) * |q - a| := by ring

lemma lip_quad (k c pb : ℝ) (hk : 0 ≤ k) (q a : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ pb)
    (ha0 : 0 ≤ a) (ha1 : a ≤ pb) :
    |q * (-k * q + c) - a * (-k * a + c)| ≤ (2 * k * pb + |c|) * |q - a| := by
  have e : q * (-k * q + c) - a * (-k * a + c) = (q - a) * (-k * (q + a) + c) := by ring
  rw [e, abs_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc |-k * (q + a) + c| ≤ |-k * (q + a)| + |c| := abs_add_le _ _
    _ ≤ 2 * k * pb + |c| := by
      have : |-k * (q + a)| = k * (q + a) := by
        rw [abs_of_nonpos (by nlinarith)]; ring
      rw [this]; nlinarith

/-- `|mean x − mean y| ≤ c` when `|xⱼ − yⱼ| ≤ c`. -/
lemma mean_diff {n : ℕ} (hn : 0 < n) (x y : Fin n → ℝ) (c : ℝ) (h : ∀ j, |x j - y j| ≤ c) :
    |(∑ j, x j) / (n : ℝ) - (∑ j, y j) / (n : ℝ)| ≤ c := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hn', div_le_iff₀ hn']
  calc |∑ j, (x j - y j)| ≤ ∑ j, |x j - y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, c := Finset.sum_le_sum (fun j _ => h j)
    _ = c * n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- `|mean x| ≤ c` when `|xⱼ| ≤ c`. -/
lemma mean_abs {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (c : ℝ) (h : ∀ j, |x j| ≤ c) :
    |(∑ j, x j) / (n : ℝ)| ≤ c := by
  have := mean_diff hn x (fun _ => 0) c (fun j => by simpa using h j)
  simpa using this


/-! ### Facts about the instance and the estimators -/

section Facts

variable {K : ℕ} [NeZero K] (I : Instance K) (hI : I.Standing) {Nv : Fin K → ℕ}
  (S : Sample K Nv)

include hI

lemma bHat_mem : bHat I.toPublic S ∈ Icc I.blo I.bhi := by
  have h1 : I.blo ≤ I.bhi := le_trans hI.2.2.2.2.2.1 hI.2.2.2.2.2.2.1
  unfold bHat
  exact ⟨le_max_left _ _, max_le h1 (min_le_left _ _)⟩

lemma iStar_spec : ∀ j, I.yh j + bHat I.toPublic S * I.p j ≤ lamHat I.toPublic S := by
  have := Finset.min'_mem (iStarSet I.toPublic S) (iStarSet_nonempty I.toPublic S)
  unfold iStarSet at this
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this

lemma lam_le_lamBar : lam I ≤ lamBar I := by
  unfold lam lamBar
  refine ciSup_le (fun i => le_trans ?_ (le_ciSup (Finite.bddAbove_range _) i))
  have := mul_le_mul_of_nonneg_right hI.2.2.2.2.2.2.1
    (le_trans hI.2.2.1.le (hI.2.2.2.2.2.2.2.2.2.1 i).1)
  linarith

lemma lam_pos : 0 < lam I := by
  obtain ⟨-, -, hplo, -, hblo, hbb, -, -, -, hpi, hyh, -⟩ := hI
  have i : Fin K := 0
  have hle : I.yh i + I.b * I.p i ≤ lam I :=
    le_ciSup (Finite.bddAbove_range (fun i => I.yh i + I.b * I.p i)) i
  have := mul_pos (lt_of_lt_of_le hblo hbb) (lt_of_lt_of_le hplo (hpi i).1)
  linarith [hyh i]

lemma lamHat_le : lamHat I.toPublic S ≤ lamBar I := by
  unfold lamHat
  set i := iStar I.toPublic S
  have hb := (bHat_mem I hI S).2
  have hp : 0 ≤ I.p i := le_trans hI.2.2.1.le (hI.2.2.2.2.2.2.2.2.2.1 i).1
  have : I.yh i + bHat I.toPublic S * I.p i ≤ I.yh i + I.bhi * I.p i := by nlinarith
  exact le_trans this (le_ciSup (Finite.bddAbove_range (fun i => I.yh i + I.bhi * I.p i)) i)

lemma lamHat_pos : 0 < lamHat I.toPublic S := by
  unfold lamHat
  set i := iStar I.toPublic S
  have hb := (bHat_mem I hI S).1
  have hp : 0 < I.p i := lt_of_lt_of_le hI.2.2.1 (hI.2.2.2.2.2.2.2.2.2.1 i).1
  have := mul_pos (lt_of_lt_of_le hI.2.2.2.2.1 hb) hp
  linarith [hI.2.2.2.2.2.2.2.2.2.2.1 i]

/-- (D.10): `|λ̂ − λ| ≤ p̄ |b̂ − b|`. -/
lemma lamHat_sub : |lamHat I.toPublic S - lam I| ≤ I.phi * |bHat I.toPublic S - I.b| := by
  obtain ⟨i0, hi0⟩ := exists_eq_ciSup_of_finite (f := fun i => I.yh i + I.b * I.p i)
  have hlam : lam I = I.yh i0 + I.b * I.p i0 := by unfold lam; rw [← hi0]
  set bh := bHat I.toPublic S
  have hp : ∀ i, 0 ≤ I.p i ∧ I.p i ≤ I.phi := fun i =>
    ⟨le_trans hI.2.2.1.le (hI.2.2.2.2.2.2.2.2.2.1 i).1, (hI.2.2.2.2.2.2.2.2.2.1 i).2⟩
  have h1 := iStar_spec I hI S i0
  set i := iStar I.toPublic S
  have hlhat : lamHat I.toPublic S = I.yh i + bh * I.p i := rfl
  have h2 : I.yh i + I.b * I.p i ≤ lam I :=
    le_ciSup (Finite.bddAbove_range (fun i => I.yh i + I.b * I.p i)) i
  have k1 : |(bh - I.b) * I.p i0| ≤ I.phi * |bh - I.b| := by
    rw [abs_mul, abs_of_nonneg (hp i0).1, mul_comm]
    exact mul_le_mul_of_nonneg_right (hp i0).2 (abs_nonneg _)
  have k2 : |(bh - I.b) * I.p i| ≤ I.phi * |bh - I.b| := by
    rw [abs_mul, abs_of_nonneg (hp i).1, mul_comm]
    exact mul_le_mul_of_nonneg_right (hp i).2 (abs_nonneg _)
  rw [abs_le]
  constructor
  · have := (abs_le.1 k1).1
    have e : I.yh i0 + bh * I.p i0 = lam I + (bh - I.b) * I.p i0 := by rw [hlam]; ring
    linarith
  · have := (abs_le.1 k2).2
    have e : lamHat I.toPublic S = I.yh i + I.b * I.p i + (bh - I.b) * I.p i := by
      rw [hlhat]; ring
    linarith

lemma gammaHat_mem (i : Fin K) : gammaHat I.toPublic S i ∈ Icc (0 : ℝ) 1 := by
  unfold gammaHat
  constructor
  · positivity
  · rcases Nat.eq_zero_or_pos (Nv i) with h | h
    · simp [h]
    · rw [div_le_one (by exact_mod_cast h)]
      have := Finset.card_filter_le (Finset.univ : Finset (Fin (Nv i)))
        (fun j => S i j < I.toPublic.yh i)
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact_mod_cast this

lemma gammaHatMax_mem : gammaHatMax I.toPublic S ∈ Icc (0 : ℝ) 1 := by
  unfold gammaHatMax
  constructor
  · exact le_trans (gammaHat_mem I hI S 0).1 (le_ciSup (Finite.bddAbove_range _) 0)
  · exact ciSup_le (fun i => (gammaHat_mem I hI S i).2)

lemma gam_mem : gam I ∈ Icc (0 : ℝ) 1 := by
  haveI := hI.1
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

lemma shiftedMean_mem (hS0 : ∀ i j, 0 ≤ S i j) (hSy : ∀ i j, S i j ≤ I.yh i)
    (hN : 0 < Nv (iStar I.toPublic S)) :
    shiftedMean I.toPublic S ∈ Icc 0 (lamHat I.toPublic S) := by
  set i := iStar I.toPublic S
  have hb := (bHat_mem I hI S).1
  have hbp : 0 ≤ bHat I.toPublic S * I.p i :=
    mul_nonneg (le_trans hI.2.2.2.2.1.le hb) (le_trans hI.2.2.1.le (hI.2.2.2.2.2.2.2.2.2.1 i).1)
  have hN' : (0 : ℝ) < Nv i := by exact_mod_cast hN
  unfold shiftedMean
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun j _ => by linarith [hS0 i j])) hN'.le
  · rw [div_le_iff₀ hN']
    calc ∑ j, (S i j + bHat I.toPublic S * I.p i) ≤ ∑ _j : Fin (Nv i), lamHat I.toPublic S :=
          Finset.sum_le_sum (fun j _ => by
            have := hSy i j
            show S i j + bHat I.toPublic S * I.p i ≤ I.yh i + bHat I.toPublic S * I.p i
            linarith)
      _ = lamHat I.toPublic S * Nv i := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Facts


/-! ### The true revenue functions -/

lemma integrable_min' (μ : Measure ℝ) [IsProbabilityMeasure μ] (m c y : ℝ)
    (hm : ∀ᵐ ξ ∂μ, m ≤ ξ) : Integrable (fun ξ => min (ξ - c) y) μ := by
  refine Integrable.of_bound (by fun_prop) (|y| + |m - c|) ?_
  filter_upwards [hm] with ξ hξ
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have : min (m - c) y ≤ min (ξ - c) y := min_le_min_right _ (by linarith)
    have h1 : -(|y| + |m - c|) ≤ min (m - c) y := by
      rcases min_cases (m - c) y with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
        linarith [neg_abs_le y, neg_abs_le (m - c), abs_nonneg y, abs_nonneg (m - c)]
    linarith
  · linarith [min_le_right (ξ - c) y, le_abs_self y, abs_nonneg (m - c)]

section True

variable {K : ℕ} [NeZero K] (I : Instance K) (hI : I.Standing)

include hI

lemma ae_ge : ∀ᵐ ξ ∂I.μξ, I.b * I.phi ≤ ξ := by
  have h := measure_eq_zero_iff_ae_notMem.1 hI.2.2.2.2.2.2.2.2.2.2.2.1
  filter_upwards [h] with ξ hξ
  simpa using hξ

lemma E_mem : ∫ ξ, min ξ (lam I) ∂I.μξ ∈ Icc 0 (lam I) := by
  haveI := hI.1
  have hl := lam_pos I hI
  have hbp : 0 < I.b * I.phi :=
    mul_pos (lt_of_lt_of_le hI.2.2.2.2.1 hI.2.2.2.2.2.1) (lt_trans hI.2.2.1 hI.2.2.2.1)
  have hint : Integrable (fun ξ => min ξ (lam I)) I.μξ := by
    have := integrable_min' I.μξ (I.b * I.phi) 0 (lam I) (ae_ge I hI)
    simpa using this
  constructor
  · refine integral_nonneg_of_ae ?_
    filter_upwards [ae_ge I hI] with ξ hξ
    show 0 ≤ min ξ (lam I)
    exact le_min (by linarith) hl.le
  · have := integral_mono_ae hint (integrable_const (lam I))
      (Filter.Eventually.of_forall (fun ξ => min_le_right ξ (lam I)))
    simpa using this

/-- Continuity of the closed forms at `p̃`: `R(p̃) = R₁(p̃) = R₂(p̃)`. -/
lemma junction_true :
    RF I I.μξ (pTilde I) = R1 I (pTilde I) ∧ RF I I.μξ (pTilde I) = R2 I (pTilde I) := by
  haveI := hI.1
  have hb : 0 < I.b := lt_of_lt_of_le hI.2.2.2.2.1 hI.2.2.2.2.2.1
  set a := pTilde I with ha
  have hba : I.b * a = lam I - I.y := by rw [ha]; unfold pTilde; field_simp
  have hint : Integrable (fun ξ => min ξ (lam I)) I.μξ := by
    have := integrable_min' I.μξ (I.b * I.phi) 0 (lam I) (ae_ge I hI)
    simpa using this
  have hRF : RF I I.μξ a = a * (∫ ξ, min ξ (lam I) ∂I.μξ + (I.y - lam I)) := by
    unfold RF
    congr 1
    have : (fun ξ => min (ξ - I.b * a) I.y) = fun ξ => min ξ (lam I) + (I.y - lam I) := by
      funext ξ
      rw [hba, ← min_add_add_right]
      congr 1 <;> ring
    rw [this, integral_add hint (integrable_const _), integral_const]
    simp
  refine ⟨?_, ?_⟩
  · rw [hRF]; unfold R1
    rw [show -gam I * I.b * a = -(gam I * (I.b * a)) by ring, hba]; ring
  · rw [hRF]; unfold R2
    rw [show -I.b * a = -(I.b * a) by ring, hba]; ring

lemma lip_true (q a : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ I.phi) (ha0 : 0 ≤ a) (ha1 : a ≤ I.phi) :
    |RF I I.μξ q - RF I I.μξ a| ≤ (I.y + I.phi * I.b) * |q - a| := by
  haveI := hI.1
  have hb : 0 < I.b := lt_of_lt_of_le hI.2.2.2.2.1 hI.2.2.2.2.2.1
  set G : ℝ → ℝ := fun q => ∫ ξ, min (ξ - I.b * q) I.y ∂I.μξ with hG
  have hint : ∀ q, Integrable (fun ξ => min (ξ - I.b * q) I.y) I.μξ := fun q =>
    integrable_min' I.μξ _ _ _ (ae_ge I hI)
  have hB : ∀ q, 0 ≤ q → q ≤ I.phi → |G q| ≤ I.y := by
    intro q hq0 hq1
    have h0 : 0 ≤ G q := integral_nonneg_of_ae (by
      filter_upwards [ae_ge I hI] with ξ hξ
      show 0 ≤ min (ξ - I.b * q) I.y
      exact le_min (by nlinarith) hI.2.1)
    have h1 : G q ≤ I.y := by
      have := integral_mono (hint q) (integrable_const I.y) (fun ξ => min_le_right _ _)
      simpa using this
    rw [abs_of_nonneg h0]; exact h1
  have hL : ∀ q a, |G q - G a| ≤ I.b * |q - a| := by
    intro q a
    rw [hG]
    simp only
    rw [← integral_sub (hint q) (hint a)]
    have := norm_integral_le_of_norm_le_const (μ := I.μξ)
      (f := fun ξ => min (ξ - I.b * q) I.y - min (ξ - I.b * a) I.y) (C := I.b * |q - a|)
      (Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_eq_abs]
        refine le_trans (abs_min_sub_min_le_max _ _ _ _) ?_
        rw [sub_self, abs_zero]
        refine max_le ?_ (by positivity)
        rw [show ξ - I.b * q - (ξ - I.b * a) = I.b * (a - q) by ring, abs_mul,
          abs_of_nonneg hb.le, abs_sub_comm]))
    simpa [probReal_univ] using this
  exact lip_qpsi G I.y I.b I.phi hB hL q a hq0 hq1 ha0 ha1

end True

section HatLip

variable {K : ℕ} [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv)

lemma lip_hat (pb : ℝ) (hbh : 0 ≤ bHat P S) (hy : 0 ≤ P.y)
    (hc : ∀ j, 0 ≤ S (iStar P S) j + bHat P S * P.p (iStar P S))
    (hN : 0 < Nv (iStar P S)) (q a : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ pb) (ha0 : 0 ≤ a)
    (ha1 : a ≤ pb) :
    |RHat P S q - RHat P S a| ≤ (P.y + bHat P S * pb + pb * bHat P S) * |q - a| := by
  set i := iStar P S
  set bh := bHat P S
  set Ψ : ℝ → ℝ := fun q => (∑ j, min (S i j + bh * P.p i - bh * q) P.y) / (Nv i : ℝ) with hΨ
  have hR : ∀ q, RHat P S q = q * Ψ q := fun q => rfl
  have hB : ∀ q, 0 ≤ q → q ≤ pb → |Ψ q| ≤ P.y + bh * pb := by
    intro q hq0 hq1
    apply mean_abs hN
    intro j
    rw [abs_le]
    have := hc j
    constructor
    · have : -(P.y + bh * pb) ≤ S i j + bh * P.p i - bh * q := by nlinarith
      exact le_min this (by nlinarith)
    · linarith [min_le_right (S i j + bh * P.p i - bh * q) P.y, mul_nonneg hbh (le_trans hq0 hq1)]
  have hL : ∀ q a, |Ψ q - Ψ a| ≤ bh * |q - a| := by
    intro q a
    apply mean_diff hN
    intro j
    refine le_trans (abs_min_sub_min_le_max _ _ _ _) ?_
    rw [sub_self, abs_zero]
    refine max_le ?_ (by positivity)
    rw [show S i j + bh * P.p i - bh * q - (S i j + bh * P.p i - bh * a) = bh * (a - q) by ring,
      abs_mul, abs_of_nonneg hbh, abs_sub_comm]
  rw [hR, hR]
  exact lip_qpsi Ψ (P.y + bh * pb) bh pb hB hL q a hq0 hq1 ha0 ha1

end HatLip


section Junction

variable {K : ℕ} [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv)

lemma bHat_pos (hb : 0 < P.blo) : 0 < bHat P S := lt_of_lt_of_le hb (le_max_left _ _)

lemma junction (hb : 0 < P.blo) (hS : ∀ i j, S i j ≤ P.yh i) (hN : 0 < Nv (iStar P S)) :
    RHat P S (pTildeHat P S) = R1Hat P S (pTildeHat P S) ∧
      RHat P S (pTildeHat P S) = R2Hat P S (pTildeHat P S) := by
  have hbp := bHat_pos P S hb
  set i := iStar P S with hi
  set bh := bHat P S with hbh
  set a := pTildeHat P S with ha
  have hba : bh * a = lamHat P S - P.y := by
    rw [ha]; unfold pTildeHat; rw [← hbh]; field_simp
  have hlam : lamHat P S = P.yh i + bh * P.p i := rfl
  have hN' : (Nv i : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hR : RHat P S a = a * (shiftedMean P S - (lamHat P S - P.y)) := by
    unfold RHat shiftedMean
    have : ∀ j, min (S i j + bh * P.p i - bh * a) P.y = (S i j + bh * P.p i) - bh * a := by
      intro j
      apply min_eq_left
      have := hS i j
      rw [hba, hlam]; linarith
    rw [← hi, ← hbh]
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hba]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hR]; unfold R1Hat
    have : gammaHatMax P S * bh * a = gammaHatMax P S * (lamHat P S - P.y) := by
      rw [mul_assoc, hba]
    rw [show -gammaHatMax P S * bh * a = -(gammaHatMax P S * bh * a) by ring, this]
    ring
  · rw [hR]; unfold R2Hat
    rw [show -bh * a = -(bh * a) by ring, hba]
    ring


end Junction

/-! ### Real-variable bounds for the three cases -/

lemma abs_add7 (a b c d e f g : ℝ) :
    |a + b + c + d + e + f + g| ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
  have h1 := abs_add_le (a + b + c + d + e + f) g
  have h2 := abs_add_le (a + b + c + d + e) f
  have h3 := abs_add_le (a + b + c + d) e
  have h4 := abs_add_le (a + b + c) d
  have h5 := abs_add_le (a + b) c
  have h6 := abs_add_le a b
  linarith

lemma c2max (q pb b bh g gh l lh y E Sh bb lb : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ pb)
    (hb0 : 0 ≤ b) (hbb : b ≤ bb) (hgh0 : 0 ≤ gh) (hgh1 : gh ≤ 1) (hl0 : 0 ≤ l) (hlb : l ≤ lb)
    (hy : 0 ≤ y) (hlhl : |lh - l| ≤ pb * |bh - b|) :
    |q * (-(gh * bh) * q + Sh + (1 - gh) * (y - lh)) - q * (-(g * b) * q + E + (1 - g) * (y - l))|
      ≤ q * (q * (|bh - b| + bb * |gh - g|) + |Sh - E| + (y + lb) * |gh - g| +
        2 * (pb * |bh - b|)) := by
  have e : q * (-(gh * bh) * q + Sh + (1 - gh) * (y - lh)) - q * (-(g * b) * q + E + (1 - g) * (y - l))
      = q * (gh * (b - bh) * q + b * (g - gh) * q + (Sh - E) + (g - gh) * y + (l - lh) +
        gh * (lh - l) + l * (gh - g)) := by ring
  rw [e, abs_mul, abs_of_nonneg hq0]
  apply mul_le_mul_of_nonneg_left _ hq0
  refine le_trans (abs_add7 _ _ _ _ _ _ _) ?_
  have t1 : |gh * (b - bh) * q| ≤ q * |bh - b| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hgh0, abs_of_nonneg hq0, abs_sub_comm]
    have := abs_nonneg (bh - b)
    nlinarith [mul_nonneg (mul_nonneg hq0 this) (sub_nonneg.2 hgh1)]
  have t2 : |b * (g - gh) * q| ≤ q * (bb * |gh - g|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hb0, abs_of_nonneg hq0, abs_sub_comm]
    have := abs_nonneg (gh - g)
    nlinarith [mul_nonneg (mul_nonneg hq0 this) (sub_nonneg.2 hbb)]
  have t4 : |(g - gh) * y| ≤ y * |gh - g| := by
    rw [abs_mul, abs_of_nonneg hy, abs_sub_comm, mul_comm]
  have t5 : |l - lh| ≤ pb * |bh - b| := by rw [abs_sub_comm]; exact hlhl
  have t6 : |gh * (lh - l)| ≤ pb * |bh - b| := by
    rw [abs_mul, abs_of_nonneg hgh0]
    have := abs_nonneg (lh - l); nlinarith
  have t7 : |l * (gh - g)| ≤ lb * |gh - g| := by
    rw [abs_mul, abs_of_nonneg hl0]
    exact mul_le_mul_of_nonneg_right hlb (abs_nonneg _)
  nlinarith

lemma c2min (q pb b bh E Sh : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ pb) :
    |q * (-bh * q + Sh) - q * (-b * q + E)| ≤ q * (q * |bh - b| + |Sh - E|) := by
  have e : q * (-bh * q + Sh) - q * (-b * q + E) = q * ((b - bh) * q + (Sh - E)) := by ring
  rw [e, abs_mul, abs_of_nonneg hq0]
  apply mul_le_mul_of_nonneg_left _ hq0
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul, abs_of_nonneg hq0, abs_sub_comm b bh, mul_comm]

lemma tri3 (Fq Fa Ga Gq : ℝ) : |Fq - Gq| ≤ |Fq - Fa| + |Fa - Ga| + |Ga - Gq| := by
  have h1 := abs_sub_le Fq Fa Gq
  have h2 := abs_sub_le Fa Ga Gq
  linarith


/-! ### The deterministic part of the proof of Lemma 2 (Appendix D.2, Cases 1–3) -/

lemma detR (pb lo y b bh bhi blo l lh lB g gh E Sh α q pt ph C1 C2 : ℝ)
    (R Rh R1 R2 R1h R2h : ℝ → ℝ)
    (hlo : 0 < lo) (hq : q ∈ Icc lo pb) (hy : 0 ≤ y) (hblo : 0 < blo) (hbb : blo ≤ b)
    (hbbh : b ≤ bhi) (hbh1 : blo ≤ bh) (hbh2 : bh ≤ bhi) (hl : 0 < l) (hlb : l ≤ lB)
    (hlh : 0 < lh) (hlhb : lh ≤ lB) (hlhl : |lh - l| ≤ pb * |bh - b|)
    (hgh0 : 0 ≤ gh) (hgh1 : gh ≤ 1) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hSh0 : 0 ≤ Sh) (hSh1 : Sh ≤ lh)
    (hE0 : 0 ≤ E) (hE1 : E ≤ l) (hα : 0 < α)
    (hpt : pt = (l - y) / b) (hph : ph = (lh - y) / bh)
    (hC1 : C1 = 5 * pb ^ 2 + (3 * (bhi * pb) + 2 * (lB + y)) ^ 2 / blo ^ 2)
    (hC2 : C2 = pb * (y + lB + pb * bhi))
    (hR1 : ∀ r, R1 r = r * (-(g * b) * r + (E + (1 - g) * (y - l))))
    (hR2 : ∀ r, R2 r = r * (-b * r + E))
    (hR1h : ∀ r, R1h r = r * (-(gh * bh) * r + (Sh + (1 - gh) * (y - lh))))
    (hR2h : ∀ r, R2h r = r * (-bh * r + Sh))
    (h1 : |bh - b| ≤ α / (2 * C1))
    (hD1 : ∀ r, 0 ≤ r → r ≤ max (min (min ph pt) pb) 0 → |Rh r - R r| ≤ 3 * pb ^ 2 * |bh - b| + α / 6)
    (hγ : |gh - g| ≤ α / (6 * C2))
    (hSE : |Sh - E| ≤ pb * |bh - b| + α / (6 * pb))
    (jt1 : R pt = R1 pt) (jt2 : R pt = R2 pt) (jh1 : Rh ph = R1h ph) (jh2 : Rh ph = R2h ph)
    (hR0 : R 0 = 0) (hRh0 : Rh 0 = 0)
    (lipR : ∀ r a, 0 ≤ r → r ≤ pb → 0 ≤ a → a ≤ pb → |R r - R a| ≤ (y + pb * b) * |r - a|)
    (lipRh : ∀ r a, 0 ≤ r → r ≤ pb → 0 ≤ a → a ≤ pb →
      |Rh r - Rh a| ≤ (y + bh * pb + pb * bh) * |r - a|) :
    |(if q < ph then Rh q else R1h q) - (if q < pt then R q else R1 q)| ≤ α ∧
      |(if q < ph then Rh q else R2h q) - (if q < pt then R q else R2 q)| ≤ α := by
  have hq0 : 0 ≤ q := le_trans hlo.le hq.1
  have hq1 : q ≤ pb := hq.2
  have hpb : 0 < pb := lt_of_lt_of_le hlo (le_trans hq.1 hq.2)
  have hb0 : 0 < b := lt_of_lt_of_le hblo hbb
  have hbh0 : 0 < bh := lt_of_lt_of_le hblo hbh1
  have hbhi0 : 0 ≤ bhi := le_trans hb0.le hbbh
  obtain ⟨u, hu⟩ : ∃ u, u = bhi * pb := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = lB + y := ⟨_, rfl⟩
  obtain ⟨δb, hδb⟩ : ∃ δb, δb = |bh - b| := ⟨_, rfl⟩
  obtain ⟨Δγ, hΔγ⟩ : ∃ Δγ, Δγ = |gh - g| := ⟨_, rfl⟩
  rw [← hu, ← hv] at hC1
  rw [← hδb] at h1 hD1 hSE hlhl
  rw [← hΔγ] at hγ
  have hu0 : 0 ≤ u := by rw [hu]; exact mul_nonneg hbhi0 hpb.le
  have hv0 : 0 ≤ v := by rw [hv]; linarith only [hy, hl, hlb]
  have hδ0 : 0 ≤ δb := by rw [hδb]; exact abs_nonneg _
  have hΔ0 : 0 ≤ Δγ := by rw [hΔγ]; exact abs_nonneg _
  have hC1pos : 0 < C1 := by rw [hC1]; positivity
  have hC2pos : 0 < C2 := by
    rw [hC2]; exact mul_pos hpb (by nlinarith only [hy, hl, hlb, hpb, hbhi0])
  have hδ : C1 * δb ≤ α / 2 := by
    have := mul_le_mul_of_nonneg_left h1 hC1pos.le
    have e : C1 * (α / (2 * C1)) = α / 2 := by field_simp
    linarith only [this, e]
  have hγ' : C2 * Δγ ≤ α / 6 := by
    have := mul_le_mul_of_nonneg_left hγ hC2pos.le
    have e : C2 * (α / (6 * C2)) = α / 6 := by field_simp
    linarith only [this, e]
  have hsq : 0 ≤ (3 * u + 2 * v) ^ 2 / blo ^ 2 := by positivity
  have h5 : 5 * pb ^ 2 * δb ≤ C1 * δb := by
    apply mul_le_mul_of_nonneg_right _ hδ0
    rw [hC1]; linarith only [hsq]
  -- |p̂~ − p̃|
  have hD : |ph - pt| ≤ (u + v) * δb / blo ^ 2 := by
    have e : ph - pt = ((lh - l) * b + (l - y) * (b - bh)) / (bh * b) := by
      rw [hph, hpt]; field_simp; ring
    have hnum : |(lh - l) * b + (l - y) * (b - bh)| ≤ (u + v) * δb := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul, abs_of_pos hb0, abs_sub_comm b bh, ← hδb]
      have k1 : |lh - l| * b ≤ u * δb := by
        have := mul_le_mul hlhl hbbh hb0.le (by positivity)
        rw [hu]; linarith only [this]
      have k2 : |l - y| * δb ≤ v * δb := by
        apply mul_le_mul_of_nonneg_right _ hδ0
        rw [abs_le, hv]; constructor <;> linarith only [hy, hl, hlb]
      linarith only [k1, k2]
    rw [e, abs_div, abs_of_pos (mul_pos hbh0 hb0)]
    have hden : blo ^ 2 ≤ bh * b := by nlinarith only [hblo, hbh1, hbb]
    rw [div_le_div_iff₀ (mul_pos hbh0 hb0) (by positivity)]
    calc |(lh - l) * b + (l - y) * (b - bh)| * blo ^ 2 ≤ (u + v) * δb * blo ^ 2 :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
      _ ≤ (u + v) * δb * (bh * b) := mul_le_mul_of_nonneg_left hden (by positivity)
  -- the Case 3 arithmetic
  have hcase3 : ∀ L d, 0 ≤ L → L ≤ 4 * u + 2 * v → 0 ≤ d → d ≤ |ph - pt| →
      L * d + (3 * pb ^ 2 * δb + α / 6) ≤ α := by
    intro L d hL0 hL hd0 hd
    have k : L * d ≤ (3 * u + 2 * v) ^ 2 / blo ^ 2 * δb := by
      calc L * d ≤ (4 * u + 2 * v) * ((u + v) * δb / blo ^ 2) :=
            mul_le_mul hL (le_trans hd hD) hd0 (by positivity)
        _ = (4 * u + 2 * v) * (u + v) / blo ^ 2 * δb := by ring
        _ ≤ (3 * u + 2 * v) ^ 2 / blo ^ 2 * δb := by
            apply mul_le_mul_of_nonneg_right _ hδ0
            apply div_le_div_of_nonneg_right _ (by positivity)
            nlinarith only [hu0, hv0]
    have : (3 * u + 2 * v) ^ 2 / blo ^ 2 * δb + 3 * pb ^ 2 * δb ≤ C1 * δb := by
      rw [hC1]; nlinarith only [hδ0, hpb]
    linarith only [k, this, hδ, hα]
  have hα3 : pb * (α / (6 * pb)) = α / 6 := by field_simp
  -- Lipschitz constants
  have hc1 : |E + (1 - g) * (y - l)| ≤ v := by
    rw [abs_le, hv]; constructor <;> nlinarith only [hE0, hE1, hg0, hg1, hy, hl, hlb]
  have hc1h : |Sh + (1 - gh) * (y - lh)| ≤ v := by
    rw [abs_le, hv]; constructor <;> nlinarith only [hSh0, hSh1, hgh0, hgh1, hy, hlh, hlhb]
  have hcE : |E| ≤ v := by rw [abs_of_nonneg hE0, hv]; linarith only [hE1, hlb, hy]
  have hcS : |Sh| ≤ v := by rw [abs_of_nonneg hSh0, hv]; linarith only [hSh1, hlhb, hy]
  have hgb : g * b * pb ≤ u := by
    rw [hu]; have := mul_le_mul hg1 hbbh hb0.le zero_le_one
    nlinarith only [this, hpb]
  have hghb : gh * bh * pb ≤ u := by
    rw [hu]; have := mul_le_mul hgh1 hbh2 hbh0.le zero_le_one
    nlinarith only [this, hpb]
  have hbpb : b * pb ≤ u := by rw [hu]; nlinarith only [hbbh, hpb]
  have hbhpb : bh * pb ≤ u := by rw [hu]; nlinarith only [hbh2, hpb]
  -- splitting into the cases
  by_cases hqt : q < pt
  · rw [if_pos hqt, if_pos hqt]
    by_cases hqh : q < ph
    · -- Case 1
      rw [if_pos hqh, if_pos hqh]
      have k := hD1 q hq0 (le_trans (le_min (le_min hqh.le hqt.le) hq1) (le_max_left _ _))
      have : 3 * pb ^ 2 * δb + α / 6 ≤ α := by nlinarith only [h5, hδ, hδ0, hpb, hα]
      exact ⟨le_trans k this, le_trans k this⟩
    · -- Case 3b: p̂~ ≤ q < p̃
      push_neg at hqh
      rw [if_neg (not_lt.2 hqh), if_neg (not_lt.2 hqh)]
      obtain ⟨a, ha⟩ : ∃ a, a = max ph 0 := ⟨_, rfl⟩
      have ha0 : 0 ≤ a := by rw [ha]; exact le_max_right _ _
      have haq : a ≤ q := by rw [ha]; exact max_le hqh hq0
      have ha1 : a ≤ pb := le_trans haq hq1
      have hda : q - a ≤ |ph - pt| := by
        have : q - a ≤ pt - ph := by rw [ha]; linarith only [le_max_left ph 0, hqt]
        exact le_trans this (by rw [abs_sub_comm]; exact le_abs_self _)
      have hRa : |Rh a - R a| ≤ 3 * pb ^ 2 * δb + α / 6 := by
        apply hD1 a ha0
        rcases le_total ph 0 with h | h
        · rw [ha, max_eq_right h]; exact le_max_right _ _
        · rw [ha, max_eq_left h]
          exact le_trans (le_min (le_min le_rfl (by linarith only [hqh, hqt]))
            (by linarith only [hqh, hq1])) (le_max_left _ _)
      have hj1 : R1h a = Rh a := by
        rcases le_total ph 0 with h | h
        · rw [ha, max_eq_right h, hRh0, hR1h]; ring
        · rw [ha, max_eq_left h]; exact jh1.symm
      have hj2 : R2h a = Rh a := by
        rcases le_total ph 0 with h | h
        · rw [ha, max_eq_right h, hRh0, hR2h]; ring
        · rw [ha, max_eq_left h]; exact jh2.symm
      have lr := lipR q a hq0 hq1 ha0 ha1
      have hqa : |q - a| = q - a := abs_of_nonneg (by linarith only [haq])
      rw [hqa] at lr
      have hd0 : 0 ≤ q - a := by linarith only [haq]
      constructor
      · have l1 := lip_quad (gh * bh) (Sh + (1 - gh) * (y - lh)) pb (by positivity) q a hq0 hq1
          ha0 ha1
        rw [← hR1h, ← hR1h, hqa, hj1] at l1
        have t := tri3 (R1h q) (R1h a) (R a) (R q)
        rw [hj1, abs_sub_comm (R a)] at t
        have key := hcase3 ((2 * (gh * bh) * pb + |Sh + (1 - gh) * (y - lh)|) + (y + pb * b))
          (q - a) (by positivity) (by linarith only [hghb, hc1h, hbpb, hv, hy, hu0, hl, hlb]) hd0 hda
        rw [add_mul] at key
        linarith only [t, l1, lr, hRa, key]
      · have l2 := lip_quad bh Sh pb hbh0.le q a hq0 hq1 ha0 ha1
        rw [← hR2h, ← hR2h, hqa, hj2] at l2
        have t := tri3 (R2h q) (R2h a) (R a) (R q)
        rw [hj2, abs_sub_comm (R a)] at t
        have key := hcase3 ((2 * bh * pb + |Sh|) + (y + pb * b))
          (q - a) (by positivity) (by linarith only [hbhpb, hcS, hbpb, hv, hy, hu0, hl, hlb]) hd0 hda
        rw [add_mul] at key
        linarith only [t, l2, lr, hRa, key]
  · push_neg at hqt
    rw [if_neg (not_lt.2 hqt), if_neg (not_lt.2 hqt)]
    by_cases hqh : q < ph
    · -- Case 3a: p̃ ≤ q < p̂~
      rw [if_pos hqh, if_pos hqh]
      obtain ⟨a, ha⟩ : ∃ a, a = max pt 0 := ⟨_, rfl⟩
      have ha0 : 0 ≤ a := by rw [ha]; exact le_max_right _ _
      have haq : a ≤ q := by rw [ha]; exact max_le hqt hq0
      have ha1 : a ≤ pb := le_trans haq hq1
      have hda : q - a ≤ |ph - pt| := by
        have : q - a ≤ ph - pt := by rw [ha]; linarith only [le_max_left pt 0, hqh]
        exact le_trans this (le_abs_self _)
      have hRa : |Rh a - R a| ≤ 3 * pb ^ 2 * δb + α / 6 := by
        apply hD1 a ha0
        rcases le_total pt 0 with h | h
        · rw [ha, max_eq_right h]; exact le_max_right _ _
        · rw [ha, max_eq_left h]
          exact le_trans (le_min (le_min (by linarith only [hqh, hqt]) le_rfl)
            (by linarith only [hqt, hq1])) (le_max_left _ _)
      have hj1 : R a = R1 a := by
        rcases le_total pt 0 with h | h
        · rw [ha, max_eq_right h, hR0, hR1]; ring
        · rw [ha, max_eq_left h]; exact jt1
      have hj2 : R a = R2 a := by
        rcases le_total pt 0 with h | h
        · rw [ha, max_eq_right h, hR0, hR2]; ring
        · rw [ha, max_eq_left h]; exact jt2
      have lh' := lipRh q a hq0 hq1 ha0 ha1
      have hqa : |q - a| = q - a := abs_of_nonneg (by linarith only [haq])
      rw [hqa] at lh'
      have hd0 : 0 ≤ q - a := by linarith only [haq]
      constructor
      · have l1 := lip_quad (g * b) (E + (1 - g) * (y - l)) pb (by positivity) a q ha0 ha1
          hq0 hq1
        rw [← hR1, ← hR1, abs_sub_comm a q, hqa] at l1
        have t := tri3 (Rh q) (Rh a) (R a) (R1 q)
        rw [hj1] at t hRa
        have key := hcase3 ((y + bh * pb + pb * bh) + (2 * (g * b) * pb + |E + (1 - g) * (y - l)|))
          (q - a) (by positivity) (by linarith only [hbhpb, hgb, hc1, hv, hy, hu0, hl, hlb]) hd0 hda
        linarith only [t, l1, lh', hRa, key]
      · have l2 := lip_quad b E pb hb0.le a q ha0 ha1 hq0 hq1
        rw [← hR2, ← hR2, abs_sub_comm a q, hqa] at l2
        have t := tri3 (Rh q) (Rh a) (R a) (R2 q)
        rw [hj2] at t hRa
        have key := hcase3 ((y + bh * pb + pb * bh) + (2 * b * pb + |E|))
          (q - a) (by positivity) (by linarith only [hbhpb, hbpb, hcE, hv, hy, hu0, hl, hlb]) hd0 hda
        linarith only [t, l2, lh', hRa, key]
    · -- Case 2
      push_neg at hqh
      rw [if_neg (not_lt.2 hqh), if_neg (not_lt.2 hqh), hR1h, hR1, hR2h, hR2]
      constructor
      · have k := c2max q pb b bh g gh l lh y E Sh bhi lB hq0 hq1 hb0.le hbbh hgh0 hgh1
          hl.le hlb hy (by rw [hδb] at hlhl; exact hlhl)
        rw [← hδb, ← hΔγ] at k
        rw [show (-(gh * bh) * q + (Sh + (1 - gh) * (y - lh))) =
          -(gh * bh) * q + Sh + (1 - gh) * (y - lh) by ring,
          show (-(g * b) * q + (E + (1 - g) * (y - l))) =
          -(g * b) * q + E + (1 - g) * (y - l) by ring]
        refine le_trans k ?_
        have e1 : q * (q * (δb + bhi * Δγ) + |Sh - E| + (y + lB) * Δγ + 2 * (pb * δb))
            ≤ pb * (pb * (δb + bhi * Δγ) + (pb * δb + α / (6 * pb)) + (y + lB) * Δγ +
              2 * (pb * δb)) := by
          apply mul_le_mul hq1 _ (by
            have a1 := mul_nonneg hq0 (add_nonneg hδ0 (mul_nonneg hbhi0 hΔ0))
            have a2 := mul_nonneg (add_nonneg hy (le_trans hl.le hlb)) hΔ0
            have a3 := mul_nonneg hpb.le hδ0
            have a4 := abs_nonneg (Sh - E)
            linarith only [a1, a2, a3, a4]) hpb.le
          have : q * (δb + bhi * Δγ) ≤ pb * (δb + bhi * Δγ) :=
            mul_le_mul_of_nonneg_right hq1 (by positivity)
          linarith only [this, hSE]
        have e2 : pb * (pb * (δb + bhi * Δγ) + (pb * δb + α / (6 * pb)) + (y + lB) * Δγ +
            2 * (pb * δb)) = 4 * pb ^ 2 * δb + C2 * Δγ + pb * (α / (6 * pb)) := by
          rw [hC2]; ring
        rw [hα3] at e2
        nlinarith only [e1, e2, h5, hδ, hγ', hδ0, hpb]
      · have k := c2min q pb b bh E Sh hq0 hq1
        rw [← hδb] at k
        refine le_trans k ?_
        have e1 : q * (q * δb + |Sh - E|) ≤ pb * (pb * δb + (pb * δb + α / (6 * pb))) := by
          apply mul_le_mul hq1 _ (by
            have a1 := mul_nonneg hq0 hδ0
            have a4 := abs_nonneg (Sh - E)
            linarith only [a1, a4]) hpb.le
          have : q * δb ≤ pb * δb := mul_le_mul_of_nonneg_right hq1 hδ0
          linarith only [this, hSE]
        have e2 : pb * (pb * δb + (pb * δb + α / (6 * pb))) = 2 * pb ^ 2 * δb + α / 6 := by
          rw [← hα3]; ring
        nlinarith only [e1, e2, h5, hδ, hδ0, hpb]


/-! ### Probability bounds -/

lemma coord_null {K : ℕ} (I : Instance K) (hP : IsProbabilityMeasure I.μξ) (Nv : Fin K → ℕ)
    (i : Fin K) (j : Fin (Nv i)) (s : Set ℝ) (hs : MeasurableSet s) (h0 : I.μξ s = 0) :
    dataLaw I Nv {ω : Sample K Nv | ω i j ∈ s} = 0 := by
  have h1 : MeasurePreserving (Function.eval i) (dataLaw I Nv)
      (Measure.pi (fun _ : Fin (Nv i) => I.μξ)) := by
    unfold dataLaw; exact measurePreserving_eval _ i
  have h2 : MeasurePreserving (Function.eval j) (Measure.pi (fun _ : Fin (Nv i) => I.μξ)) I.μξ :=
    measurePreserving_eval _ j
  have h3 := h2.comp h1
  have : {ω : Sample K Nv | ω i j ∈ s} = (Function.eval j ∘ Function.eval i) ⁻¹' s := rfl
  rw [this, h3.measure_preimage hs.nullMeasurableSet, h0]

lemma hoeff_block {K : ℕ} (I : Instance K) (hP : IsProbabilityMeasure I.μξ) (Nv : Fin K → ℕ)
    (i : Fin K) (θ : ℝ → ℝ) (hθ : Measurable θ) {a b : ℝ}
    (hab : ∀ᵐ x ∂I.μξ, a ≤ θ x ∧ θ x ≤ b) {ε : ℝ} (hε : 0 < ε) :
    dataLaw I Nv {ω : Sample K Nv | ε < |(∑ j, θ (ω i j)) / (Nv i : ℝ) - ∫ x, θ x ∂I.μξ|} ≤
      ENNReal.ofReal (2 * Real.exp (-(2 * (Nv i : ℝ) * ε ^ 2 / (b - a) ^ 2))) := by
  have hH := UnderstandingML.hoeffding_inequality I.μξ θ hθ hab (Nv i) hε
  have hmp : MeasurePreserving (Function.eval i) (dataLaw I Nv)
      (Measure.pi (fun _ : Fin (Nv i) => I.μξ)) := by
    unfold dataLaw; exact measurePreserving_eval _ i
  have hmeas : Measurable (fun x : Fin (Nv i) → ℝ =>
      |(∑ j, θ (x j)) / (Nv i : ℝ) - ∫ x, θ x ∂I.μξ|) := by
    have : Measurable (fun x : Fin (Nv i) → ℝ => ∑ j, θ (x j)) :=
      Finset.measurable_sum _ (fun j _ => hθ.comp (measurable_pi_apply j))
    exact ((this.div_const _).sub_const _).abs
  have : {ω : Sample K Nv | ε < |(∑ j, θ (ω i j)) / (Nv i : ℝ) - ∫ x, θ x ∂I.μξ|} =
      Function.eval i ⁻¹' {x : Fin (Nv i) → ℝ | ε < |(∑ j, θ (x j)) / (Nv i : ℝ) -
        ∫ x, θ x ∂I.μξ|} := rfl
  rw [this, hmp.measure_preimage (measurableSet_lt measurable_const hmeas).nullMeasurableSet]
  exact hH

end OCPLem2Aux

open OCPLem2Aux in
theorem solution {K : ℕ} [NeZero K] (I : Instance K) (hI : I.Standing) (Nv : Fin K → ℕ) {α : ℝ}
    (hα : 0 < α) :
    dataLaw I Nv {ω | ((∃ q ∈ Icc I.plo I.phi, α < |RHatMax I.toPublic (sales I ω) q - Rmax I q|) ∨
          (∃ q ∈ Icc I.plo I.phi, α < |RHatMin I.toPublic (sales I ω) q - Rmin I q|)) ∧
        ∀ i, 0 < gammaHat I.toPublic (sales I ω) i} ≤
      ENNReal.ofReal
        (2 * K * Real.exp (-((Nmin Nv : ℝ) * α ^ 2 / (36 * (I.y + I.bhi * I.phi) ^ 2 * I.phi ^ 2))) +
          2 * K * Real.exp (-(priceVar I.toPublic * I.g ^ 2 / (36 * C1 I ^ 2) *
            (Nmin Nv : ℝ) * α ^ 2)) +
          2 * K * Real.exp (-((Nmin Nv : ℝ) * α ^ 2 / (18 * C2 I ^ 2))) +
          2 * K * Real.exp (-((Nmin Nv : ℝ) * α ^ 2 / (18 * I.phi ^ 2 * lamBar I ^ 2)))) := by
  have hP := hI.1
  haveI := hP
  have hplo := hI.2.2.1
  have hlohi := hI.2.2.2.1
  have hpb : 0 < I.phi := lt_trans hplo hlohi
  have hblo := hI.2.2.2.2.1
  have hbb := hI.2.2.2.2.2.1
  have hbbh := hI.2.2.2.2.2.2.1
  have hb0 : 0 < I.b := lt_of_lt_of_le hblo hbb
  have hl := lam_pos I hI
  have hlb := lam_le_lamBar I hI
  have hK2 := hI.2.2.2.2.2.2.2.1
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hv0 : 0 < lamBar I + I.y := by linarith [hI.2.1]
  have hu0 : 0 ≤ I.bhi * I.phi := mul_nonneg (by linarith) hpb.le
  have hC1pos : 0 < C1 I := by unfold C1; positivity
  have hC2pos : 0 < C2 I := by
    unfold C2; exact mul_pos hpb (by nlinarith [hI.2.1])
  set E := ∫ ξ, min ξ (lam I) ∂I.μξ with hE
  set α1 := α / (2 * C1 I) with hα1
  set α0 := α / 6 with hα0
  set α2 := α / (6 * C2 I) with hα2
  set α3 := α / (6 * I.phi) with hα3
  have hα1p : 0 < α1 := by positivity
  have hα0p : 0 < α0 := by positivity
  have hα2p : 0 < α2 := by positivity
  have hα3p : 0 < α3 := by positivity
  set A1 := {ω : Sample K Nv | α1 < |bHat I.toPublic (sales I ω) - I.b| ∧
        ∀ i, 0 < gammaHat I.toPublic (sales I ω) i} with hA1
  set A2 := {ω : Sample K Nv | ∃ q : ℝ, 0 ≤ q ∧
        q ≤ max (min (min (pTildeHat I.toPublic (sales I ω)) (pTilde I)) I.phi) 0 ∧
        3 * I.phi ^ 2 * |bHat I.toPublic (sales I ω) - I.b| + α0 <
          |RHat I.toPublic (sales I ω) q - RF I I.μξ q|} with hA2
  set A3 := {ω : Sample K Nv | α2 < |gammaHatMax I.toPublic (sales I ω) - gam I|} with hA3
  set A4 := ⋃ i, {ω : Sample K Nv |
    α3 < |(∑ j, (fun x => min x (lam I)) (ω i j)) / (Nv i : ℝ) - ∫ x, min x (lam I) ∂I.μξ|}
    with hA4
  set G := ⋃ i, ⋃ j : Fin (Nv i), {ω : Sample K Nv | ω i j ∈ Iio (I.b * I.phi)} with hG
  -- the inclusion
  have hsub : {ω | ((∃ q ∈ Icc I.plo I.phi, α < |RHatMax I.toPublic (sales I ω) q - Rmax I q|) ∨
          (∃ q ∈ Icc I.plo I.phi, α < |RHatMin I.toPublic (sales I ω) q - Rmin I q|)) ∧
        ∀ i, 0 < gammaHat I.toPublic (sales I ω) i} ⊆ A1 ∪ A2 ∪ A3 ∪ A4 ∪ G := by
    rintro ω ⟨hbad, hpos⟩
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨⟨⟨⟨n1, n2⟩, n3⟩, n4⟩, n5⟩ := hnot
    -- consequences
    have hG' : ∀ i j, I.b * I.phi ≤ ω i j := by
      intro i j; by_contra h; push_neg at h
      exact n5 (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, h⟩⟩)
    have hN : ∀ i, 0 < Nv i := by
      intro i
      by_contra h0
      have h0' : Nv i = 0 := by omega
      have := hpos i
      unfold gammaHat at this
      have hz : ((Nv i : ℕ) : ℝ) = 0 := by exact_mod_cast h0'
      rw [hz, div_zero] at this
      exact lt_irrefl _ this
    set S := sales I ω with hSdef
    have hS0 : ∀ i j, 0 ≤ S i j := by
      intro i j
      have hp := (hI.2.2.2.2.2.2.2.2.2.1 i).2
      have := hG' i j
      exact le_min (by nlinarith) (hI.2.2.2.2.2.2.2.2.2.2.1 i)
    have hSy : ∀ i j, S i j ≤ I.yh i := fun i j => min_le_right _ _
    have h1 : |bHat I.toPublic S - I.b| ≤ α1 := by
      by_contra h; push_neg at h; exact n1 ⟨h, hpos⟩
    have hD1 : ∀ q, 0 ≤ q → q ≤ max (min (min (pTildeHat I.toPublic S) (pTilde I)) I.phi) 0 →
        |RHat I.toPublic S q - RF I I.μξ q| ≤ 3 * I.phi ^ 2 * |bHat I.toPublic S - I.b| + α0 := by
      intro q hq0 hq1; by_contra h; push_neg at h; exact n2 ⟨q, hq0, hq1, h⟩
    have hγ : |gammaHatMax I.toPublic S - gam I| ≤ α2 := by
      by_contra h; push_neg at h; exact n3 h
    have hH : ∀ i, |(∑ j, min (ω i j) (lam I)) / (Nv i : ℝ) - E| ≤ α3 := by
      intro i; by_contra h; push_neg at h; exact n4 (mem_iUnion.2 ⟨i, h⟩)
    -- (D.12)
    have hSE : |shiftedMean I.toPublic S - E| ≤ I.phi * |bHat I.toPublic S - I.b| + α3 := by
      set i := iStar I.toPublic S
      have hmd := mean_diff (hN i) (fun j => S i j + bHat I.toPublic S * I.p i)
        (fun j => min (ω i j) (lam I)) (I.phi * |bHat I.toPublic S - I.b|) (fun j => by
          have e : S i j + bHat I.toPublic S * I.p i =
              min (ω i j + (bHat I.toPublic S - I.b) * I.p i) (lamHat I.toPublic S) := by
            rw [hSdef]; unfold sales lamHat
            rw [← min_add_add_right]; congr 1; ring
          rw [e]
          refine le_trans (abs_min_sub_min_le_max _ _ _ _) (max_le ?_ ?_)
          · rw [show ω i j + (bHat I.toPublic S - I.b) * I.p i - ω i j =
              (bHat I.toPublic S - I.b) * I.p i by ring, abs_mul, mul_comm]
            have hp := hI.2.2.2.2.2.2.2.2.2.1 i
            rw [abs_of_nonneg (le_trans hplo.le hp.1)]
            exact mul_le_mul_of_nonneg_right hp.2 (abs_nonneg _)
          · exact lamHat_sub I hI S)
      have := hH i
      have e2 : shiftedMean I.toPublic S =
          (∑ j, (S i j + bHat I.toPublic S * I.p i)) / (Nv i : ℝ) := rfl
      rw [e2]
      calc |(∑ j, (S i j + bHat I.toPublic S * I.p i)) / (Nv i : ℝ) - E|
          ≤ |(∑ j, (S i j + bHat I.toPublic S * I.p i)) / (Nv i : ℝ) -
              (∑ j, min (ω i j) (lam I)) / (Nv i : ℝ)| +
            |(∑ j, min (ω i j) (lam I)) / (Nv i : ℝ) - E| := abs_sub_le _ _ _
        _ ≤ _ := add_le_add hmd this
    -- apply the deterministic part
    obtain ⟨jt1, jt2⟩ := junction_true I hI
    obtain ⟨jh1, jh2⟩ := junction I.toPublic S hblo hSy (hN _)
    obtain ⟨hSh0, hSh1⟩ := shiftedMean_mem I hI S hS0 hSy (hN _)
    obtain ⟨hE0, hE1⟩ := E_mem I hI
    have key : ∀ q ∈ Icc I.plo I.phi,
        |(if q < pTildeHat I.toPublic S then RHat I.toPublic S q else R1Hat I.toPublic S q) -
          (if q < pTilde I then RF I I.μξ q else R1 I q)| ≤ α ∧
        |(if q < pTildeHat I.toPublic S then RHat I.toPublic S q else R2Hat I.toPublic S q) -
          (if q < pTilde I then RF I I.μξ q else R2 I q)| ≤ α := fun q hq =>
      detR I.phi I.plo I.y I.b (bHat I.toPublic S) I.bhi I.blo (lam I) (lamHat I.toPublic S)
        (lamBar I) (gam I) (gammaHatMax I.toPublic S) E (shiftedMean I.toPublic S) α q
        (pTilde I) (pTildeHat I.toPublic S) (C1 I) (C2 I)
        (RF I I.μξ) (RHat I.toPublic S) (R1 I) (R2 I) (R1Hat I.toPublic S) (R2Hat I.toPublic S)
        hplo hq hI.2.1 hblo hbb hbbh (bHat_mem I hI S).1 (bHat_mem I hI S).2 hl hlb
        (lamHat_pos I hI S) (lamHat_le I hI S) (lamHat_sub I hI S)
        (gammaHatMax_mem I hI S).1 (gammaHatMax_mem I hI S).2 (gam_mem I hI).1 (gam_mem I hI).2
        hSh0 hSh1 hE0 hE1 hα rfl rfl (by unfold C1; ring) rfl
        (fun r => by unfold R1; ring) (fun r => rfl) (fun r => by unfold R1Hat; ring) (fun r => rfl)
        h1 hD1 hγ hSE jt1 jt2 jh1 jh2 (by unfold RF; ring) (by unfold RHat; ring)
        (fun r a hr0 hr1 ha0 ha1 => lip_true I hI r a hr0 hr1 ha0 ha1)
        (fun r a hr0 hr1 ha0 ha1 => lip_hat I.toPublic S I.phi
          (le_trans hblo.le (bHat_mem I hI S).1) hI.2.1 (fun j => by
            have := hS0 (iStar I.toPublic S) j
            have : 0 ≤ bHat I.toPublic S * I.p (iStar I.toPublic S) :=
              mul_nonneg (le_trans hblo.le (bHat_mem I hI S).1)
                (le_trans hplo.le (hI.2.2.2.2.2.2.2.2.2.1 _).1)
            linarith) (hN _) r a hr0 hr1 ha0 ha1)
    rcases hbad with ⟨q, hq, hlt⟩ | ⟨q, hq, hlt⟩
    · have := (key q hq).1
      rw [(proposition_2 I hI q hq).2.2.1] at hlt
      exact absurd this (not_le.2 hlt)
    · have := (key q hq).2
      rw [(proposition_2 I hI q hq).2.2.2] at hlt
      exact absurd this (not_le.2 hlt)
  -- measures of the pieces
  have mG : dataLaw I Nv G = 0 := by
    rw [hG]
    refine measure_iUnion_null (fun i => measure_iUnion_null (fun j => ?_))
    exact coord_null I hP Nv i j _ measurableSet_Iio hI.2.2.2.2.2.2.2.2.2.2.2.1
  have m1 := lemma_1 I hI Nv hα1p
  have m2 := lemma_D_1 I hI Nv hα0p
  have m3 := lemma_D_2 I hI Nv hα2p
  have m4 : dataLaw I Nv A4 ≤ ENNReal.ofReal
      (2 * K * Real.exp (-((Nmin Nv : ℝ) * α ^ 2 / (18 * I.phi ^ 2 * lamBar I ^ 2)))) := by
    rw [hA4]
    refine le_trans (measure_iUnion_fintype_le _ _) ?_
    have hab : ∀ᵐ x ∂I.μξ, (0 : ℝ) ≤ (fun x => min x (lam I)) x ∧
        (fun x => min x (lam I)) x ≤ lam I := by
      filter_upwards [ae_ge I hI] with x hx
      exact ⟨le_min (by nlinarith) hl.le, min_le_right _ _⟩
    have hone : ∀ i, dataLaw I Nv {ω : Sample K Nv | α3 < |(∑ j, (fun x => min x (lam I)) (ω i j)) /
        (Nv i : ℝ) - ∫ x, min x (lam I) ∂I.μξ|} ≤
        ENNReal.ofReal (2 * Real.exp (-((Nmin Nv : ℝ) * α ^ 2 / (18 * I.phi ^ 2 * lamBar I ^ 2))))
        := by
      intro i
      refine le_trans (hoeff_block I hP Nv i _ (measurable_id.min measurable_const) hab hα3p) ?_
      apply ENNReal.ofReal_le_ofReal
      have hNi : (Nmin Nv : ℝ) ≤ Nv i := by
        exact_mod_cast ciInf_le (Finite.bddBelow_range Nv) i
      have : Real.exp (-(2 * (Nv i : ℝ) * α3 ^ 2 / (lam I - 0) ^ 2)) ≤
          Real.exp (-((Nmin Nv : ℝ) * α ^ 2 / (18 * I.phi ^ 2 * lamBar I ^ 2))) := by
        apply Real.exp_le_exp.2
        rw [sub_zero, hα3]
        have e : 2 * (Nv i : ℝ) * (α / (6 * I.phi)) ^ 2 / lam I ^ 2 =
            (Nv i : ℝ) * α ^ 2 / (18 * I.phi ^ 2 * lam I ^ 2) := by
          field_simp; ring
        rw [e, neg_le_neg_iff]
        have hN0 : (0 : ℝ) ≤ Nmin Nv := Nat.cast_nonneg _
        calc (Nmin Nv : ℝ) * α ^ 2 / (18 * I.phi ^ 2 * lamBar I ^ 2)
            ≤ (Nv i : ℝ) * α ^ 2 / (18 * I.phi ^ 2 * lamBar I ^ 2) := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_right hNi (by positivity)
          _ ≤ (Nv i : ℝ) * α ^ 2 / (18 * I.phi ^ 2 * lam I ^ 2) := by
              apply div_le_div_of_nonneg_left (by positivity) (by positivity)
              have : lam I ^ 2 ≤ lamBar I ^ 2 := pow_le_pow_left₀ hl.le hlb 2
              nlinarith [sq_nonneg I.phi]
      linarith
    calc ∑ i, dataLaw I Nv _ ≤ ∑ _i : Fin K, ENNReal.ofReal
          (2 * Real.exp (-((Nmin Nv : ℝ) * α ^ 2 / (18 * I.phi ^ 2 * lamBar I ^ 2)))) :=
          Finset.sum_le_sum (fun i _ => hone i)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  -- exponents
  have e1 : (1 / (9 * (K : ℝ)) * (∑ i, (I.p i - (1 / (K : ℝ)) * ∑ j, I.p j) ^ 2) * I.g ^ 2 *
      (Nmin Nv : ℝ) * α1 ^ 2) = priceVar I.toPublic * I.g ^ 2 / (36 * C1 I ^ 2) *
      (Nmin Nv : ℝ) * α ^ 2 := by
    rw [hα1]; unfold priceVar; field_simp; ring
  have e2 : (Nmin Nv : ℝ) * α0 ^ 2 / ((I.y + I.bhi * I.phi) ^ 2 * I.phi ^ 2) =
      (Nmin Nv : ℝ) * α ^ 2 / (36 * (I.y + I.bhi * I.phi) ^ 2 * I.phi ^ 2) := by
    rw [hα0]; field_simp; ring
  have e3 : 2 * (Nmin Nv : ℝ) * α2 ^ 2 = (Nmin Nv : ℝ) * α ^ 2 / (18 * C2 I ^ 2) := by
    rw [hα2]; field_simp; ring
  rw [e1] at m1
  rw [e2] at m2
  rw [e3] at m3
  calc _ ≤ dataLaw I Nv (A1 ∪ A2 ∪ A3 ∪ A4 ∪ G) := measure_mono hsub
    _ ≤ dataLaw I Nv A1 + dataLaw I Nv A2 + dataLaw I Nv A3 + dataLaw I Nv A4 + dataLaw I Nv G := by
        refine le_trans (measure_union_le _ _) (add_le_add ?_ le_rfl)
        refine le_trans (measure_union_le _ _) (add_le_add ?_ le_rfl)
        refine le_trans (measure_union_le _ _) (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ _ := by
        rw [mG, add_zero]
        refine le_trans (add_le_add (add_le_add (add_le_add m1 m2) m3) m4) ?_
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply le_of_eq
        congr 1
        ring
