-- Prove2me | solution 1 for UnderstandingML.linear_l2_generalization
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T16:33:25.524607+00:00
-- url     : https://prove2.me/submissions/8a551e6a-dc0a-4f2b-880e-7baee180b058

import Theorems.Thm_UnderstandingML_rademacher_generalization
import Theorems.Thm_UnderstandingML_contraction_lemma
import Theorems.Thm_UnderstandingML_rademacher_linearEvalSet_le
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML.LinearGenAux

lemma abs_signVec {m : ℕ} (σ : Fin m → Bool) (i : Fin m) : |signVec σ i| = 1 := by
  unfold signVec; cases σ i <;> simp

lemma abs_signed_sum_le {m : ℕ} (σ : Fin m → Bool) (x : Fin m → ℝ) (C : ℝ)
    (hx : ∀ i, |x i| ≤ C) : |∑ i, signVec σ i * x i| ≤ m * C := by
  calc |∑ i, signVec σ i * x i| ≤ ∑ i, |signVec σ i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |x i| := by simp only [abs_mul, abs_signVec, one_mul]
    _ ≤ ∑ _i : Fin m, C := Finset.sum_le_sum (fun i _ ↦ hx i)
    _ = m * C := by simp

lemma bddAbove_of_abs {ι : Type*} (f : ι → ℝ) (C : ℝ) (hf : ∀ i, |f i| ≤ C) :
    BddAbove (Set.range f) :=
  ⟨C, by rintro _ ⟨i, rfl⟩; exact (le_abs_self _).trans (hf i)⟩

/-- The Rademacher complexity of `ℓ ∘ H ∘ S` as a supremum over `H`. -/
lemma iSup_evalSet {Z Hyp : Type*} (loss : Hyp → Z → ℝ) (H : Set Hyp) {m : ℕ}
    (hH : H.Nonempty) (c : ℝ) (hc : ∀ h ∈ H, ∀ z, |loss h z| ≤ c)
    (S : Fin m → Z) (σ : Fin m → Bool) :
    (⨆ a : evalSet (lossClass loss H) S, ∑ i, signVec σ i * (a : Fin m → ℝ) i) =
      ⨆ h : H, ∑ i, signVec σ i * loss h (S i) := by
  have : Nonempty H := hH.to_subtype
  obtain ⟨h0, hh0⟩ := hH
  have hne : Nonempty (evalSet (lossClass loss H) S) :=
    ⟨⟨fun i ↦ loss h0 (S i), loss h0, ⟨h0, hh0, rfl⟩, rfl⟩⟩
  have hb1 : BddAbove (Set.range fun h : H ↦ ∑ i, signVec σ i * loss h (S i)) :=
    bddAbove_of_abs _ (m * c) (fun h ↦ abs_signed_sum_le σ _ c (fun i ↦ hc h h.2 _))
  have hb2 : BddAbove (Set.range fun a : evalSet (lossClass loss H) S ↦
      ∑ i, signVec σ i * (a : Fin m → ℝ) i) := by
    refine bddAbove_of_abs _ (m * c) (fun a ↦ ?_)
    obtain ⟨v, f, ⟨h, hh, rfl⟩, rfl⟩ := a
    exact abs_signed_sum_le σ _ c (fun i ↦ hc h hh _)
  refine le_antisymm (ciSup_le fun a ↦ ?_) (ciSup_le fun h ↦ ?_)
  · obtain ⟨v, f, ⟨h, hh, rfl⟩, rfl⟩ := a
    exact le_ciSup hb1 ⟨h, hh⟩
  · exact le_ciSup hb2 ⟨fun i ↦ loss h (S i), loss h, ⟨h, h.2, rfl⟩, rfl⟩

variable {E : Type*} [NormedAddCommGroup E]

/-- A supremum of a Lipschitz, bounded function over `H` equals its supremum over a dense
subset `H₀ ⊆ H`. -/
lemma iSup_eq_iSup_dense (H H0 : Set E) (hsub : H0 ⊆ H) (hne : H0.Nonempty)
    (hdense : ∀ w ∈ H, ∀ ε > 0, ∃ w0 ∈ H0, ‖w - w0‖ < ε) (F : E → ℝ) (K C : ℝ) (hK : 0 ≤ K)
    (hF : ∀ w ∈ H, ∀ w' ∈ H, |F w - F w'| ≤ K * ‖w - w'‖) (hC : ∀ w ∈ H, |F w| ≤ C) :
    (⨆ w : H, F w) = ⨆ w : H0, F w := by
  have : Nonempty H0 := hne.to_subtype
  have : Nonempty H := (hne.mono hsub).to_subtype
  have hb : BddAbove (Set.range fun w : H ↦ F w) := bddAbove_of_abs _ C (fun w ↦ hC w w.2)
  have hb0 : BddAbove (Set.range fun w : H0 ↦ F w) :=
    bddAbove_of_abs _ C (fun w ↦ hC w (hsub w.2))
  refine le_antisymm (ciSup_le fun w ↦ ?_) (ciSup_le fun w ↦ le_ciSup hb ⟨w, hsub w.2⟩)
  refine le_of_forall_pos_le_add (fun ε hε ↦ ?_)
  obtain ⟨w0, hw0, hd⟩ := hdense w w.2 (ε / (K + 1)) (by positivity)
  have h1 := hF w w.2 w0 (hsub hw0)
  have h2 : F w0 ≤ ⨆ w : H0, F w := le_ciSup hb0 ⟨w0, hw0⟩
  have h3 : K * ‖(w : E) - w0‖ ≤ ε := by
    calc K * ‖(w : E) - w0‖ ≤ (K + 1) * (ε / (K + 1)) := by
          apply mul_le_mul (by linarith) hd.le (norm_nonneg _) (by linarith)
      _ = ε := by field_simp
  linarith [(abs_le.1 h1).2]

/-- Measurability of a supremum over `H` of Lipschitz, bounded, measurable functions, via a
countable dense subset. -/
lemma measurable_iSup_of_dense {Ω : Type*} [MeasurableSpace Ω] (H H0 : Set E) (hsub : H0 ⊆ H)
    (hne : H0.Nonempty) (hc : H0.Countable)
    (hdense : ∀ w ∈ H, ∀ ε > 0, ∃ w0 ∈ H0, ‖w - w0‖ < ε) (G : E → Ω → ℝ) (K C : ℝ) (hK : 0 ≤ K)
    (hGm : ∀ w, Measurable (G w))
    (hGl : ∀ ω, ∀ w ∈ H, ∀ w' ∈ H, |G w ω - G w' ω| ≤ K * ‖w - w'‖)
    (hGb : ∀ ω, ∀ w ∈ H, |G w ω| ≤ C) :
    Measurable (fun ω ↦ ⨆ w : H, G w ω) := by
  have : Countable H0 := hc.to_subtype
  have e : (fun ω ↦ ⨆ w : H, G w ω) = fun ω ↦ ⨆ w : H0, G w ω := by
    funext ω
    exact iSup_eq_iSup_dense H H0 hsub hne hdense (fun w ↦ G w ω) K C hK (hGl ω) (hGb ω)
  rw [e]
  exact Measurable.iSup (fun w ↦ hGm w)

end UnderstandingML.LinearGenAux

open UnderstandingML UnderstandingML.LinearGenAux in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Y : Type*} [MeasurableSpace Y]
    (D : Measure (E × Y)) [IsProbabilityMeasure D] (R : ℝ) (hR : D {p | R < ‖p.1‖} = 0)
    (B : ℝ) (hB : 0 ≤ B) (φ : ℝ → Y → ℝ) (hφm : Measurable (Function.uncurry φ)) (ρ : NNReal)
    (hφ : ∀ y, LipschitzWith ρ (fun a ↦ φ a y)) (c : ℝ)
    (hc : ∀ a y, |a| ≤ B * R → |φ a y| ≤ c) (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    iidLaw D m {S | ∃ w : E, ‖w‖ ≤ B ∧
      empRisk (fun w p ↦ φ ⟪w, p.1⟫_ℝ p.2) S w + 2 * ρ * B * R / Real.sqrt m +
        c * Real.sqrt (2 * Real.log (2 / δ) / m) < risk (fun w p ↦ φ ⟪w, p.1⟫_ℝ p.2) D w} ≤
      ENNReal.ofReal δ := by
  classical
  -- `R ≥ 0`
  have hR0 : 0 ≤ R := by
    by_contra hneg
    replace hneg : R < 0 := lt_of_not_ge hneg
    have : {p : E × Y | R < ‖p.1‖} = Set.univ :=
      Set.eq_univ_of_forall (fun p ↦ lt_of_lt_of_le hneg (norm_nonneg _))
    rw [this, measure_univ] at hR
    exact one_ne_zero hR
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hρ0 : (0 : ℝ) ≤ ρ := ρ.2
  -- the projection onto the ball of radius `R`
  set proj : E → E := fun x ↦ (min 1 (R / ‖x‖)) • x with hproj
  have hproj_norm : ∀ x, ‖proj x‖ ≤ R := by
    intro x
    simp only [hproj, norm_smul]
    rcases eq_or_ne ‖x‖ 0 with h0 | h0
    · rw [h0, mul_zero]; exact hR0
    · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (div_nonneg hR0 hxpos.le))]
      calc min 1 (R / ‖x‖) * ‖x‖ ≤ R / ‖x‖ * ‖x‖ :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hxpos.le
        _ = R := div_mul_cancel₀ _ h0
  have hproj_eq : ∀ x, ‖x‖ ≤ R → proj x = x := by
    intro x hx
    simp only [hproj]
    rcases eq_or_ne ‖x‖ 0 with h0 | h0
    · rw [norm_eq_zero.1 h0, smul_zero]
    · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      rw [min_eq_left ((one_le_div hxpos).2 hx), one_smul]
  have hproj_meas : Measurable proj :=
    (measurable_const.min (measurable_const.div measurable_norm)).smul measurable_id
  -- the truncated loss
  set loss : E → E × Y → ℝ := fun w p ↦ φ ⟪w, proj p.1⟫_ℝ p.2 with hloss
  set H : Set E := {w | ‖w‖ ≤ B} with hH
  have hHne : H.Nonempty := ⟨0, by simp [hH, hB]⟩
  have hinner : ∀ w ∈ H, ∀ x, |⟪w, proj x⟫_ℝ| ≤ B * R := by
    intro w hw x
    calc |⟪w, proj x⟫_ℝ| ≤ ‖w‖ * ‖proj x‖ := abs_real_inner_le_norm _ _
      _ ≤ B * R := mul_le_mul hw (hproj_norm x) (norm_nonneg _) hB
  have hlossb : ∀ w ∈ H, ∀ p, |loss w p| ≤ c := fun w hw p ↦ hc _ _ (hinner w hw p.1)
  have hlossm : ∀ w, Measurable (loss w) := by
    intro w
    have : Measurable fun p : E × Y ↦ (⟪w, proj p.1⟫_ℝ, p.2) :=
      (Measurable.inner measurable_const (hproj_meas.comp measurable_fst)).prodMk measurable_snd
    exact hφm.comp this
  have hlip : ∀ w w' : E, ∀ p : E × Y, |loss w p - loss w' p| ≤ ρ * R * ‖w - w'‖ := by
    intro w w' p
    have h1 := (hφ p.2).dist_le_mul ⟪w, proj p.1⟫_ℝ ⟪w', proj p.1⟫_ℝ
    rw [Real.dist_eq, Real.dist_eq, ← inner_sub_left] at h1
    calc |loss w p - loss w' p| ≤ ρ * |⟪w - w', proj p.1⟫_ℝ| := h1
      _ ≤ ρ * (‖w - w'‖ * R) := by
          gcongr
          exact (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left (hproj_norm _) (norm_nonneg _))
      _ = ρ * R * ‖w - w'‖ := by ring
  -- a countable dense subset of the ball
  obtain ⟨T, hTc, hTd⟩ := TopologicalSpace.exists_countable_dense H
  set H0 : Set E := Subtype.val '' T with hH0
  have hH0c : H0.Countable := hTc.image _
  have hsub : H0 ⊆ H := by rintro _ ⟨w, _, rfl⟩; exact w.2
  have hdense : ∀ w ∈ H, ∀ ε > 0, ∃ w0 ∈ H0, ‖w - w0‖ < ε := by
    intro w hw ε hε
    obtain ⟨y, hy, hd⟩ := hTd.exists_dist_lt ⟨w, hw⟩ hε
    exact ⟨y, ⟨y, hy, rfl⟩, by rwa [Subtype.dist_eq, dist_eq_norm] at hd⟩
  have hH0ne : H0.Nonempty := by
    obtain ⟨w0, hw0, _⟩ := hdense 0 (by simp [hH, hB]) 1 one_pos
    exact ⟨w0, hw0⟩
  have hK : (0 : ℝ) ≤ ρ * R := mul_nonneg hρ0 hR0
  -- Lipschitz bounds for the empirical and true risks
  have hemp_lip : ∀ {k : ℕ} (S : Fin k → E × Y) (w w' : E), 0 < k →
      |empRisk loss S w - empRisk loss S w'| ≤ ρ * R * ‖w - w'‖ := by
    intro k S w w' hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    unfold empRisk
    rw [div_sub_div_same, ← Finset.sum_sub_distrib, abs_div, Nat.abs_cast, div_le_iff₀ hk']
    calc |∑ i, (loss w (S i) - loss w' (S i))| ≤ ∑ i, |loss w (S i) - loss w' (S i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin k, ρ * R * ‖w - w'‖ := Finset.sum_le_sum (fun i _ ↦ hlip _ _ _)
      _ = ρ * R * ‖w - w'‖ * k := by simp [mul_comm]
  have hlossi : ∀ w ∈ H, Integrable (loss w) D := fun w hw ↦
    Integrable.of_bound (hlossm w).aestronglyMeasurable c
      (Filter.Eventually.of_forall (fun p ↦ by rw [Real.norm_eq_abs]; exact hlossb w hw p))
  have hrisk_lip : ∀ w ∈ H, ∀ w' ∈ H, |risk loss D w - risk loss D w'| ≤ ρ * R * ‖w - w'‖ := by
    intro w hw w' hw'
    unfold risk
    rw [← integral_sub (hlossi w hw) (hlossi w' hw')]
    have := norm_integral_le_of_norm_le_const (μ := D) (f := fun p ↦ loss w p - loss w' p)
      (C := ρ * R * ‖w - w'‖)
      (Filter.Eventually.of_forall (fun p ↦ by rw [Real.norm_eq_abs]; exact hlip w w' p))
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
  have hemp_b : ∀ {k : ℕ} (S : Fin k → E × Y) (w : E), w ∈ H → 0 < k → |empRisk loss S w| ≤ c := by
    intro k S w hw hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    unfold empRisk
    rw [abs_div, Nat.abs_cast, div_le_iff₀ hk']
    calc |∑ i, loss w (S i)| ≤ ∑ i, |loss w (S i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin k, c := Finset.sum_le_sum (fun i _ ↦ hlossb w hw _)
      _ = c * k := by simp [mul_comm]
  have hrisk_b : ∀ w ∈ H, |risk loss D w| ≤ c := by
    intro w hw
    unfold risk
    have := norm_integral_le_of_norm_le_const (μ := D) (f := loss w) (C := c)
      (Filter.Eventually.of_forall (fun p ↦ by rw [Real.norm_eq_abs]; exact hlossb w hw p))
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
  have hemp_m : ∀ w, Measurable (fun S : Fin m → E × Y ↦ empRisk loss S w) := by
    intro w
    unfold empRisk
    exact (Finset.measurable_sum _ (fun i _ ↦ (hlossm w).comp (measurable_pi_apply i))).div_const _
  -- the three measurability hypotheses of Theorem 26.5
  have hrep : Measurable (fun S : Fin m → E × Y ↦ representativeness loss H D S) := by
    refine measurable_iSup_of_dense H H0 hsub hH0ne hH0c hdense
      (fun w S ↦ risk loss D w - empRisk loss S w) (2 * (ρ * R)) (2 * c) (by linarith)
      (fun w ↦ measurable_const.sub (hemp_m w)) (fun S w hw w' hw' ↦ ?_) (fun S w hw ↦ ?_)
    · have h1 := hrisk_lip w hw w' hw'
      have h2 := hemp_lip S w w' hm
      calc |risk loss D w - empRisk loss S w - (risk loss D w' - empRisk loss S w')|
          ≤ |risk loss D w - risk loss D w'| + |empRisk loss S w - empRisk loss S w'| := by
            rw [show risk loss D w - empRisk loss S w - (risk loss D w' - empRisk loss S w') =
              (risk loss D w - risk loss D w') - (empRisk loss S w - empRisk loss S w') by ring]
            exact abs_sub _ _
        _ ≤ 2 * (ρ * R) * ‖w - w'‖ := by linarith
    · have h1 := hrisk_b w hw
      have h2 := hemp_b S w hw hm
      calc _ ≤ |risk loss D w| + |empRisk loss S w| := abs_sub _ _
        _ ≤ 2 * c := by linarith
  have hradS : ∀ S : Fin m → E × Y, rademacher (evalSet (lossClass loss H) S) =
      (1 / m) * ((1 / 2 ^ m) * ∑ σ : Fin m → Bool, ⨆ w : H, ∑ i, signVec σ i * loss w (S i)) := by
    intro S
    simp only [rademacher]
    congr 2
    exact Finset.sum_congr rfl (fun σ _ ↦ iSup_evalSet loss H hHne c hlossb S σ)
  have hsupm : ∀ σ : Fin m → Bool,
      Measurable (fun S : Fin m → E × Y ↦ ⨆ w : H, ∑ i, signVec σ i * loss w (S i)) := by
    intro σ
    have g1 : ∀ w, Measurable (fun S : Fin m → E × Y ↦ ∑ i, signVec σ i * loss w (S i)) :=
      fun w ↦ Finset.measurable_sum _ (fun i _ ↦
        measurable_const.mul ((hlossm w).comp (measurable_pi_apply i)))
    have g2 : ∀ (S : Fin m → E × Y), ∀ w ∈ H, ∀ w' ∈ H,
        |∑ i, signVec σ i * loss w (S i) - ∑ i, signVec σ i * loss w' (S i)| ≤
          m * (ρ * R) * ‖w - w'‖ := by
      intro S w _ w' _
      rw [← Finset.sum_sub_distrib]
      have := abs_signed_sum_le σ (fun i ↦ loss w (S i) - loss w' (S i)) (ρ * R * ‖w - w'‖)
        (fun i ↦ hlip _ _ _)
      simp only [mul_sub] at this ⊢
      calc _ ≤ m * (ρ * R * ‖w - w'‖) := this
        _ = m * (ρ * R) * ‖w - w'‖ := by ring
    have g3 : ∀ (S : Fin m → E × Y), ∀ w ∈ H, |∑ i, signVec σ i * loss w (S i)| ≤ m * c :=
      fun S w hw ↦ abs_signed_sum_le σ _ c (fun i ↦ hlossb w hw _)
    exact measurable_iSup_of_dense H H0 hsub hH0ne hH0c hdense
      (fun w (S : Fin m → E × Y) ↦ ∑ i, signVec σ i * loss w (S i)) (m * (ρ * R)) (m * c)
      (mul_nonneg (Nat.cast_nonneg m) hK) g1 g2 g3
  have hrad : Measurable (fun S : Fin m → E × Y ↦ rademacher (evalSet (lossClass loss H) S)) := by
    have e : (fun S : Fin m → E × Y ↦ rademacher (evalSet (lossClass loss H) S)) =
        fun S ↦ (1 / m) * ((1 / 2 ^ m) *
          ∑ σ : Fin m → Bool, ⨆ w : H, ∑ i, signVec σ i * loss w (S i)) := funext hradS
    rw [e]
    exact measurable_const.mul (measurable_const.mul
      (Finset.measurable_sum _ (fun σ _ ↦ hsupm σ)))
  have hdbl : Measurable (fun p : (Fin m → E × Y) × (Fin m → E × Y) ↦
      ⨆ h : H, (empRisk loss p.2 (h : E) - empRisk loss p.1 (h : E))) := by
    refine measurable_iSup_of_dense H H0 hsub hH0ne hH0c hdense
      (fun w (p : (Fin m → E × Y) × (Fin m → E × Y)) ↦ empRisk loss p.2 w - empRisk loss p.1 w) (2 * (ρ * R)) (2 * c) (by linarith)
      (fun w ↦ ((hemp_m w).comp measurable_snd).sub ((hemp_m w).comp measurable_fst))
      (fun p w hw w' hw' ↦ ?_) (fun p w hw ↦ ?_)
    · have h1 := hemp_lip p.2 w w' hm
      have h2 := hemp_lip p.1 w w' hm
      calc |empRisk loss p.2 w - empRisk loss p.1 w - (empRisk loss p.2 w' - empRisk loss p.1 w')|
          ≤ |empRisk loss p.2 w - empRisk loss p.2 w'| + |empRisk loss p.1 w - empRisk loss p.1 w'| := by
            rw [show empRisk loss p.2 w - empRisk loss p.1 w - (empRisk loss p.2 w' - empRisk loss p.1 w') =
              (empRisk loss p.2 w - empRisk loss p.2 w') - (empRisk loss p.1 w - empRisk loss p.1 w') by ring]
            exact abs_sub _ _
        _ ≤ 2 * (ρ * R) * ‖w - w'‖ := by linarith
    · have h1 := hemp_b p.2 w hw hm
      have h2 := hemp_b p.1 w hw hm
      calc _ ≤ |empRisk loss p.2 w| + |empRisk loss p.1 w| := abs_sub _ _
        _ ≤ 2 * c := by linarith
  -- Theorem 26.5, part 1
  have h265 := (rademacher_generalization loss H hHne c hlossb (fun w _ ↦ hlossm w) D m hm
    hrep hrad hdbl δ hδ hδ1).1
  -- the Rademacher complexity of the loss class, via contraction and Lemma 26.10
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hm'
  have hRpt : ∀ S : Fin m → E × Y,
      rademacher (evalSet (lossClass loss H) S) ≤ ρ * B * R / Real.sqrt m := by
    intro S
    set px : Fin m → E := fun i ↦ proj (S i).1
    have hset : evalSet (lossClass loss H) S =
        (fun a i ↦ (fun i a ↦ φ a (S i).2) i (a i)) '' linearEvalSet B px := by
      ext v
      constructor
      · rintro ⟨f, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨fun i ↦ ⟪w, px i⟫_ℝ, ⟨w, hw, rfl⟩, rfl⟩
      · rintro ⟨a, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨loss w, ⟨w, hw, rfl⟩, rfl⟩
    have hAne : (linearEvalSet B px).Nonempty := ⟨fun i ↦ ⟪(0 : E), px i⟫_ℝ, 0, by simpa using hB, rfl⟩
    have hAb : Bornology.IsBounded (linearEvalSet B px) := by
      refine isBounded_iff_forall_norm_le.2 ⟨B * R, ?_⟩
      rintro _ ⟨w, hw, rfl⟩
      refine (pi_norm_le_iff_of_nonneg (mul_nonneg hB hR0)).2 (fun i ↦ ?_)
      rw [Real.norm_eq_abs]
      exact hinner w hw _
    have h1 := contraction_lemma (linearEvalSet B px) hAne hAb ρ (fun i a ↦ φ a (S i).2)
      (fun i ↦ hφ _)
    have h2 := rademacher_linearEvalSet_le B hB px
    have hmax : (⨆ i, ‖px i‖) ≤ R := by
      have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      exact ciSup_le (fun i ↦ hproj_norm _)
    rw [hset]
    calc _ ≤ ρ * rademacher (linearEvalSet B px) := h1
      _ ≤ ρ * (B * (⨆ i, ‖px i‖) / Real.sqrt m) := mul_le_mul_of_nonneg_left h2 hρ0
      _ ≤ ρ * (B * R / Real.sqrt m) := by gcongr
      _ = ρ * B * R / Real.sqrt m := by ring
  have hμP : IsProbabilityMeasure (iidLaw D m) := by unfold iidLaw; infer_instance
  have hER : ∫ S', rademacher (evalSet (lossClass loss H) S') ∂(iidLaw D m) ≤
      ρ * B * R / Real.sqrt m := by
    by_cases hi : Integrable (fun S' ↦ rademacher (evalSet (lossClass loss H) S')) (iidLaw D m)
    · calc _ ≤ ∫ _S', ρ * B * R / Real.sqrt m ∂(iidLaw D m) :=
            integral_mono hi (integrable_const _) hRpt
        _ = ρ * B * R / Real.sqrt m := by rw [integral_const, probReal_univ, one_smul]
    · rw [integral_undef hi]; positivity
  -- the sample almost surely lies in the ball of radius `R`
  set N : Set (Fin m → E × Y) := {S | ∃ i, R < ‖(S i).1‖} with hN
  have hA : MeasurableSet {p : E × Y | R < ‖p.1‖} :=
    measurableSet_lt measurable_const (measurable_norm.comp measurable_fst)
  have hN0 : iidLaw D m N = 0 := by
    have : N = ⋃ i, (fun S : Fin m → E × Y ↦ S i) ⁻¹' {p | R < ‖p.1‖} := by
      ext S; simp [hN]
    rw [this]
    refine measure_iUnion_null (fun i ↦ ?_)
    have hp := measurePreserving_eval (fun _ : Fin m ↦ D) i
    unfold iidLaw
    rw [show (fun S : Fin m → E × Y ↦ S i) = Function.eval i from rfl,
      hp.measure_preimage hA.nullMeasurableSet]
    exact hR
  have hae : ∀ᵐ p ∂D, ‖p.1‖ ≤ R := by
    rw [ae_iff]
    simpa [not_le] using hR
  -- conclusion
  refine le_trans (measure_mono (t := {S | ∃ h ∈ H,
      2 * (∫ S', rademacher (evalSet (lossClass loss H) S') ∂(iidLaw D m)) +
        c * Real.sqrt (2 * Real.log (2 / δ) / m) < risk loss D h - empRisk loss S h} ∪ N)
    (fun S hS ↦ ?_)) ?_
  · by_cases hSN : S ∈ N
    · exact Or.inr hSN
    left
    obtain ⟨w, hw, hlt⟩ := hS
    have hSb : ∀ i, ‖(S i).1‖ ≤ R := by
      intro i; by_contra h; exact hSN ⟨i, not_le.1 h⟩
    have he : empRisk (fun w p ↦ φ ⟪w, p.1⟫_ℝ p.2) S w = empRisk loss S w := by
      unfold empRisk
      congr 1
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      simp only [hloss, hproj_eq _ (hSb i)]
    have hr : risk (fun w p ↦ φ ⟪w, p.1⟫_ℝ p.2) D w = risk loss D w := by
      unfold risk
      refine integral_congr_ae (hae.mono (fun p hp ↦ ?_))
      simp only [hloss, hproj_eq _ hp]
    refine ⟨w, hw, ?_⟩
    rw [he, hr] at hlt
    have : 2 * ∫ S', rademacher (evalSet (lossClass loss H) S') ∂(iidLaw D m) ≤
        2 * ρ * B * R / Real.sqrt m := by
      have := mul_le_mul_of_nonneg_left hER (by norm_num : (0 : ℝ) ≤ 2)
      calc _ ≤ 2 * (ρ * B * R / Real.sqrt m) := this
        _ = 2 * ρ * B * R / Real.sqrt m := by ring
    linarith
  · refine (measure_union_le _ _).trans ?_
    rw [hN0, add_zero]
    exact h265
