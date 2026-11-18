-- Prove2me | solution 1 for PrivateAgnosticHalfspace.Gaussian.lemma_B_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T21:45:06.213241+00:00
-- url     : https://prove2.me/submissions/f27cb13e-6da4-4325-ba42-29981a916e93

import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression
import Theorems.Thm_UnderstandingML_contraction_lemma
open MeasureTheory UnderstandingML
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PrivateAgnosticHalfspace.Symmetrization

variable {Z Hyp : Type*} [MeasurableSpace Z]

/-- Swap the coordinates of two samples where `σ` is `false`. -/
def swapS {m : ℕ} (σ : Fin m → Bool) (p : (Fin m → Z) × (Fin m → Z)) :
    (Fin m → Z) × (Fin m → Z) :=
  (fun i ↦ if σ i then p.1 i else p.2 i, fun i ↦ if σ i then p.2 i else p.1 i)

lemma measurePreserving_swapS {m : ℕ} (D : Measure Z) [IsProbabilityMeasure D]
    (σ : Fin m → Bool) :
    MeasurePreserving (swapS σ) ((iidLaw D m).prod (iidLaw D m))
      ((iidLaw D m).prod (iidLaw D m)) := by
  unfold iidLaw
  have e := measurePreserving_arrowProdEquivProdArrow Z Z (Fin m) (fun _ ↦ D) (fun _ ↦ D)
  have P : MeasurePreserving
      (fun (a : Fin m → Z × Z) i ↦ (if σ i then id else Prod.swap) (a i))
      (Measure.pi fun _ ↦ D.prod D) (Measure.pi fun _ ↦ D.prod D) := by
    refine measurePreserving_pi _ _ (fun i ↦ ?_)
    by_cases h : σ i
    · simp only [h, if_true]; exact MeasurePreserving.id _
    · simp only [h]; exact Measure.measurePreserving_swap
  have := e.comp (P.comp (MeasurePreserving.symm _ e))
  convert this using 1
  funext p
  ext i <;> by_cases h : σ i <;> simp [swapS, h, MeasurableEquiv.arrowProdEquivProdArrow,
    Equiv.arrowProdEquivProdArrow]

/-- The average of one coordinate under `D^m`. -/
lemma integral_eval {m : ℕ} (D : Measure Z) [IsProbabilityMeasure D] (f : Z → ℝ)
    (hf : Measurable f) (i : Fin m) :
    ∫ S, f (S i) ∂(iidLaw D m) = ∫ z, f z ∂D := by
  have h := measurePreserving_eval (fun _ : Fin m ↦ D) i
  unfold iidLaw
  calc ∫ S, f (S i) ∂(Measure.pi fun _ : Fin m ↦ D)
      = ∫ z, f z ∂((Measure.pi fun _ : Fin m ↦ D).map (Function.eval i)) :=
        (integral_map h.measurable.aemeasurable (by rw [h.map_eq]; exact hf.aestronglyMeasurable)).symm
    _ = ∫ z, f z ∂D := by rw [h.map_eq]

lemma abs_signVec {m : ℕ} (σ : Fin m → Bool) (i : Fin m) : |signVec σ i| = 1 := by
  unfold signVec; cases σ i <;> simp

lemma signVec_not {m : ℕ} (σ : Fin m → Bool) (i : Fin m) :
    signVec (fun j ↦ !σ j) i = - signVec σ i := by
  unfold signVec; cases h : σ i <;> simp [h]

lemma sum_not {m : ℕ} (F : (Fin m → Bool) → ℝ) :
    ∑ σ : Fin m → Bool, F σ = ∑ σ : Fin m → Bool, F (fun j ↦ !σ j) :=
  (Fintype.sum_equiv (Equiv.piCongrRight fun (_ : Fin m) ↦ Equiv.boolNot) _ _
    (fun _ ↦ rfl)).symm

lemma abs_iSup_le {ι : Type*} [Nonempty ι] (f : ι → ℝ) (C : ℝ) (hf : ∀ i, |f i| ≤ C) :
    |⨆ i, f i| ≤ C := by
  have hb : BddAbove (Set.range f) := ⟨C, by rintro _ ⟨i, rfl⟩; exact (le_abs_self _).trans (hf i)⟩
  rw [abs_le]
  constructor
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact (neg_le_of_abs_le (hf i)).trans (le_ciSup hb i)
  · exact ciSup_le (fun i ↦ (le_abs_self _).trans (hf i))

lemma bddAbove_of_abs {ι : Type*} (f : ι → ℝ) (C : ℝ) (hf : ∀ i, |f i| ≤ C) :
    BddAbove (Set.range f) :=
  ⟨C, by rintro _ ⟨i, rfl⟩; exact (le_abs_self _).trans (hf i)⟩

variable (loss : Hyp → Z → ℝ)

lemma measurable_empRisk {m : ℕ} (h : Hyp) (hmeas : Measurable (loss h)) :
    Measurable (fun S : Fin m → Z ↦ empRisk loss S h) := by
  unfold empRisk
  refine Measurable.div_const ?_ _
  exact Finset.measurable_sum _ (fun i _ ↦ hmeas.comp (measurable_pi_apply i))


end PrivateAgnosticHalfspace.Symmetrization
namespace PrivateAgnosticHalfspace.Symmetrization
variable {Z Hyp : Type*} [MeasurableSpace Z]
noncomputable def empEnvelope {m : ℕ} (B : Z → ℝ) (S : Fin m → Z) : ℝ := (∑ i, B (S i)) / m

lemma empEnvelope_nonneg {m : ℕ} (B : Z → ℝ) (hB : ∀ z, 0 ≤ B z) (S : Fin m → Z) :
    0 ≤ empEnvelope B S := by
  unfold empEnvelope
  exact div_nonneg (Finset.sum_nonneg (fun i _ => hB _)) (Nat.cast_nonneg _)

lemma integrable_empRisk {m : ℕ} (loss : Hyp → Z → ℝ) (D : Measure Z) [IsProbabilityMeasure D]
    (h : Hyp) (hint : Integrable (loss h) D) :
    Integrable (fun S : Fin m → Z => empRisk loss S h) (iidLaw D m) := by
  unfold empRisk iidLaw
  apply Integrable.div_const
  apply integrable_finsetSum
  intro i _
  exact (measurePreserving_eval (fun _ : Fin m => D) i).integrable_comp_of_integrable hint

lemma integrable_empEnvelope {m : ℕ} (B : Z → ℝ) (D : Measure Z) [IsProbabilityMeasure D]
    (hint : Integrable B D) : Integrable (empEnvelope B (m := m)) (iidLaw D m) :=
  integrable_empRisk (fun _ : Unit => B) D () hint

lemma integral_empRisk {m : ℕ} (hm : 0 < m) (loss : Hyp → Z → ℝ)
    (D : Measure Z) [IsProbabilityMeasure D] (h : Hyp)
    (hmeas : Measurable (loss h)) (hint : Integrable (loss h) D) :
    (∫ S, empRisk loss S h ∂iidLaw D m) = risk loss D h := by
  unfold empRisk
  rw [integral_div, integral_finsetSum]
  · simp only [integral_eval D _ hmeas, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    unfold risk
    field_simp
  · intro i _
    exact (measurePreserving_eval (fun _ : Fin m => D) i).integrable_comp_of_integrable hint

lemma abs_signed_sum_le {m : ℕ} (σ : Fin m → Bool) (x b : Fin m → ℝ)
    (hx : ∀ i, |x i| ≤ b i) : |∑ i, signVec σ i * x i| ≤ ∑ i, b i := by
  calc
    _ ≤ ∑ i, |signVec σ i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |x i| := by simp only [abs_mul, abs_signVec, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hx i)

lemma abs_empRisk_le {m : ℕ} (hm : 0 < m) (loss : Hyp → Z → ℝ) (B : Z → ℝ)
    (h : Hyp) (hc : ∀ z, |loss h z| ≤ B z) (S : Fin m → Z) :
    |empRisk loss S h| ≤ empEnvelope B S := by
  unfold empRisk empEnvelope
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [abs_div, abs_of_pos hm']
  apply div_le_div_of_nonneg_right _ hm'.le
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hc _))

lemma abs_risk_le (loss : Hyp → Z → ℝ) (B : Z → ℝ) (D : Measure Z) [IsProbabilityMeasure D]
    (h : Hyp) (hc : ∀ z, |loss h z| ≤ B z) (hint : Integrable B D) (hmeas : Measurable (loss h)) :
    |risk loss D h| ≤ ∫ z, B z ∂D := by
  have hfi : Integrable (loss h) D := hint.mono' hmeas.aestronglyMeasurable (ae_of_all _ hc)
  calc
    _ ≤ ∫ z, |loss h z| ∂D := by simpa only [risk, Real.norm_eq_abs] using norm_integral_le_integral_norm (loss h)
    _ ≤ _ := integral_mono hfi.abs hint hc

lemma iSup_evalSet {m : ℕ} (loss : Hyp → Z → ℝ) (H : Set Hyp) (hH : H.Nonempty)
    (B : Z → ℝ) (hc : ∀ h ∈ H, ∀ z, |loss h z| ≤ B z)
    (S : Fin m → Z) (σ : Fin m → Bool) :
    (⨆ a : evalSet (lossClass loss H) S, ∑ i, signVec σ i * (a : Fin m → ℝ) i) =
      ⨆ h : H, ∑ i, signVec σ i * loss h (S i) := by
  have : Nonempty H := hH.to_subtype
  obtain ⟨h0,hh0⟩ := hH
  have hne : Nonempty (evalSet (lossClass loss H) S) :=
    ⟨⟨fun i => loss h0 (S i), loss h0, ⟨h0,hh0,rfl⟩, rfl⟩⟩
  have hb1 : BddAbove (Set.range fun h : H => ∑ i, signVec σ i * loss h (S i)) :=
    bddAbove_of_abs _ (∑ i, B (S i)) (fun h => abs_signed_sum_le σ _ _ (fun i => hc h h.2 _))
  have hb2 : BddAbove (Set.range fun a : evalSet (lossClass loss H) S =>
      ∑ i, signVec σ i * (a : Fin m → ℝ) i) := by
    apply bddAbove_of_abs _ (∑ i, B (S i))
    rintro ⟨v,f,⟨h,hh,rfl⟩,rfl⟩
    exact abs_signed_sum_le σ _ _ (fun i => hc h hh _)
  refine le_antisymm (ciSup_le fun a => ?_) (ciSup_le fun h => ?_)
  · obtain ⟨v,f,⟨h,hh,rfl⟩,rfl⟩ := a
    exact le_ciSup hb1 ⟨h,hh⟩
  · exact le_ciSup hb2 ⟨fun i => loss h (S i),loss h,⟨h,h.2,rfl⟩,rfl⟩
end PrivateAgnosticHalfspace.Symmetrization
namespace PrivateAgnosticHalfspace.Symmetrization
variable {Z Hyp : Type*} [MeasurableSpace Z]

theorem representativeness_le_rademacher_envelope
    (loss : Hyp → Z → ℝ) (H : Set Hyp) (hH : H.Nonempty)
    (D : Measure Z) [IsProbabilityMeasure D] (B : Z → ℝ)
    (hB0 : ∀ z, 0 ≤ B z) (hBm : Measurable B) (hBiD : Integrable B D)
    (hc : ∀ h ∈ H, ∀ z, |loss h z| ≤ B z) (hmeas : ∀ h ∈ H, Measurable (loss h))
    (m : ℕ) (hm : 0 < m)
    (hrep : Measurable (fun S : Fin m → Z => representativeness loss H D S))
    (hrad : Measurable (fun S : Fin m → Z => rademacher (evalSet (lossClass loss H) S)))
    (hdbl : Measurable (fun p : (Fin m → Z) × (Fin m → Z) =>
      ⨆ h : H, (empRisk loss p.2 (h : Hyp) - empRisk loss p.1 (h : Hyp)))) :
    (∫ S, representativeness loss H D S ∂iidLaw D m) ≤
      2 * ∫ S, rademacher (evalSet (lossClass loss H) S) ∂iidLaw D m := by
  classical
  let μ := iidLaw D m
  haveI : IsProbabilityMeasure μ := by unfold μ iidLaw; infer_instance
  have hNe : Nonempty H := hH.to_subtype
  obtain ⟨h0,hh0⟩ := hH
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  let F : (Fin m → Z) → ℝ := fun S => representativeness loss H D S
  let G : (Fin m → Z) × (Fin m → Z) → ℝ :=
    fun p => ⨆ h : H, (empRisk loss p.2 (h : Hyp) - empRisk loss p.1 (h : Hyp))
  let Rad : (Fin m → Z) → ℝ := fun S => rademacher (evalSet (lossClass loss H) S)
  have hBi : Integrable (empEnvelope B (m := m)) μ := integrable_empEnvelope B D hBiD
  have hLi (h : H) : Integrable (loss h) D := by
    apply hBiD.mono' (hmeas h h.2).aestronglyMeasurable
    exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hc h h.2 z)
  have hdiff (h : H) (S S' : Fin m → Z) :
      |empRisk loss S' (h : Hyp) - empRisk loss S (h : Hyp)| ≤ empEnvelope B S + empEnvelope B S' := by
    have h1 := abs_empRisk_le hm loss B h (hc h h.2) S
    have h2 := abs_empRisk_le hm loss B h (hc h h.2) S'
    exact (abs_sub _ _).trans (by linarith)
  have hFb (S : Fin m → Z) : |F S| ≤ (∫ z, B z ∂D) + empEnvelope B S := by
    apply abs_iSup_le
    intro h
    have h1 := abs_empRisk_le hm loss B h (hc h h.2) S
    have h2 := abs_risk_le loss B D h (hc h h.2) hBiD (hmeas h h.2)
    exact (abs_sub _ _).trans (by linarith)
  have hGb (p : (Fin m → Z) × (Fin m → Z)) : |G p| ≤ empEnvelope B p.1 + empEnvelope B p.2 :=
    abs_iSup_le _ _ (fun h => hdiff h p.1 p.2)
  have hRadb (S : Fin m → Z) : |Rad S| ≤ empEnvelope B S := by
    simp only [Rad,rademacher]
    have hinner (σ : Fin m → Bool) :
        |⨆ a : evalSet (lossClass loss H) S, ∑ i, signVec σ i * (a : Fin m → ℝ) i| ≤ ∑ i, B (S i) := by
      rw [iSup_evalSet loss H ⟨h0,hh0⟩ B hc]
      exact abs_iSup_le _ _ (fun h => abs_signed_sum_le σ _ _ (fun i => hc h h.2 _))
    have hsum := Finset.abs_sum_le_sum_abs
      (fun σ : Fin m → Bool => ⨆ a : evalSet (lossClass loss H) S,
        ∑ i, signVec σ i * (a : Fin m → ℝ) i) Finset.univ
    have hsum2 : (∑ σ : Fin m → Bool, |⨆ a : evalSet (lossClass loss H) S,
        ∑ i, signVec σ i * (a : Fin m → ℝ) i|) ≤ 2 ^ m * ∑ i, B (S i) := by
      calc
        _ ≤ ∑ _σ : Fin m → Bool, ∑ i, B (S i) := Finset.sum_le_sum (fun σ _ => hinner σ)
        _ = _ := by simp [Finset.card_univ,Fintype.card_bool,Fintype.card_fin]
    rw [abs_mul,abs_mul,abs_of_pos (by positivity : (0 : ℝ) < 1 / m),
      abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ m)]
    calc
      _ ≤ 1 / (m : ℝ) * (1 / 2 ^ m * (2 ^ m * ∑ i, B (S i))) := by
        gcongr
        exact hsum.trans hsum2
      _ = empEnvelope B S := by unfold empEnvelope; field_simp
  have hFi : Integrable F μ := by
    apply ((integrable_const (∫ z, B z ∂D)).add hBi).mono' hrep.aestronglyMeasurable
    exact ae_of_all _ (fun S => by simpa only [Real.norm_eq_abs, Pi.add_apply, F] using hFb S)
  have hGi : Integrable G (μ.prod μ) := by
    apply ((hBi.comp_fst μ).add (hBi.comp_snd μ)).mono' hdbl.aestronglyMeasurable
    exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs, Pi.add_apply, G] using hGb p)
  have hRadi : Integrable Rad μ := by
    apply hBi.mono' hrad.aestronglyMeasurable
    exact ae_of_all _ (fun S => by simpa only [Real.norm_eq_abs] using hRadb S)
  have hA (S : Fin m → Z) : F S ≤ ∫ S', G (S,S') ∂μ := by
    have hsec : Integrable (fun S' => G (S,S')) μ := by
      apply ((integrable_const (empEnvelope B S)).add hBi).mono'
        (hdbl.comp measurable_prodMk_left).aestronglyMeasurable
      exact ae_of_all _ (fun S' => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_def, G] using hGb (S,S'))
    apply ciSup_le
    intro h
    have hEi : Integrable (fun S' : Fin m → Z => empRisk loss S' (h : Hyp)) μ :=
      integrable_empRisk loss D h (hLi h)
    have he : risk loss D (h : Hyp) - empRisk loss S (h : Hyp) =
        ∫ S', (empRisk loss S' (h : Hyp) - empRisk loss S (h : Hyp)) ∂μ := by
      rw [integral_sub hEi (integrable_const _), integral_const, probReal_univ,one_smul,
        integral_empRisk hm loss D h (hmeas h h.2) (hLi h)]
    rw [he]
    apply integral_mono (hEi.sub (integrable_const _)) hsec
    intro S'
    exact le_ciSup (f := fun h : H => empRisk loss S' (h : Hyp) - empRisk loss S (h : Hyp))
      (bddAbove_of_abs _ _ (fun h => hdiff h S S')) h
  have hB : (∫ S, F S ∂μ) ≤ ∫ p, G p ∂μ.prod μ := by
    rw [integral_prod _ hGi]
    exact integral_mono hFi hGi.integral_prod_left hA
  have hC (σ : Fin m → Bool) :
      (∫ p, G (swapS σ p) ∂μ.prod μ) = ∫ p, G p ∂μ.prod μ := by
    have hp := measurePreserving_swapS D σ
    rw [← integral_map hp.measurable.aemeasurable (by rw [hp.map_eq]; exact hGi.1),hp.map_eq]
  have hD (p : (Fin m → Z) × (Fin m → Z)) :
      (∑ σ : Fin m → Bool, G (swapS σ p)) ≤ 2 ^ m * (Rad p.1 + Rad p.2) := by
    rcases p with ⟨S,S'⟩
    let a : (Fin m → Bool) → H → ℝ := fun σ h => ∑ i, signVec σ i * loss h (S' i)
    let b : (Fin m → Bool) → H → ℝ := fun σ h => ∑ i, signVec σ i * loss h (S i)
    have hab (σ : Fin m → Bool) (h : H) :
        empRisk loss (swapS σ (S,S')).2 (h : Hyp) - empRisk loss (swapS σ (S,S')).1 (h : Hyp) =
          (1 / m) * (a σ h + b (fun j => !σ j) h) := by
      simp only [a,b,empRisk,swapS,signVec_not]
      rw [div_sub_div_same,← Finset.sum_sub_distrib,← Finset.sum_add_distrib,one_div_mul_eq_div]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      unfold signVec
      cases σ i <;> simp <;> ring
    have hba (σ : Fin m → Bool) : BddAbove (Set.range (a σ)) :=
      bddAbove_of_abs _ (∑ i, B (S' i)) (fun h => abs_signed_sum_le σ _ _ (fun i => hc h h.2 _))
    have hbb (σ : Fin m → Bool) : BddAbove (Set.range (b σ)) :=
      bddAbove_of_abs _ (∑ i, B (S i)) (fun h => abs_signed_sum_le σ _ _ (fun i => hc h h.2 _))
    have hGσ (σ : Fin m → Bool) : G (swapS σ (S,S')) ≤
        (1 / m) * ((⨆ h, a σ h) + ⨆ h, b (fun j => !σ j) h) := by
      apply ciSup_le
      intro h
      rw [hab]
      gcongr
      · exact le_ciSup (hba σ) h
      · exact le_ciSup (hbb _) h
    have hRadS (T : Fin m → Z) : Rad T = (1 / m) * ((1 / 2 ^ m) *
        ∑ σ : Fin m → Bool, ⨆ h : H, ∑ i, signVec σ i * loss h (T i)) := by
      simp only [Rad,rademacher]
      congr 2
      exact Finset.sum_congr rfl (fun σ _ => iSup_evalSet loss H ⟨h0,hh0⟩ B hc T σ)
    calc
      _ ≤ ∑ σ : Fin m → Bool, (1 / m) * ((⨆ h, a σ h) + ⨆ h, b (fun j => !σ j) h) :=
        Finset.sum_le_sum (fun σ _ => hGσ σ)
      _ = (1 / m) * (∑ σ : Fin m → Bool, (⨆ h, a σ h) + ∑ σ : Fin m → Bool, ⨆ h, b σ h) := by
        rw [← Finset.mul_sum,Finset.sum_add_distrib,← sum_not (fun σ => ⨆ h, b σ h)]
      _ = 2 ^ m * (Rad (S,S').1 + Rad (S,S').2) := by
        rw [hRadS,hRadS]
        simp only [a,b]
        field_simp
        ring
  have hGσi (σ : Fin m → Bool) : Integrable (fun p => G (swapS σ p)) (μ.prod μ) :=
    (measurePreserving_swapS D σ).integrable_comp_of_integrable hGi
  have hE : 2 ^ m * (∫ p, G p ∂μ.prod μ) ≤ 2 ^ m * (2 * ∫ S, Rad S ∂μ) := by
    have he1 : 2 ^ m * (∫ p, G p ∂μ.prod μ) = ∫ p, ∑ σ : Fin m → Bool, G (swapS σ p) ∂μ.prod μ := by
      rw [integral_finsetSum _ (fun σ _ => hGσi σ)]
      simp only [hC,Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,
        Fintype.card_fin,nsmul_eq_mul]
      norm_num
    have he2 : (∫ p, 2 ^ m * (Rad p.1 + Rad p.2) ∂μ.prod μ) = 2 ^ m * (2 * ∫ S, Rad S ∂μ) := by
      rw [integral_const_mul,integral_add (hRadi.comp_fst μ) (hRadi.comp_snd μ),
        integral_fun_fst,integral_fun_snd,probReal_univ,one_smul]
      ring
    rw [he1,← he2]
    exact integral_mono (integrable_finsetSum _ (fun σ _ => hGσi σ))
      (((hRadi.comp_fst μ).add (hRadi.comp_snd μ)).const_mul _) hD
  have hE' := le_of_mul_le_mul_left hE (by positivity : (0 : ℝ) < 2 ^ m)
  exact hB.trans hE'
end PrivateAgnosticHalfspace.Symmetrization

namespace PrivateAgnosticHalfspace.Symmetrization
lemma measurable_ciSup_continuous {ι A : Type*} [TopologicalSpace ι] [TopologicalSpace.SeparableSpace ι]
    [MeasurableSpace A] (f : ι → A → ℝ) (hm : ∀ i, Measurable (f i))
    (hc : ∀ a, Continuous (fun i => f i a)) : Measurable (fun a => ⨆ i, f i a) := by
  obtain ⟨J,hJ,hJd⟩ := TopologicalSpace.exists_countable_dense ι
  haveI := hJ.to_subtype
  have he (a : A) : (⨆ j : J, f j a) = ⨆ i, f i a := hJd.ciSup' (hc a)
  simp_rw [← he]
  exact Measurable.iSup (fun j => hm j)
end PrivateAgnosticHalfspace.Symmetrization
open MeasureTheory UnderstandingML
open scoped BigOperators InnerProductSpace
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Symmetrization
theorem svm_eps_flip (b : Bool) :
    (if (!b) then (1 : ℝ) else -1) = -(if b then (1 : ℝ) else -1) := by
  cases b <;> norm_num

theorem svm_eps_sum {m : ℕ} (i j : Fin m) :
    ∑ σ : Fin m → Bool, (if σ i then (1 : ℝ) else -1) * (if σ j then (1 : ℝ) else -1) =
      if i = j then (2 : ℝ) ^ m else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have h1 : ∀ σ : Fin m → Bool,
        (if σ i then (1 : ℝ) else -1) * (if σ i then (1 : ℝ) else -1) = 1 := by
      intro σ
      cases σ i <;> norm_num
    simp_rw [h1]
    simp [Finset.card_univ]
  · rw [if_neg hij]
    let f : (Fin m → Bool) → (Fin m → Bool) := fun σ => Function.update σ i (!(σ i))
    have hf : Function.Involutive f := by
      intro σ
      funext k
      by_cases hk : k = i
      · subst hk
        simp [f]
      · simp [f, hk]
    have hsum := Equiv.sum_comp (Function.Involutive.toPerm f hf) (fun σ : Fin m → Bool =>
      (if σ i then (1 : ℝ) else -1) * (if σ j then (1 : ℝ) else -1))
    have hneg : ∀ σ : Fin m → Bool,
        (if (Function.Involutive.toPerm f hf σ) i then (1 : ℝ) else -1) *
          (if (Function.Involutive.toPerm f hf σ) j then (1 : ℝ) else -1) =
          -((if σ i then (1 : ℝ) else -1) * (if σ j then (1 : ℝ) else -1)) := by
      intro σ
      have hei : (Function.Involutive.toPerm f hf σ) i = !(σ i) := by
        simp [f]
      have hej : (Function.Involutive.toPerm f hf σ) j = σ j := by
        simp [f, Ne.symm hij]
      rw [hei, hej, svm_eps_flip]
      ring
    simp_rw [hneg, Finset.sum_neg_distrib] at hsum
    linarith

theorem svm_norm_sq_sum {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {m : ℕ} (S : Fin m → X) :
    ∑ σ : Fin m → Bool, ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖ ^ 2 =
      (2 : ℝ) ^ m * ∑ i, ‖S i‖ ^ 2 := by
  have hexp : ∀ σ : Fin m → Bool, ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖ ^ 2 =
      ∑ i, ∑ j, ((if σ i then (1 : ℝ) else -1) * (if σ j then (1 : ℝ) else -1)) *
        inner ℝ (S i) (S j) := by
    intro σ
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [inner_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, svm_eps_sum]
  simp [real_inner_self_eq_norm_sq]


end PrivateAgnosticHalfspace.Symmetrization
namespace PrivateAgnosticHalfspace.Symmetrization
lemma rademacher_linear_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (hm : 0 < m) (x : Fin m → E) (R : ℝ) (hR : 0 ≤ R) :
    rademacher (linearEvalSet R x) ≤ R / m * Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
  classical
  haveI : Nonempty (linearEvalSet R x) := ⟨⟨0,0,by simpa using hR,by ext; simp⟩⟩
  have hs (σ : Fin m → Bool) :
      (⨆ a : linearEvalSet R x, ∑ i, signVec σ i * a.val i) ≤
        R * ‖∑ i, signVec σ i • x i‖ := by
    apply ciSup_le
    rintro ⟨a,w,hw,rfl⟩
    have he : (∑ i, signVec σ i * inner ℝ w (x i)) = inner ℝ w (∑ i, signVec σ i • x i) := by
      simp [inner_sum,real_inner_smul_right]
    rw [he]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hw (norm_nonneg _))
  have hN : (0 : ℝ) < 2 ^ m := by positivity
  have hsum := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m → Bool)))
    (f := fun σ => ‖∑ i, signVec σ i • x i‖)
  have hsq : (∑ σ : Fin m → Bool, ‖∑ i, signVec σ i • x i‖) ^ 2 ≤
      (2 : ℝ) ^ m * ((2 : ℝ) ^ m * ∑ i, ‖x i‖ ^ 2) := by
    simpa only [signVec,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,
      Nat.cast_pow,Nat.cast_ofNat,svm_norm_sq_sum] using hsum
  have hmean : (1 / (2 : ℝ) ^ m * ∑ σ : Fin m → Bool, ‖∑ i, signVec σ i • x i‖) ≤
      Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
    apply (le_abs_self _).trans
    apply Real.abs_le_sqrt
    calc
      _ = (∑ σ : Fin m → Bool, ‖∑ i, signVec σ i • x i‖) ^ 2 / ((2 : ℝ) ^ m) ^ 2 := by ring
      _ ≤ ((2 : ℝ) ^ m * ((2 : ℝ) ^ m * ∑ i, ‖x i‖ ^ 2)) / ((2 : ℝ) ^ m) ^ 2 :=
        div_le_div_of_nonneg_right hsq (sq_nonneg _)
      _ = _ := by field_simp
  unfold rademacher
  calc
    _ ≤ (1 / m : ℝ) * (1 / 2 ^ m * ∑ σ : Fin m → Bool, R * ‖∑ i, signVec σ i • x i‖) := by
      gcongr
      exact hs _
    _ = R / m * (1 / 2 ^ m * ∑ σ : Fin m → Bool, ‖∑ i, signVec σ i • x i‖) := by
      rw [← Finset.mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmean (div_nonneg hR (Nat.cast_nonneg _))
end PrivateAgnosticHalfspace.Symmetrization
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Symmetrization
lemma integrable_sqrt {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (Q : Z → ℝ) (hm : Measurable Q) (h0 : ∀ z, 0 ≤ Q z) (hi : Integrable Q μ) :
    Integrable (fun z => Real.sqrt (Q z)) μ := by
  apply (hi.add (integrable_const 1)).mono' hm.sqrt.aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    simp only [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Pi.add_apply]
    have hs := Real.sq_sqrt (h0 z)
    have hn := Real.sqrt_nonneg (Q z)
    nlinarith [sq_nonneg (Real.sqrt (Q z)-1)])
lemma expected_sqrt_le {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (Q : Z → ℝ) (hm : Measurable Q) (h0 : ∀ z, 0 ≤ Q z) (hi : Integrable Q μ) :
    (∫ z, Real.sqrt (Q z) ∂μ) ≤ Real.sqrt (∫ z, Q z ∂μ) := by
  have he : (fun z => (Real.sqrt (Q z)) ^ 2) = Q := funext (fun z => Real.sq_sqrt (h0 z))
  have hsq : Integrable ((fun x : ℝ => x ^ 2) ∘ (fun z => Real.sqrt (Q z))) μ := by
    change Integrable (fun z => (Real.sqrt (Q z)) ^ 2) μ
    rw [he]
    exact hi
  have h := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le (continuous_pow 2).continuousOn
    isClosed_Ici (ae_of_all μ (fun z => Real.sqrt_nonneg (Q z)))
    (integrable_sqrt μ Q hm h0 hi) hsq
  rw [he] at h
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)
end PrivateAgnosticHalfspace.Symmetrization
open MeasureTheory UnderstandingML
open scoped BigOperators ENNReal InnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PrivateAgnosticHalfspace.Gaussian
variable {X : Type*} [MeasurableSpace X]

noncomputable def centeredLoss (D : ℕ) (φ : X → Vec D) (v : Vec D) (z : X × Bool) : ℝ :=
  |inner ℝ v (φ z.1) - label z.2| - 1

lemma abs_label (b : Bool) : |label b| = 1 := by cases b <;> norm_num [label]

lemma centeredLoss_bound (D : ℕ) (φ : X → Vec D) (v : Vec D) (z : X × Bool) :
    |centeredLoss D φ v z| ≤ ‖v‖ * ‖φ z.1‖ := by
  have h := abs_abs_sub_abs_le_abs_sub (inner ℝ v (φ z.1) - label z.2) (-label z.2)
  simp only [abs_neg,abs_label,sub_neg_eq_add,sub_add_cancel] at h
  exact h.trans (abs_real_inner_le_norm _ _)

lemma centeredLoss_lipschitz (D : ℕ) (φ : X → Vec D) (v w : Vec D) (z : X × Bool) :
    |centeredLoss D φ v z - centeredLoss D φ w z| ≤ ‖v-w‖ * ‖φ z.1‖ := by
  have h := abs_abs_sub_abs_le_abs_sub (inner ℝ v (φ z.1) - label z.2)
    (inner ℝ w (φ z.1) - label z.2)
  simp only [sub_sub_sub_cancel_right, ← inner_sub_left] at h
  simpa only [centeredLoss,sub_sub_sub_cancel_right] using h.trans (abs_real_inner_le_norm _ _)

lemma measurable_centeredLoss (D : ℕ) (φ : X → Vec D) (hφ : Measurable φ) (v : Vec D) :
    Measurable (centeredLoss D φ v) := by
  exact (((measurable_const.inner (hφ.comp measurable_fst)).sub
    ((show Measurable label from measurable_of_countable _).comp measurable_snd)).abs).sub_const 1

lemma continuous_centeredLoss (D : ℕ) (φ : X → Vec D) (z : X × Bool) :
    Continuous (fun v => centeredLoss D φ v z) := by
  exact ((continuous_id.inner continuous_const).sub continuous_const).abs.sub continuous_const

lemma integrable_feature_norm (D : ℕ) (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (φ : X → Vec D) (hφ : Measurable φ)
    (hf : Integrable (fun z : X × Bool => ‖φ z.1‖ ^ 2) P) :
    Integrable (fun z : X × Bool => ‖φ z.1‖) P := by
  apply (hf.add (integrable_const 1)).mono' (hφ.comp measurable_fst).norm.aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Pi.add_apply, Function.comp_apply]
    nlinarith [sq_nonneg (‖φ z.1‖ - 1)])

lemma integrable_centeredLoss (D : ℕ) (P : Measure (X × Bool))
    (φ : X → Vec D) (hφ : Measurable φ) (hi : Integrable (fun z : X × Bool => ‖φ z.1‖) P)
    (v : Vec D) : Integrable (centeredLoss D φ v) P := by
  apply (hi.const_mul ‖v‖).mono' (measurable_centeredLoss D φ hφ v).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using centeredLoss_bound D φ v z)

lemma continuous_centeredRisk (D : ℕ) (P : Measure (X × Bool))
    (φ : X → Vec D) (hφ : Measurable φ) (hi : Integrable (fun z : X × Bool => ‖φ z.1‖) P) :
    Continuous (fun v => UnderstandingML.risk (centeredLoss D φ) P v) := by
  let B := ∫ z, ‖φ z.1‖ ∂P
  have hB : 0 ≤ B := integral_nonneg (fun _ => norm_nonneg _)
  apply (show LipschitzWith (Real.toNNReal B) (fun v => UnderstandingML.risk (centeredLoss D φ) P v) from ?_).continuous
  apply LipschitzWith.of_dist_le_mul
  intro v w
  have hiv := integrable_centeredLoss D P φ hφ hi v
  have hiw := integrable_centeredLoss D P φ hφ hi w
  simp only [Real.dist_eq, UnderstandingML.risk, Real.coe_toNNReal _ hB, dist_eq_norm]
  rw [← integral_sub hiv hiw]
  calc
    _ ≤ ∫ z, |centeredLoss D φ v z - centeredLoss D φ w z| ∂P :=
      by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => centeredLoss D φ v z - centeredLoss D φ w z)
    _ ≤ ∫ z, ‖v-w‖ * ‖φ z.1‖ ∂P :=
      integral_mono (hiv.sub hiw).abs (hi.const_mul _) (centeredLoss_lipschitz D φ v w)
    _ = B * ‖v-w‖ := by rw [integral_const_mul]; ring

end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
open PrivateAgnosticHalfspace.Symmetrization
variable {X : Type*} [MeasurableSpace X]

lemma centered_envelope (D : ℕ) (φ : X → Vec D) (R : ℝ) (v : Metric.closedBall (0 : Vec D) R)
    (z : X × Bool) : |centeredLoss D φ v z| ≤ R * ‖φ z.1‖ := by
  exact (centeredLoss_bound D φ v z).trans (mul_le_mul_of_nonneg_right
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using v.2) (norm_nonneg _))

lemma continuous_centeredEmp {n : ℕ} (D : ℕ) (φ : X → Vec D) (S : Fin n → X × Bool) :
    Continuous (fun v => empRisk (centeredLoss D φ) S v) := by
  unfold empRisk
  exact (continuous_finset_sum _ (fun _ _ => continuous_centeredLoss D φ _)).div_const _

lemma measurable_centered_rep {n : ℕ} (D : ℕ) (P : Measure (X × Bool))
    (φ : X → Vec D) (hφ : Measurable φ) (hi : Integrable (fun z : X × Bool => ‖φ z.1‖) P)
    (R : ℝ) :
    Measurable (fun S : Fin n → X × Bool => representativeness (centeredLoss D φ)
      (Metric.closedBall 0 R) P S) := by
  apply measurable_ciSup_continuous
  · intro v
    exact measurable_const.sub (measurable_empRisk (centeredLoss D φ) (v : Vec D) (measurable_centeredLoss D φ hφ v))
  · intro S
    exact ((continuous_centeredRisk D P φ hφ hi).sub (continuous_centeredEmp D φ S)).comp
      continuous_subtype_val

lemma measurable_centered_double {n : ℕ} (D : ℕ) (φ : X → Vec D) (hφ : Measurable φ) (R : ℝ) :
    Measurable (fun p : (Fin n → X × Bool) × (Fin n → X × Bool) =>
      ⨆ v : Metric.closedBall (0 : Vec D) R,
        empRisk (centeredLoss D φ) p.2 v - empRisk (centeredLoss D φ) p.1 v) := by
  apply measurable_ciSup_continuous
  · intro v
    exact ((measurable_empRisk (centeredLoss D φ) (v : Vec D) (measurable_centeredLoss D φ hφ v)).comp measurable_snd).sub
      ((measurable_empRisk (centeredLoss D φ) (v : Vec D) (measurable_centeredLoss D φ hφ v)).comp measurable_fst)
  · intro p
    exact ((continuous_centeredEmp D φ p.2).sub (continuous_centeredEmp D φ p.1)).comp continuous_subtype_val

lemma measurable_centered_rad {n : ℕ} (D : ℕ) (φ : X → Vec D) (hφ : Measurable φ)
    (R : ℝ) (hR : 0 ≤ R) :
    Measurable (fun S : Fin n → X × Bool =>
      rademacher (evalSet (lossClass (centeredLoss D φ) (Metric.closedBall 0 R)) S)) := by
  have hH : (Metric.closedBall (0 : Vec D) R).Nonempty := ⟨0,by simpa using hR⟩
  have hc : ∀ v ∈ Metric.closedBall (0 : Vec D) R, ∀ z,
      |centeredLoss D φ v z| ≤ R * ‖φ z.1‖ := fun v hv => centered_envelope D φ R ⟨v,hv⟩
  simp only [rademacher]
  simp_rw [iSup_evalSet (centeredLoss D φ) (Metric.closedBall 0 R) hH (fun z => R * ‖φ z.1‖) hc]
  apply Measurable.const_mul
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro σ _
  apply measurable_ciSup_continuous
  · intro v
    exact Finset.measurable_sum _ (fun i _ => ((measurable_centeredLoss D φ hφ v).comp
      (measurable_pi_apply i)).const_mul _)
  · intro S
    exact continuous_finset_sum _ (fun i _ => ((continuous_centeredLoss D φ (S i)).comp
      continuous_subtype_val).const_mul _)

lemma centered_rad_bound {n : ℕ} (hn : 0 < n) (D : ℕ) (φ : X → Vec D)
    (R : ℝ) (hR : 0 ≤ R) (S : Fin n → X × Bool) :
    rademacher (evalSet (lossClass (centeredLoss D φ) (Metric.closedBall 0 R)) S) ≤
      R / n * Real.sqrt (∑ i, ‖φ (S i).1‖ ^ 2) := by
  classical
  let A := linearEvalSet R (fun i => φ (S i).1)
  have hA : A.Nonempty := ⟨0,0,by simpa using hR,by ext; simp⟩
  have he : A = (fun v : Vec D => fun i : Fin n => inner ℝ v (φ (S i).1)) '' Metric.closedBall 0 R := by
    ext a
    simp only [A,linearEvalSet,Set.mem_setOf_eq,Set.mem_image,Metric.mem_closedBall,dist_zero_right]
    constructor <;> rintro ⟨v,hv,h⟩ <;> exact ⟨v,hv,h.symm⟩
  have hb : Bornology.IsBounded A := by
    rw [he]
    exact ((isCompact_closedBall (0 : Vec D) R).image (continuous_pi (fun i =>
      continuous_id.inner continuous_const))).isBounded
  let f : Fin n → ℝ → ℝ := fun i a => |a - label (S i).2| - 1
  have hf : ∀ i, LipschitzWith 1 (f i) := by
    intro i
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [f,Real.dist_eq,NNReal.coe_one,one_mul,sub_sub_sub_cancel_right] using
      abs_abs_sub_abs_le_abs_sub (a - label (S i).2) (b - label (S i).2)
  have him : (fun a i => f i (a i)) '' A =
      evalSet (lossClass (centeredLoss D φ) (Metric.closedBall 0 R)) S := by
    ext a
    constructor
    · rintro ⟨b,⟨v,hv,rfl⟩,rfl⟩
      exact ⟨centeredLoss D φ v,⟨v,by simpa using hv,rfl⟩,rfl⟩
    · rintro ⟨g,⟨v,hv,rfl⟩,rfl⟩
      exact ⟨fun i => inner ℝ v (φ (S i).1),⟨v,by simpa using hv,rfl⟩,rfl⟩
  have hc := contraction_lemma A hA hb 1 f hf
  rw [him] at hc
  simp only [NNReal.coe_one,one_mul] at hc
  exact hc.trans (rademacher_linear_bound hn _ R hR)
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
open PrivateAgnosticHalfspace.Symmetrization
variable {X : Type*} [MeasurableSpace X]

lemma centeredRisk_eq (D : ℕ) (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (φ : X → Vec D) (hφ : Measurable φ) (hi : Integrable (fun z : X × Bool => ‖φ z.1‖) P)
    (v : Vec D) : UnderstandingML.risk (centeredLoss D φ) P v = risk D φ P v - 1 := by
  have hc := integrable_centeredLoss D P φ hφ hi v
  have hfull : Integrable (fun z : X × Bool => |inner ℝ v (φ z.1)-label z.2|) P := by
    convert! hc.add (integrable_const 1) using 1
    funext z; simp [centeredLoss]
  unfold UnderstandingML.risk centeredLoss risk
  rw [integral_sub hfull (integrable_const 1),integral_const,probReal_univ,one_smul]

lemma centeredEmp_eq {n : ℕ} (hn : 0 < n) (D : ℕ) (φ : X → Vec D)
    (S : Fin n → X × Bool) (v : Vec D) :
    empRisk (centeredLoss D φ) S v = empiricalRisk D φ S v - 1 := by
  unfold empRisk centeredLoss empiricalRisk
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  field_simp

lemma centered_rep_eq {n : ℕ} (hn : 0 < n) (D : ℕ) (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (φ : X → Vec D) (hφ : Measurable φ) (hi : Integrable (fun z : X × Bool => ‖φ z.1‖) P)
    (R : ℝ) (S : Fin n → X × Bool) :
    representativeness (centeredLoss D φ) (Metric.closedBall 0 R) P S = deviation D φ P R S := by
  unfold representativeness deviation
  simp_rw [centeredRisk_eq D P φ hφ hi,centeredEmp_eq hn D φ,sub_sub_sub_cancel_right]
  rw [← sSup_range]
  congr 1
  ext z
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨v,v.2,hv⟩
  · rintro ⟨v,hv,h⟩
    exact ⟨⟨v,hv⟩,h⟩

lemma expected_sqrt_sample {n : ℕ} (D : ℕ) (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (φ : X → Vec D) (hφ : Measurable φ)
    (hi : Integrable (fun z : X × Bool => ‖φ z.1‖ ^ 2) P)
    (hm : (∫ z, ‖φ z.1‖ ^ 2 ∂P) ≤ D) :
    Integrable (fun S : Fin n → X × Bool => Real.sqrt (∑ i, ‖φ (S i).1‖ ^ 2)) (iidLaw P n) ∧
    (∫ S : Fin n → X × Bool, Real.sqrt (∑ i, ‖φ (S i).1‖ ^ 2) ∂iidLaw P n) ≤
      Real.sqrt ((n : ℝ) * D) := by
  classical
  haveI : IsProbabilityMeasure (iidLaw P n) := by unfold iidLaw; infer_instance
  let Q : (Fin n → X × Bool) → ℝ := fun S => ∑ i, ‖φ (S i).1‖ ^ 2
  have hqm : Measurable Q := Finset.measurable_sum _ (fun i _ =>
    (((hφ.comp measurable_fst).comp (measurable_pi_apply i)).norm).pow_const _)
  have hq0 : ∀ S, 0 ≤ Q S := fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hqi : Integrable Q (iidLaw P n) := by
    apply integrable_finsetSum
    intro i _
    exact (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp_of_integrable hi
  have he : (∫ S, Q S ∂iidLaw P n) = (n : ℝ) * ∫ z, ‖φ z.1‖ ^ 2 ∂P := by
    unfold Q
    have hfint (i : Fin n) : Integrable (fun S : Fin n → X × Bool => ‖φ (S i).1‖ ^ 2) (iidLaw P n) := by
      simpa only [Function.comp_def,iidLaw] using
        (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp_of_integrable hi
    rw [integral_finsetSum _ (fun i _ => hfint i)]
    have hev (i : Fin n) :
        (∫ S : Fin n → X × Bool, ‖φ (S i).1‖ ^ 2 ∂iidLaw P n) = ∫ z, ‖φ z.1‖ ^ 2 ∂P :=
      integral_eval P (fun z : X × Bool => ‖φ z.1‖ ^ 2) ((hφ.comp measurable_fst).norm.pow_const 2) i
    simp_rw [hev]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  refine ⟨integrable_sqrt _ Q hqm hq0 hqi, (expected_sqrt_le _ Q hqm hq0 hqi).trans ?_⟩
  rw [he]
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _))

lemma centered_rad_nonneg {n : ℕ} (D : ℕ) (φ : X → Vec D) (R : ℝ) (hR : 0 ≤ R)
    (S : Fin n → X × Bool) :
    0 ≤ rademacher (evalSet (lossClass (centeredLoss D φ) (Metric.closedBall 0 R)) S) := by
  classical
  have hH : (Metric.closedBall (0 : Vec D) R).Nonempty := ⟨0,by simpa using hR⟩
  have hc : ∀ v ∈ Metric.closedBall (0 : Vec D) R, ∀ z,
      |centeredLoss D φ v z| ≤ R * ‖φ z.1‖ := fun v hv => centered_envelope D φ R ⟨v,hv⟩
  unfold rademacher
  apply mul_nonneg (by positivity)
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro σ _
  rw [iSup_evalSet (centeredLoss D φ) (Metric.closedBall 0 R) hH (fun z => R * ‖φ z.1‖) hc]
  have hb := bddAbove_of_abs (fun v : Metric.closedBall (0 : Vec D) R =>
    ∑ i, signVec σ i * centeredLoss D φ v (S i)) (∑ i, R * ‖φ (S i).1‖)
    (fun v => abs_signed_sum_le σ _ _ (fun i => hc v v.2 _))
  have hz := le_ciSup hb (⟨0,by simpa using hR⟩ : Metric.closedBall (0 : Vec D) R)
  simpa [centeredLoss,abs_label] using hz
end PrivateAgnosticHalfspace.Gaussian

open PrivateAgnosticHalfspace.Symmetrization in
theorem solution {X : Type*} [MeasurableSpace X]
    (D n : ℕ) (hn : 0 < n) (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (φ : X → PrivateAgnosticHalfspace.Gaussian.Vec D) (hφ : Measurable φ)
    (hfinite : Integrable (fun z : X × Bool => ‖φ z.1‖ ^ 2) P)
    (hmoment : (∫ z, ‖φ z.1‖ ^ 2 ∂P) ≤ D) (R : ℝ) (hR : 0 < R) :
    (∀ v, Integrable (fun z : X × Bool => |inner ℝ v (φ z.1) - PrivateAgnosticHalfspace.Gaussian.label z.2|) P) ∧
    (∀ S : Fin n → X × Bool,
      BddAbove ((fun v => PrivateAgnosticHalfspace.Gaussian.risk D φ P v -
        PrivateAgnosticHalfspace.Gaussian.empiricalRisk D φ S v) '' Metric.closedBall 0 R)) ∧
    Integrable (PrivateAgnosticHalfspace.Gaussian.deviation D φ P R (n := n)) (Measure.pi (fun _ : Fin n => P)) ∧
    (∫ S, PrivateAgnosticHalfspace.Gaussian.deviation D φ P R S ∂Measure.pi (fun _ : Fin n => P)) ≤
      2 * R * Real.sqrt ((D : ℝ) / n) := by
  classical
  letI : IsProbabilityMeasure (iidLaw P n) := by unfold iidLaw; infer_instance
  let B : X × Bool → ℝ := fun z => R * ‖φ z.1‖
  let H := Metric.closedBall (0 : PrivateAgnosticHalfspace.Gaussian.Vec D) R
  let ℓ := PrivateAgnosticHalfspace.Gaussian.centeredLoss D φ
  have hi := PrivateAgnosticHalfspace.Gaussian.integrable_feature_norm D P φ hφ hfinite
  have hBm : Measurable B := ((hφ.comp measurable_fst).norm).const_mul R
  have hBi : Integrable B P := hi.const_mul R
  have hB0 : ∀ z, 0 ≤ B z := fun _ => mul_nonneg hR.le (norm_nonneg _)
  have hH : H.Nonempty := ⟨0,by simpa [H] using hR.le⟩
  haveI : Nonempty H := hH.to_subtype
  have hLm : ∀ v ∈ H, Measurable (ℓ v) := fun v _ =>
    PrivateAgnosticHalfspace.Gaussian.measurable_centeredLoss D φ hφ v
  have hLc : ∀ v ∈ H, ∀ z, |ℓ v z| ≤ B z := fun v hv =>
    PrivateAgnosticHalfspace.Gaussian.centered_envelope D φ R ⟨v,hv⟩
  have hrepabs (S : Fin n → X × Bool) :
      |representativeness ℓ H P S| ≤ (∫ z, B z ∂P) + empEnvelope B S := by
    apply abs_iSup_le
    intro v
    exact (abs_sub _ _).trans (add_le_add
      (abs_risk_le ℓ B P v (hLc v v.2) hBi (hLm v v.2))
      (abs_empRisk_le hn ℓ B v (hLc v v.2) S))
  have hrepM := PrivateAgnosticHalfspace.Gaussian.measurable_centered_rep D P φ hφ hi R (n := n)
  have hrepI : Integrable (fun S : Fin n → X × Bool => representativeness ℓ H P S) (iidLaw P n) := by
    apply ((integrable_const (∫ z, B z ∂P)).add (integrable_empEnvelope B P hBi)).mono'
      hrepM.aestronglyMeasurable
    exact ae_of_all _ (fun S => by simpa only [Real.norm_eq_abs,Pi.add_apply] using hrepabs S)
  have he (S : Fin n → X × Bool) : representativeness ℓ H P S =
      PrivateAgnosticHalfspace.Gaussian.deviation D φ P R S :=
    PrivateAgnosticHalfspace.Gaussian.centered_rep_eq hn D P φ hφ hi R S
  have hfirst : ∀ v, Integrable (fun z : X × Bool =>
      |inner ℝ v (φ z.1) - PrivateAgnosticHalfspace.Gaussian.label z.2|) P := by
    intro v
    convert! (PrivateAgnosticHalfspace.Gaussian.integrable_centeredLoss D P φ hφ hi v).add
      (integrable_const 1) using 1
    funext z
    simp [PrivateAgnosticHalfspace.Gaussian.centeredLoss]
  refine ⟨hfirst,?_,?_,?_⟩
  · intro S
    refine ⟨(∫ z, B z ∂P) + empEnvelope B S,?_⟩
    rintro _ ⟨v,hv,rfl⟩
    have hd : PrivateAgnosticHalfspace.Gaussian.risk D φ P v -
        PrivateAgnosticHalfspace.Gaussian.empiricalRisk D φ S v =
        UnderstandingML.risk ℓ P v - empRisk ℓ S v := by
      rw [PrivateAgnosticHalfspace.Gaussian.centeredRisk_eq D P φ hφ hi,
        PrivateAgnosticHalfspace.Gaussian.centeredEmp_eq hn D φ]; ring
    dsimp only
    rw [hd]
    exact (le_abs_self _).trans ((abs_sub _ _).trans (add_le_add
      (abs_risk_le ℓ B P v (hLc v hv) hBi (hLm v hv))
      (abs_empRisk_le hn ℓ B v (hLc v hv) S)))
  · simpa only [he,iidLaw] using hrepI
  · have hradM := PrivateAgnosticHalfspace.Gaussian.measurable_centered_rad D φ hφ R hR.le (n := n)
    have hsqrt := PrivateAgnosticHalfspace.Gaussian.expected_sqrt_sample D P φ hφ hfinite hmoment (n := n)
    have hradI : Integrable (fun S : Fin n → X × Bool => rademacher (evalSet (lossClass ℓ H) S)) (iidLaw P n) := by
      apply (hsqrt.1.const_mul (R / n)).mono' hradM.aestronglyMeasurable
      exact ae_of_all _ (fun S => by
        simp only [Real.norm_eq_abs,abs_of_nonneg
          (PrivateAgnosticHalfspace.Gaussian.centered_rad_nonneg D φ R hR.le S)]
        exact PrivateAgnosticHalfspace.Gaussian.centered_rad_bound hn D φ R hR.le S)
    have hsym := representativeness_le_rademacher_envelope ℓ H hH P B hB0 hBm hBi hLc hLm n hn
      hrepM hradM (PrivateAgnosticHalfspace.Gaussian.measurable_centered_double D φ hφ R)
    have hlin := integral_mono hradI (hsqrt.1.const_mul (R / n))
      (PrivateAgnosticHalfspace.Gaussian.centered_rad_bound hn D φ R hR.le)
    rw [integral_const_mul] at hlin
    have hbound := hlin.trans (mul_le_mul_of_nonneg_left hsqrt.2 (by positivity : (0 : ℝ) ≤ R / n))
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hs : Real.sqrt ((n : ℝ) * D) / n = Real.sqrt ((D : ℝ) / n) := by
      calc
        _ = Real.sqrt ((n : ℝ) * D) / Real.sqrt ((n : ℝ) ^ 2) := by rw [Real.sqrt_sq (Nat.cast_nonneg n)]
        _ = Real.sqrt (((n : ℝ) * D) / (n : ℝ) ^ 2) := (Real.sqrt_div (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg D)) _).symm
        _ = _ := congrArg Real.sqrt (by field_simp)
    have heq : R / n * Real.sqrt ((n : ℝ) * D) = R * Real.sqrt ((D : ℝ) / n) := by
      rw [← hs]; ring
    rw [heq] at hbound
    have hfinal := hsym.trans (mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 2))
    simpa only [he,iidLaw,mul_assoc] using hfinal
