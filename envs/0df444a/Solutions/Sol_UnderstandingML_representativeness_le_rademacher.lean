-- Prove2me | solution 1 for UnderstandingML.representativeness_le_rademacher
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T16:02:39.060447+00:00
-- url     : https://prove2.me/submissions/4d39d6fc-9656-4171-becc-53616cc44c7c

import Definitions.Def_UnderstandingML_Rademacher
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Logic.Equiv.Bool

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML.SymmAux

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

lemma abs_signed_sum_le {m : ℕ} (σ : Fin m → Bool) (x : Fin m → ℝ) (C : ℝ)
    (hx : ∀ i, |x i| ≤ C) : |∑ i, signVec σ i * x i| ≤ m * C := by
  calc |∑ i, signVec σ i * x i| ≤ ∑ i, |signVec σ i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |x i| := by simp only [abs_mul, abs_signVec, one_mul]
    _ ≤ ∑ _i : Fin m, C := Finset.sum_le_sum (fun i _ ↦ hx i)
    _ = m * C := by simp

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

variable (loss : Hyp → Z → ℝ) (H : Set Hyp)

omit [MeasurableSpace Z] in
lemma abs_empRisk_le {m : ℕ} (hm : 0 < m) (c : ℝ) (h : Hyp) (hc : ∀ z, |loss h z| ≤ c)
    (S : Fin m → Z) : |empRisk loss S h| ≤ c := by
  unfold empRisk
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [abs_div, abs_of_pos hm', div_le_iff₀ hm']
  calc |∑ i, loss h (S i)| ≤ ∑ i, |loss h (S i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, c := Finset.sum_le_sum (fun i _ ↦ hc _)
    _ = c * m := by simp [mul_comm]

lemma abs_risk_le (D : Measure Z) [IsProbabilityMeasure D] (c : ℝ) (h : Hyp)
    (hc : ∀ z, |loss h z| ≤ c) : |risk loss D h| ≤ c := by
  unfold risk
  have := norm_integral_le_of_norm_le_const (μ := D) (f := loss h) (C := c)
    (Filter.Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs]; exact hc z))
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

lemma measurable_empRisk {m : ℕ} (h : Hyp) (hmeas : Measurable (loss h)) :
    Measurable (fun S : Fin m → Z ↦ empRisk loss S h) := by
  unfold empRisk
  refine Measurable.div_const ?_ _
  exact Finset.measurable_sum _ (fun i _ ↦ hmeas.comp (measurable_pi_apply i))

lemma integral_empRisk {m : ℕ} (hm : 0 < m) (D : Measure Z) [IsProbabilityMeasure D] (c : ℝ)
    (h : Hyp) (hc : ∀ z, |loss h z| ≤ c) (hmeas : Measurable (loss h)) :
    ∫ S, empRisk loss S h ∂(iidLaw D m) = risk loss D h := by
  have : IsProbabilityMeasure (iidLaw D m) := by unfold iidLaw; infer_instance
  unfold empRisk
  rw [integral_div, integral_finset_sum]
  · simp only [integral_eval D _ hmeas, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    unfold risk; field_simp
  · intro i _
    refine Integrable.of_bound (hmeas.comp (measurable_pi_apply i)).aestronglyMeasurable c ?_
    exact Filter.Eventually.of_forall (fun S ↦ by rw [Real.norm_eq_abs]; exact hc _)

omit [MeasurableSpace Z] in
/-- The Rademacher complexity of `ℓ ∘ H ∘ S` as a supremum over `H`. -/
lemma iSup_evalSet {m : ℕ} (hH : H.Nonempty) (c : ℝ) (hc : ∀ h ∈ H, ∀ z, |loss h z| ≤ c)
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

end UnderstandingML.SymmAux

open UnderstandingML UnderstandingML.SymmAux in
theorem solution {Z Hyp : Type*} [MeasurableSpace Z]
    (loss : Hyp → Z → ℝ) (H : Set Hyp) (hH : H.Nonempty) (c : ℝ)
    (hc : ∀ h ∈ H, ∀ z, |loss h z| ≤ c) (hmeas : ∀ h ∈ H, Measurable (loss h))
    (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) (hm : 0 < m)
    (hrep : Measurable (fun S : Fin m → Z ↦ representativeness loss H D S))
    (hrad : Measurable (fun S : Fin m → Z ↦ rademacher (evalSet (lossClass loss H) S)))
    (hdbl : Measurable (fun p : (Fin m → Z) × (Fin m → Z) ↦
      ⨆ h : H, (empRisk loss p.2 (h : Hyp) - empRisk loss p.1 (h : Hyp)))) :
    ∫ S, representativeness loss H D S ∂(iidLaw D m) ≤
      2 * ∫ S, rademacher (evalSet (lossClass loss H) S) ∂(iidLaw D m) := by
  classical
  set μ := iidLaw D m with hμ
  have hμP : IsProbabilityMeasure μ := by rw [hμ]; unfold iidLaw; infer_instance
  have hNe : Nonempty H := hH.to_subtype
  obtain ⟨h0, hh0⟩ := hH
  -- `Z` is nonempty, hence `c ≥ 0`
  have hZ : Nonempty Z := by
    by_contra hZ
    rw [not_nonempty_iff] at hZ
    have := measure_univ (μ := D)
    rw [Set.univ_eq_empty_iff.2 hZ, measure_empty] at this
    exact zero_ne_one this
  obtain ⟨z0⟩ := hZ
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc h0 hh0 z0)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  -- the three random variables and their bounds
  set F : (Fin m → Z) → ℝ := fun S ↦ representativeness loss H D S with hF
  set G : (Fin m → Z) × (Fin m → Z) → ℝ :=
    fun p ↦ ⨆ h : H, (empRisk loss p.2 (h : Hyp) - empRisk loss p.1 (h : Hyp)) with hG
  set Rad : (Fin m → Z) → ℝ := fun S ↦ rademacher (evalSet (lossClass loss H) S) with hRad
  have hdiff : ∀ (h : H) (S S' : Fin m → Z),
      |empRisk loss S' (h : Hyp) - empRisk loss S (h : Hyp)| ≤ 2 * c := by
    intro h S S'
    have h1 := abs_empRisk_le loss hm c h (hc h h.2) S
    have h2 := abs_empRisk_le loss hm c h (hc h h.2) S'
    calc _ ≤ |empRisk loss S' (h : Hyp)| + |empRisk loss S (h : Hyp)| := abs_sub _ _
      _ ≤ 2 * c := by linarith
  have hFb : ∀ S, |F S| ≤ 2 * c := by
    intro S
    refine abs_iSup_le _ _ (fun h ↦ ?_)
    have h1 := abs_empRisk_le loss hm c h (hc h h.2) S
    have h2 := abs_risk_le loss D c h (hc h h.2)
    calc _ ≤ |risk loss D (h : Hyp)| + |empRisk loss S (h : Hyp)| := abs_sub _ _
      _ ≤ 2 * c := by linarith
  have hGb : ∀ p, |G p| ≤ 2 * c := fun p ↦ abs_iSup_le _ _ (fun h ↦ hdiff h p.1 p.2)
  have hRadb : ∀ S, |Rad S| ≤ c := by
    intro S
    simp only [hRad, rademacher]
    have hinner : ∀ σ : Fin m → Bool,
        |⨆ a : evalSet (lossClass loss H) S, ∑ i, signVec σ i * (a : Fin m → ℝ) i| ≤ m * c := by
      intro σ
      rw [iSup_evalSet loss H ⟨h0, hh0⟩ c hc]
      exact abs_iSup_le _ _ (fun h ↦ abs_signed_sum_le σ _ c (fun i ↦ hc h h.2 _))
    have hsum := Finset.abs_sum_le_sum_abs
      (fun σ : Fin m → Bool ↦ ⨆ a : evalSet (lossClass loss H) S,
        ∑ i, signVec σ i * (a : Fin m → ℝ) i) Finset.univ
    have hsum2 : ∑ σ : Fin m → Bool, |⨆ a : evalSet (lossClass loss H) S,
        ∑ i, signVec σ i * (a : Fin m → ℝ) i| ≤ 2 ^ m * (m * c) := by
      calc _ ≤ ∑ _σ : Fin m → Bool, (m : ℝ) * c := Finset.sum_le_sum (fun σ _ ↦ hinner σ)
        _ = 2 ^ m * (m * c) := by
          simp [Finset.card_univ, Fintype.card_bool, Fintype.card_fin]
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / m),
      abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ m)]
    calc 1 / (m : ℝ) * (1 / 2 ^ m * |∑ σ : Fin m → Bool, ⨆ a : evalSet (lossClass loss H) S,
          ∑ i, signVec σ i * (a : Fin m → ℝ) i|)
        ≤ 1 / (m : ℝ) * (1 / 2 ^ m * (2 ^ m * (m * c))) := by
          gcongr; exact hsum.trans hsum2
      _ = c := by field_simp
  -- integrability
  have hFi : Integrable F μ :=
    Integrable.of_bound hrep.aestronglyMeasurable _
      (Filter.Eventually.of_forall (fun S ↦ by rw [Real.norm_eq_abs]; exact hFb S))
  have hGi : Integrable G (μ.prod μ) :=
    Integrable.of_bound hdbl.aestronglyMeasurable _
      (Filter.Eventually.of_forall (fun p ↦ by rw [Real.norm_eq_abs]; exact hGb p))
  have hRadi : Integrable Rad μ :=
    Integrable.of_bound hrad.aestronglyMeasurable _
      (Filter.Eventually.of_forall (fun S ↦ by rw [Real.norm_eq_abs]; exact hRadb S))
  -- Step A: `Rep(S) ≤ E_{S'} G(S, S')`
  have hA : ∀ S, F S ≤ ∫ S', G (S, S') ∂μ := by
    intro S
    have hsec : Integrable (fun S' ↦ G (S, S')) μ :=
      Integrable.of_bound (hdbl.comp measurable_prodMk_left).aestronglyMeasurable _
        (Filter.Eventually.of_forall (fun S' ↦ by rw [Real.norm_eq_abs]; exact hGb _))
    refine ciSup_le (fun h ↦ ?_)
    have hEi : Integrable (fun S' : Fin m → Z ↦ empRisk loss S' (h : Hyp)) μ :=
      Integrable.of_bound (measurable_empRisk loss (h : Hyp) (hmeas h h.2)).aestronglyMeasurable c
        (Filter.Eventually.of_forall (fun S' ↦ by
          rw [Real.norm_eq_abs]; exact abs_empRisk_le loss hm c h (hc h h.2) S'))
    have e : risk loss D (h : Hyp) - empRisk loss S (h : Hyp) =
        ∫ S', (empRisk loss S' (h : Hyp) - empRisk loss S (h : Hyp)) ∂μ := by
      rw [integral_sub hEi (integrable_const _), integral_const, probReal_univ, one_smul,
        integral_empRisk loss hm D c h (hc h h.2) (hmeas h h.2)]
    rw [e]
    refine integral_mono (hEi.sub (integrable_const _)) hsec (fun S' ↦ ?_)
    exact le_ciSup (f := fun h : H ↦ empRisk loss S' (h : Hyp) - empRisk loss S (h : Hyp))
      (bddAbove_of_abs _ _ (fun h ↦ hdiff h S S')) h
  -- Step B
  have hB : ∫ S, F S ∂μ ≤ ∫ p, G p ∂(μ.prod μ) := by
    rw [integral_prod _ hGi]
    exact integral_mono hFi hGi.integral_prod_left hA
  -- Step C: invariance under swaps
  have hC : ∀ σ : Fin m → Bool, ∫ p, G (swapS σ p) ∂(μ.prod μ) = ∫ p, G p ∂(μ.prod μ) := by
    intro σ
    have hp := measurePreserving_swapS D σ
    rw [← integral_map hp.measurable.aemeasurable (by rw [hp.map_eq]; exact hGi.1), hp.map_eq]
  -- Step D: the pointwise symmetrization bound
  have hD : ∀ p : (Fin m → Z) × (Fin m → Z),
      ∑ σ : Fin m → Bool, G (swapS σ p) ≤ 2 ^ m * (Rad p.1 + Rad p.2) := by
    rintro ⟨S, S'⟩
    set a : (Fin m → Bool) → H → ℝ := fun σ h ↦ ∑ i, signVec σ i * loss h (S' i) with ha
    set b : (Fin m → Bool) → H → ℝ := fun σ h ↦ ∑ i, signVec σ i * loss h (S i) with hb
    have hab : ∀ σ (h : H), empRisk loss (swapS σ (S, S')).2 (h : Hyp) -
        empRisk loss (swapS σ (S, S')).1 (h : Hyp) =
        (1 / m) * (a σ h + b (fun j ↦ !σ j) h) := by
      intro σ h
      simp only [ha, hb, empRisk, swapS, signVec_not]
      rw [div_sub_div_same, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, one_div_mul_eq_div]
      congr 1
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      unfold signVec; cases σ i <;> simp <;> ring
    have hba : ∀ σ, BddAbove (Set.range (a σ)) := fun σ ↦
      bddAbove_of_abs _ (m * c) (fun h ↦ abs_signed_sum_le σ _ c (fun i ↦ hc h h.2 _))
    have hbb : ∀ σ, BddAbove (Set.range (b σ)) := fun σ ↦
      bddAbove_of_abs _ (m * c) (fun h ↦ abs_signed_sum_le σ _ c (fun i ↦ hc h h.2 _))
    have hGσ : ∀ σ, G (swapS σ (S, S')) ≤
        (1 / m) * ((⨆ h, a σ h) + ⨆ h, b (fun j ↦ !σ j) h) := by
      intro σ
      simp only [hG]
      refine ciSup_le (fun h ↦ ?_)
      rw [hab]
      gcongr
      · exact le_ciSup (hba σ) h
      · exact le_ciSup (hbb _) h
    have hRadS : ∀ T : Fin m → Z, Rad T = (1 / m) * ((1 / 2 ^ m) *
        ∑ σ : Fin m → Bool, ⨆ h : H, ∑ i, signVec σ i * loss h (T i)) := by
      intro T
      simp only [hRad, rademacher]
      congr 2
      exact Finset.sum_congr rfl (fun σ _ ↦ iSup_evalSet loss H ⟨h0, hh0⟩ c hc T σ)
    calc ∑ σ, G (swapS σ (S, S'))
        ≤ ∑ σ : Fin m → Bool, (1 / m) * ((⨆ h, a σ h) + ⨆ h, b (fun j ↦ !σ j) h) :=
          Finset.sum_le_sum (fun σ _ ↦ hGσ σ)
      _ = (1 / m) * (∑ σ : Fin m → Bool, (⨆ h, a σ h) + ∑ σ : Fin m → Bool, ⨆ h, b σ h) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib,
            ← sum_not (fun σ ↦ ⨆ h, b σ h)]
      _ = 2 ^ m * (Rad (S, S').1 + Rad (S, S').2) := by
          rw [hRadS, hRadS]
          simp only [ha, hb]
          field_simp
          ring
  -- Step E: integrate
  have hGσi : ∀ σ : Fin m → Bool, Integrable (fun p ↦ G (swapS σ p)) (μ.prod μ) := by
    intro σ
    have hp := measurePreserving_swapS D σ
    exact Integrable.of_bound (hdbl.comp hp.measurable).aestronglyMeasurable _
      (Filter.Eventually.of_forall (fun p ↦ by rw [Real.norm_eq_abs]; exact hGb _))
  have hE : 2 ^ m * ∫ p, G p ∂(μ.prod μ) ≤ 2 ^ m * (2 * ∫ S, Rad S ∂μ) := by
    have e1 : 2 ^ m * ∫ p, G p ∂(μ.prod μ) =
        ∫ p, ∑ σ : Fin m → Bool, G (swapS σ p) ∂(μ.prod μ) := by
      rw [integral_finset_sum _ (fun σ _ ↦ hGσi σ)]
      simp only [hC, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul]
      norm_num
    have e2 : ∫ p, 2 ^ m * (Rad p.1 + Rad p.2) ∂(μ.prod μ) = 2 ^ m * (2 * ∫ S, Rad S ∂μ) := by
      rw [integral_const_mul, integral_add (hRadi.comp_fst μ) (hRadi.comp_snd μ),
        integral_fun_fst, integral_fun_snd, probReal_univ, one_smul]
      ring
    rw [e1, ← e2]
    refine integral_mono (integrable_finset_sum _ (fun σ _ ↦ hGσi σ)) ?_ hD
    exact ((hRadi.comp_fst μ).add (hRadi.comp_snd μ)).const_mul _
  have hE' : ∫ p, G p ∂(μ.prod μ) ≤ 2 * ∫ S, Rad S ∂μ :=
    le_of_mul_le_mul_left hE (by positivity)
  exact hB.trans hE'

