-- Prove2me | solution 1 for UnderstandingML.rademacher_generalization
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T16:14:58.957992+00:00
-- url     : https://prove2.me/submissions/86e5a056-b93a-4a71-a212-0bd9c567885b

import Theorems.Thm_UnderstandingML_representativeness_le_rademacher
import Theorems.Thm_UnderstandingML_mcdiarmid_inequality_pi
import Mathlib.Logic.Equiv.Bool

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML.GenAux

variable {Z Hyp : Type*} [MeasurableSpace Z]

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


omit [MeasurableSpace Z] in
/-- Replacing one example changes the empirical risk by at most `2c/m`. -/
lemma abs_empRisk_update_le {m : ℕ} (c : ℝ) (h : Hyp) (hc : ∀ z, |loss h z| ≤ c)
    (S : Fin m → Z) (i : Fin m) (z : Z) :
    |empRisk loss S h - empRisk loss (Function.update S i z) h| ≤ 2 * c / m := by
  classical
  unfold empRisk
  rw [div_sub_div_same, abs_div, Nat.abs_cast, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · gcongr
    simp only [Function.update_self]
    calc |loss h (S i) - loss h z| ≤ |loss h (S i)| + |loss h z| := abs_sub _ _
      _ ≤ 2 * c := by linarith [hc (S i), hc z]
  · intro j _ hj; simp [Function.update_of_ne hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma abs_ciSup_sub_ciSup_le {ι : Type*} [Nonempty ι] (a b : ι → ℝ) (C K : ℝ)
    (ha : ∀ i, |a i| ≤ C) (hb : ∀ i, |b i| ≤ C) (hab : ∀ i, |a i - b i| ≤ K) :
    |(⨆ i, a i) - ⨆ i, b i| ≤ K := by
  have hba : BddAbove (Set.range a) := bddAbove_of_abs a C ha
  have hbb : BddAbove (Set.range b) := bddAbove_of_abs b C hb
  rw [abs_le]
  constructor
  · have : (⨆ i, b i) ≤ (⨆ i, a i) + K := ciSup_le (fun i ↦ by
      have := (abs_le.1 (hab i)).1
      linarith [le_ciSup hba i])
    linarith
  · have : (⨆ i, a i) ≤ (⨆ i, b i) + K := ciSup_le (fun i ↦ by
      have := (abs_le.1 (hab i)).2
      linarith [le_ciSup hbb i])
    linarith

/-- The McDiarmid bound for a function with bounded differences `2c/m`. -/
lemma mcdiarmid_two_c {m : ℕ} (hm : 0 < m) (D : Measure Z) [IsProbabilityMeasure D] (c : ℝ)
    (f : (Fin m → Z) → ℝ) (hf : Measurable f)
    (hfc : ∀ (S : Fin m → Z) (i : Fin m) (z : Z), |f S - f (Function.update S i z)| ≤ 2 * c / m)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    iidLaw D m {S | c * Real.sqrt (2 * Real.log (2 / δ) / m) <
      |f S - ∫ S', f S' ∂(iidLaw D m)|} ≤ ENNReal.ofReal δ := by
  have h := mcdiarmid_inequality_pi m (fun _ ↦ D) f hf (2 * c / m) hfc δ hδ hδ1
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have e : 2 * c / m * Real.sqrt (Real.log (2 / δ) * m / 2) =
      c * Real.sqrt (2 * Real.log (2 / δ) / m) := by
    calc 2 * c / m * Real.sqrt (Real.log (2 / δ) * m / 2)
        = c * ((2 / m) * Real.sqrt (Real.log (2 / δ) * m / 2)) := by ring
      _ = c * (Real.sqrt ((2 / m) ^ 2) * Real.sqrt (Real.log (2 / δ) * m / 2)) := by
          rw [Real.sqrt_sq (by positivity)]
      _ = c * Real.sqrt ((2 / m) ^ 2 * (Real.log (2 / δ) * m / 2)) := by
          rw [← Real.sqrt_mul (by positivity)]
      _ = c * Real.sqrt (2 * Real.log (2 / δ) / m) := by
          congr 2; field_simp; try ring
  rw [e] at h
  exact h

end UnderstandingML.GenAux

open UnderstandingML UnderstandingML.GenAux in
theorem solution {Z Hyp : Type*} [MeasurableSpace Z]
    (loss : Hyp → Z → ℝ) (H : Set Hyp) (hH : H.Nonempty) (c : ℝ)
    (hc : ∀ h ∈ H, ∀ z, |loss h z| ≤ c) (hmeas : ∀ h ∈ H, Measurable (loss h))
    (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) (hm : 0 < m)
    (hrep : Measurable (fun S : Fin m → Z ↦ representativeness loss H D S))
    (hrad : Measurable (fun S : Fin m → Z ↦ rademacher (evalSet (lossClass loss H) S)))
    (hdbl : Measurable (fun p : (Fin m → Z) × (Fin m → Z) ↦
      ⨆ h : H, (empRisk loss p.2 (h : Hyp) - empRisk loss p.1 (h : Hyp))))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (iidLaw D m {S | ∃ h ∈ H,
      2 * (∫ S', rademacher (evalSet (lossClass loss H) S') ∂(iidLaw D m)) +
        c * Real.sqrt (2 * Real.log (2 / δ) / m) < risk loss D h - empRisk loss S h} ≤
      ENNReal.ofReal δ) ∧
    (iidLaw D m {S | ∃ h ∈ H,
      2 * rademacher (evalSet (lossClass loss H) S) + 4 * c * Real.sqrt (2 * Real.log (4 / δ) / m) <
        risk loss D h - empRisk loss S h} ≤ ENNReal.ofReal δ) ∧
    (∀ (A : Learner Z Hyp), IsERMLearner loss H A → ∀ hstar ∈ H,
      iidLaw D m {S | 2 * rademacher (evalSet (lossClass loss H) S) +
        5 * c * Real.sqrt (2 * Real.log (8 / δ) / m) < risk loss D (A m S) - risk loss D hstar} ≤
      ENNReal.ofReal δ) := by
  classical
  have hNe : Nonempty H := hH.to_subtype
  obtain ⟨h0, hh0⟩ := hH
  have hZ : Nonempty Z := by
    by_contra hZ
    rw [not_nonempty_iff] at hZ
    have := measure_univ (μ := D)
    rw [Set.univ_eq_empty_iff.2 hZ, measure_empty] at this
    exact zero_ne_one this
  obtain ⟨z0⟩ := hZ
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc h0 hh0 z0)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set μ := iidLaw D m with hμ
  set Rep : (Fin m → Z) → ℝ := fun S ↦ representativeness loss H D S with hRep
  set Rad : (Fin m → Z) → ℝ := fun S ↦ rademacher (evalSet (lossClass loss H) S) with hRad
  -- basic bounds
  have hdiffb : ∀ (h : H) (S : Fin m → Z), |risk loss D (h : Hyp) - empRisk loss S (h : Hyp)| ≤ 2 * c := by
    intro h S
    have h1 := abs_empRisk_le loss hm c h (hc h h.2) S
    have h2 := abs_risk_le loss D c h (hc h h.2)
    calc _ ≤ |risk loss D (h : Hyp)| + |empRisk loss S (h : Hyp)| := abs_sub _ _
      _ ≤ 2 * c := by linarith
  have hRep_ge : ∀ S, ∀ h ∈ H, risk loss D h - empRisk loss S h ≤ Rep S := fun S h hh ↦
    le_ciSup (f := fun h : H ↦ risk loss D (h : Hyp) - empRisk loss S (h : Hyp))
      (bddAbove_of_abs _ _ (fun h ↦ hdiffb h S)) ⟨h, hh⟩
  -- the Rademacher complexity as a supremum over `H`
  have hRadS : ∀ T : Fin m → Z, Rad T = (1 / m) * ((1 / 2 ^ m) *
      ∑ σ : Fin m → Bool, ⨆ h : H, ∑ i, signVec σ i * loss h (T i)) := by
    intro T
    simp only [hRad, rademacher]
    congr 2
    exact Finset.sum_congr rfl (fun σ _ ↦ iSup_evalSet loss H ⟨h0, hh0⟩ c hc T σ)
  -- bounded differences
  have hRep_bd : ∀ (S : Fin m → Z) (i : Fin m) (z : Z),
      |Rep S - Rep (Function.update S i z)| ≤ 2 * c / m := by
    intro S i z
    refine abs_ciSup_sub_ciSup_le _ _ (2 * c) _ (fun h ↦ hdiffb h S)
      (fun h ↦ hdiffb h _) (fun h ↦ ?_)
    have := abs_empRisk_update_le loss c h (hc h h.2) S i z
    rw [abs_sub_comm] at this
    calc _ = |empRisk loss (Function.update S i z) (h : Hyp) - empRisk loss S (h : Hyp)| := by
          congr 1; ring
      _ ≤ 2 * c / m := this
  have hRad_bd : ∀ (S : Fin m → Z) (i : Fin m) (z : Z),
      |Rad S - Rad (Function.update S i z)| ≤ 2 * c / m := by
    intro S i z
    rw [hRadS, hRadS, ← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / m), abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ m)]
    have hσ : ∀ σ : Fin m → Bool, |(⨆ h : H, ∑ j, signVec σ j * loss h (S j)) -
        ⨆ h : H, ∑ j, signVec σ j * loss h (Function.update S i z j)| ≤ 2 * c := by
      intro σ
      refine abs_ciSup_sub_ciSup_le _ _ (m * c) _
        (fun h ↦ abs_signed_sum_le σ _ c (fun j ↦ hc h h.2 _))
        (fun h ↦ abs_signed_sum_le σ _ c (fun j ↦ hc h h.2 _)) (fun h ↦ ?_)
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
      · simp only [Function.update_self, ← mul_sub, abs_mul, abs_signVec, one_mul]
        calc |loss h (S i) - loss h z| ≤ |loss h (S i)| + |loss h z| := abs_sub _ _
          _ ≤ 2 * c := by linarith [hc h h.2 (S i), hc h h.2 z]
      · intro j _ hj; simp [Function.update_of_ne hj]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    have hsum : |∑ σ : Fin m → Bool, ((⨆ h : H, ∑ j, signVec σ j * loss h (S j)) -
        ⨆ h : H, ∑ j, signVec σ j * loss h (Function.update S i z j))| ≤ 2 ^ m * (2 * c) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ _σ : Fin m → Bool, 2 * c := Finset.sum_le_sum (fun σ _ ↦ hσ σ)
        _ = 2 ^ m * (2 * c) := by simp [Finset.card_univ, Fintype.card_bool, Fintype.card_fin]
    calc 1 / (m : ℝ) * (1 / 2 ^ m * |∑ σ : Fin m → Bool, ((⨆ h : H, ∑ j, signVec σ j * loss h (S j)) -
          ⨆ h : H, ∑ j, signVec σ j * loss h (Function.update S i z j))|)
        ≤ 1 / (m : ℝ) * (1 / 2 ^ m * (2 ^ m * (2 * c))) := by gcongr
      _ = 2 * c / m := by field_simp
  -- Lemma 26.2
  have h262 := representativeness_le_rademacher loss H ⟨h0, hh0⟩ c hc hmeas D m hm hrep hrad hdbl
  -- auxiliary: bounds and logs
  have hlog_mono : ∀ a b : ℝ, 0 < a → a ≤ b →
      c * Real.sqrt (2 * Real.log a / m) ≤ c * Real.sqrt (2 * Real.log b / m) := by
    intro a b ha hab
    gcongr
  have hδ2 : 2 / (δ / 2) = 4 / δ := by field_simp; ring
  have hδ4 : 2 / (δ / 4) = 8 / δ := by field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · -- part 1
    refine le_trans (measure_mono (fun S hS ↦ ?_)) (mcdiarmid_two_c hm D c Rep hrep hRep_bd δ hδ hδ1)
    obtain ⟨h, hh, hlt⟩ := hS
    simp only [Set.mem_setOf_eq]
    have := hRep_ge S h hh
    refine lt_of_lt_of_le ?_ (le_abs_self _)
    linarith
  · -- part 2
    set ε := c * Real.sqrt (2 * Real.log (4 / δ) / m) with hε
    have hε0 : 0 ≤ ε := by positivity
    have hA := mcdiarmid_two_c hm D c Rep hrep hRep_bd (δ / 2) (by positivity) (by linarith)
    have hB := mcdiarmid_two_c hm D c Rad hrad hRad_bd (δ / 2) (by positivity) (by linarith)
    rw [hδ2] at hA hB
    refine le_trans (measure_mono (t := {S | ε < |Rep S - ∫ S', Rep S' ∂μ|} ∪
      {S | ε < |Rad S - ∫ S', Rad S' ∂μ|}) (fun S hS ↦ ?_)) ?_
    · obtain ⟨h, hh, hlt⟩ := hS
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hcon
      have h1 := (abs_le.1 hcon.1).2
      have h2 := (abs_le.1 hcon.2).1
      have := hRep_ge S h hh
      have : risk loss D h - empRisk loss S h ≤ 2 * Rad S + 4 * c * Real.sqrt (2 * Real.log (4 / δ) / m) := by
        rw [mul_assoc 4]; linarith
      linarith
    · refine (measure_union_le _ _).trans ?_
      calc _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hA hB
        _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  · -- part 3
    intro A hA hstar hhstar
    set ε := c * Real.sqrt (2 * Real.log (8 / δ) / m) with hε
    have hε0 : 0 ≤ ε := by positivity
    have hE1 := mcdiarmid_two_c hm D c Rep hrep hRep_bd (δ / 4) (by positivity) (by linarith)
    have hE2 := mcdiarmid_two_c hm D c Rad hrad hRad_bd (δ / 4) (by positivity) (by linarith)
    have hE3 := mcdiarmid_two_c hm D c (fun S ↦ empRisk loss S hstar)
      (measurable_empRisk loss hstar (hmeas hstar hhstar))
      (fun S i z ↦ abs_empRisk_update_le loss c hstar (hc hstar hhstar) S i z) (δ / 2)
      (by positivity) (by linarith)
    rw [hδ4] at hE1 hE2
    rw [hδ2] at hE3
    rw [integral_empRisk loss hm D c hstar (hc hstar hhstar) (hmeas hstar hhstar)] at hE3
    have hε' : c * Real.sqrt (2 * Real.log (4 / δ) / m) ≤ ε :=
      hlog_mono _ _ (by positivity) (by gcongr; norm_num)
    refine le_trans (measure_mono (t := {S | ε < |Rep S - ∫ S', Rep S' ∂μ|} ∪
      {S | ε < |Rad S - ∫ S', Rad S' ∂μ|} ∪
      {S | c * Real.sqrt (2 * Real.log (4 / δ) / m) < |empRisk loss S hstar - risk loss D hstar|})
      (fun S hS ↦ ?_)) ?_
    · by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hcon hS
      have h1 := (abs_le.1 hcon.1.1).2
      have h2 := (abs_le.1 hcon.1.2).1
      have h3 := (abs_le.1 hcon.2).2
      have hAS := hA m S
      have h4 := hRep_ge S (A m S) hAS.1
      have h5 := hAS.2 hstar hhstar
      have : risk loss D (A m S) - risk loss D hstar ≤ 2 * Rad S + 5 * c * Real.sqrt (2 * Real.log (8 / δ) / m) := by
        rw [mul_assoc 5]; linarith
      linarith
    · refine (measure_union_le _ _).trans ?_
      refine (add_le_add (measure_union_le _ _) le_rfl).trans ?_
      calc _ ≤ ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 2) :=
            add_le_add (add_le_add hE1 hE2) hE3
        _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
