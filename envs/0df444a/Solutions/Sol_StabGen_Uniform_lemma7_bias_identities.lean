-- Prove2me | solution 1 for StabGen.Uniform.lemma7_bias_identities
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:24:02.284125+00:00
-- url     : https://prove2.me/submissions/75e0365a-8ce5-4ab4-8584-4eec1aaf3f9f

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Uniform_Stability

-- carved verbatim out of submission 08fae585-26d2-48c6-bea0-1df5b249980c, lines 495-540

section
set_option autoImplicit false
open MeasureTheory FoundationsML.Stability
open StabGen
open StabGen.Uniform
open ProbabilityTheory

lemma b2_perm_integral {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    {m : ℕ} (σ : Equiv.Perm (Fin m)) (G : (Fin m → Z) → ℝ) :
    ∫ S, G (S ∘ σ) ∂(Measure.pi fun _ : Fin m => D) = ∫ S, G S ∂(Measure.pi fun _ : Fin m => D) := by
  have h := measurePreserving_piCongrLeft (fun _ : Fin m => D) σ.symm
  have hfun : ∀ S : Fin m → Z, MeasurableEquiv.piCongrLeft (fun _ : Fin m => Z) σ.symm S = S ∘ σ := by
    intro S
    funext b
    rw [MeasurableEquiv.coe_piCongrLeft]
    simp [Equiv.piCongrLeft_apply_eq_cast]
  have := h.integral_comp' (g := G)
  simpa [hfun] using this

lemma b2_int_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : α → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ x, |F x| ≤ C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

lemma b2_key {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    {n : ℕ} (j : Fin (n + 1)) (H : (Fin (n + 1) → Z) → Z → ℝ)
    (hH : Measurable (Function.uncurry H)) (B : ℝ) (hB : ∀ S z, |H S z| ≤ B) :
    ∫ S, H S (S j) ∂(Measure.pi fun _ : Fin (n + 1) => D)
      = ∫ p : (Fin (n + 1) → Z) × Z, H (Function.update p.1 j p.2) p.2
          ∂((Measure.pi fun _ : Fin (n + 1) => D).prod D) := by
  set μ : Measure (Fin (n + 1) → Z) := Measure.pi fun _ : Fin (n + 1) => D with hμ
  set ν : Measure (Fin n → Z) := Measure.pi fun _ : Fin n => D with hν
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Z) j with he
  have hmp : MeasurePreserving e μ (D.prod ν) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => D) j
  set K : Z × (Fin n → Z) → ℝ := fun q => H (e.symm q) q.1 with hK
  have hKm : Measurable K := by
    have : K = fun q => Function.uncurry H (e.symm q, q.1) := rfl
    rw [this]
    exact hH.comp (e.symm.measurable.prodMk measurable_fst)
  have hKint : Integrable K (D.prod ν) := b2_int_of_bdd _ K hKm B fun q => hB _ _
  have h1 : ∫ S, H S (S j) ∂μ = ∫ q, K q ∂(D.prod ν) := by
    rw [← hmp.integral_comp' K]
    congr 1
    funext S
    simp only [K, MeasurableEquiv.symm_apply_apply]
    rfl
  have hupd : ∀ (S : Fin (n + 1) → Z) (z : Z), Function.update S j z = e.symm (z, (e S).2) := by
    intro S z
    funext k
    by_cases hk : k = j
    · subst hk
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    · obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hk
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      rfl
  have h2 : ∀ z, ∫ S, H (Function.update S j z) z ∂μ = ∫ w, K (z, w) ∂ν := by
    intro z
    have e1 : ∀ S, H (Function.update S j z) z = (fun q : Z × (Fin n → Z) => K (z, q.2)) (e S) := by
      intro S
      simp only [K]
      rw [hupd S z]
    simp_rw [e1]
    rw [hmp.integral_comp' (fun q : Z × (Fin n → Z) => K (z, q.2))]
    have hi : Integrable (fun q : Z × (Fin n → Z) => K (z, q.2)) (D.prod ν) :=
      b2_int_of_bdd _ _ (hKm.comp (measurable_const.prodMk measurable_snd)) B fun q => hB _ _
    rw [integral_prod _ hi]
    simp
  have hRHS : ∫ p : (Fin (n + 1) → Z) × Z, H (Function.update p.1 j p.2) p.2 ∂(μ.prod D)
      = ∫ z, ∫ S, H (Function.update S j z) z ∂μ ∂D := by
    rw [integral_prod_symm]
    exact b2_int_of_bdd _ _ (hH.comp ((measurable_update' (a := j)).prodMk measurable_snd)) B fun p => hB _ _
  rw [hRHS, h1]
  simp_rw [h2]
  rw [integral_prod _ hKint]

lemma b2_perm_prod {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    {m : ℕ} (σ : Equiv.Perm (Fin m)) (G : (Fin m → Z) × Z → ℝ) (hG : Measurable G) (B : ℝ)
    (hB : ∀ p, |G p| ≤ B) :
    ∫ p, G (p.1 ∘ σ, p.2) ∂((Measure.pi fun _ : Fin m => D).prod D)
      = ∫ p, G p ∂((Measure.pi fun _ : Fin m => D).prod D) := by
  have hσ : Measurable (fun S : Fin m → Z => S ∘ σ) := measurable_pi_lambda _ fun i => measurable_pi_apply _
  have h1 : Integrable (fun p : (Fin m → Z) × Z => G (p.1 ∘ σ, p.2)) ((Measure.pi fun _ : Fin m => D).prod D) :=
    b2_int_of_bdd _ _ (hG.comp ((hσ.comp measurable_fst).prodMk measurable_snd)) B fun p => hB _
  have h2 : Integrable G ((Measure.pi fun _ : Fin m => D).prod D) := b2_int_of_bdd _ _ hG B hB
  have e1 : ∫ p, G (p.1 ∘ σ, p.2) ∂((Measure.pi fun _ : Fin m => D).prod D)
      = ∫ z, ∫ S, G (S ∘ σ, z) ∂(Measure.pi fun _ : Fin m => D) ∂D :=
    integral_prod_symm (fun p : (Fin m → Z) × Z => G (p.1 ∘ σ, p.2)) h1
  have e2 : ∫ p, G p ∂((Measure.pi fun _ : Fin m => D).prod D)
      = ∫ z, ∫ S, G (S, z) ∂(Measure.pi fun _ : Fin m => D) ∂D :=
    integral_prod_symm G h2
  rw [e1, e2]
  congr 1
  funext z
  exact b2_perm_integral D σ (fun S => G (S, z))

lemma b2_training_perm {Z : Type*} {m : ℕ} (S : Fin m → Z) (σ : Equiv.Perm (Fin m)) :
    StabGen.Hypothesis.trainingSet (S ∘ σ) = StabGen.Hypothesis.trainingSet S := by
  unfold StabGen.Hypothesis.trainingSet
  rw [← Multiset.map_map]
  congr 1
  have := congrArg Finset.val (Finset.map_univ_equiv σ)
  simpa [Finset.map_val] using this

lemma b2_removeAt_perm {Z : Type*} {m : ℕ} (S : Fin m → Z) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    StabGen.Hypothesis.removeAt (S ∘ σ) i = StabGen.Hypothesis.removeAt S (σ i) := by
  unfold StabGen.Hypothesis.removeAt
  rw [← Multiset.map_map]
  congr 1
  have := Finset.map_erase σ.toEmbedding (Finset.univ : Finset (Fin m)) i
  rw [Finset.map_univ_equiv] at this
  exact congrArg Finset.val this

lemma b2_removeAt_update {Z : Type*} {m : ℕ} (S : Fin m → Z) (j : Fin m) (w : Z) :
    StabGen.Hypothesis.removeAt (Function.update S j w) j = StabGen.Hypothesis.removeAt S j := by
  unfold StabGen.Hypothesis.removeAt
  refine Multiset.map_congr rfl fun k hk => ?_
  have : k ≠ j := (Finset.mem_erase.mp (Finset.mem_val.mp hk)).1
  simp [Function.update_of_ne this]

lemma b2_removeAt_eq {Z : Type*} {n : ℕ} (S : Fin (n + 1) → Z) (j : Fin (n + 1)) :
    StabGen.Hypothesis.removeAt S j
      = StabGen.Hypothesis.trainingSet (fun k : Fin n => S (j.succAbove k)) := by
  unfold StabGen.Hypothesis.removeAt StabGen.Hypothesis.trainingSet
  have h : (Finset.univ : Finset (Fin (n + 1))).erase j = Finset.univ.map (Fin.succAboveEmb j) := by
    conv_lhs => rw [Fin.univ_succAbove n j]
    rw [Finset.erase_cons]
  rw [h, Finset.map_val, Multiset.map_map]
  rfl

lemma b2_avg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {n : ℕ}
    (f : Fin (n + 1) → Ω → ℝ) (hint : ∀ j, Integrable (f j) μ) (c : ℝ)
    (h : ∀ j, ∫ x, f j x ∂μ = c) (hμ : μ Set.univ = 1) :
    ∫ x, ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) * ∑ j, f j x ∂μ = c := by
  rw [integral_const_mul, integral_finset_sum _ (fun j _ => hint j)]
  simp_rw [h]
  simp
  field_simp

lemma b2_abstract {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D] {n : ℕ}
    (Φ1 : (Fin (n + 1) → Z) → Z → ℝ) (Φ2 : Fin (n + 1) → (Fin (n + 1) → Z) → Z → ℝ) (M : ℝ)
    (h1m : Measurable (Function.uncurry Φ1)) (h2m : ∀ j, Measurable (Function.uncurry (Φ2 j)))
    (h1B : ∀ S z, |Φ1 S z| ≤ M) (h2B : ∀ j S z, |Φ2 j S z| ≤ M)
    (s1 : ∀ S z (σ : Equiv.Perm (Fin (n + 1))), Φ1 (S ∘ σ) z = Φ1 S z)
    (s2 : ∀ S z (σ : Equiv.Perm (Fin (n + 1))) i, Φ2 i (S ∘ σ) z = Φ2 (σ i) S z)
    (s3 : ∀ S z j w, Φ2 j (Function.update S j w) z = Φ2 j S z)
    (i : Fin (n + 1)) :
    (∫ S, (∫ z, Φ1 S z ∂D - ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) * ∑ j, Φ1 S (S j))
        ∂(Measure.pi fun _ : Fin (n + 1) => D)
      = ∫ p : (Fin (n + 1) → Z) × Z, (Φ1 p.1 p.2 - Φ1 (Function.update p.1 i p.2) p.2)
          ∂((Measure.pi fun _ : Fin (n + 1) => D).prod D)) ∧
    (∫ S, (∫ z, Φ2 i S z ∂D - ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) * ∑ j, Φ2 j S (S j))
        ∂(Measure.pi fun _ : Fin (n + 1) => D) = 0) ∧
    (∫ S, (∫ z, Φ1 S z ∂D - ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) * ∑ j, Φ2 j S (S j))
        ∂(Measure.pi fun _ : Fin (n + 1) => D)
      = ∫ p : (Fin (n + 1) → Z) × Z, (Φ1 p.1 p.2 - Φ2 i p.1 p.2)
          ∂((Measure.pi fun _ : Fin (n + 1) => D).prod D)) := by
  set μ : Measure (Fin (n + 1) → Z) := Measure.pi fun _ : Fin (n + 1) => D with hμ
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  set N : Measure ((Fin (n + 1) → Z) × Z) := μ.prod D with hN
  have hN1 : Integrable (fun p : (Fin (n + 1) → Z) × Z => Φ1 p.1 p.2) N :=
    b2_int_of_bdd _ _ h1m M fun p => h1B _ _
  have hN2 : ∀ j, Integrable (fun p : (Fin (n + 1) → Z) × Z => Φ2 j p.1 p.2) N := fun j =>
    b2_int_of_bdd _ _ (h2m j) M fun p => h2B _ _ _
  have hupdm : ∀ j, Measurable (fun p : (Fin (n + 1) → Z) × Z => (Function.update p.1 j p.2, p.2)) :=
    fun j => (measurable_update' (a := j)).prodMk measurable_snd
  have hU1 : ∀ j, Integrable (fun p : (Fin (n + 1) → Z) × Z => Φ1 (Function.update p.1 j p.2) p.2) N :=
    fun j => b2_int_of_bdd _ _ (h1m.comp (hupdm j)) M fun p => h1B _ _
  have hdm : ∀ j, Measurable (fun S : Fin (n + 1) → Z => (S, S j)) :=
    fun j => measurable_id.prodMk (measurable_pi_apply j)
  have hD1 : ∀ j, Integrable (fun S : Fin (n + 1) → Z => Φ1 S (S j)) μ :=
    fun j => b2_int_of_bdd _ _ (h1m.comp (hdm j)) M fun S => h1B _ _
  have hD2 : ∀ j, Integrable (fun S : Fin (n + 1) → Z => Φ2 j S (S j)) μ :=
    fun j => b2_int_of_bdd _ _ ((h2m j).comp (hdm j)) M fun S => h2B _ _ _
  have hR1 : Integrable (fun S => ∫ z, Φ1 S z ∂D) μ := hN1.integral_prod_left
  have hR2 : Integrable (fun S => ∫ z, Φ2 i S z ∂D) μ := (hN2 i).integral_prod_left
  have hR1' : ∫ S, ∫ z, Φ1 S z ∂D ∂μ = ∫ p, Φ1 p.1 p.2 ∂N := (integral_prod _ hN1).symm
  have hR2' : ∫ S, ∫ z, Φ2 i S z ∂D ∂μ = ∫ p, Φ2 i p.1 p.2 ∂N := (integral_prod _ (hN2 i)).symm
  have hunit : μ Set.univ = 1 := measure_univ
  -- the diagonal terms for Φ1
  have hdiag1 : ∀ j, ∫ S, Φ1 S (S j) ∂μ = ∫ p, Φ1 (Function.update p.1 i p.2) p.2 ∂N := by
    intro j
    rw [b2_key D j Φ1 h1m M h1B]
    have hperm := b2_perm_prod D (Equiv.swap i j)
      (fun p : (Fin (n + 1) → Z) × Z => Φ1 (Function.update p.1 i p.2) p.2)
      (h1m.comp (hupdm i)) M (fun p => h1B _ _)
    rw [← hperm]
    congr 1
    funext p
    simp only []
    have hu : Function.update (p.1 ∘ ⇑(Equiv.swap i j)) i p.2
        = (Function.update p.1 j p.2) ∘ ⇑(Equiv.swap i j) := by
      have := Function.update_comp_equiv p.1 (Equiv.swap i j) j p.2
      rw [this]
      simp [Equiv.swap_apply_right]
    rw [hu, s1]
  have hdiag2 : ∀ j, ∫ S, Φ2 j S (S j) ∂μ = ∫ p, Φ2 i p.1 p.2 ∂N := by
    intro j
    rw [b2_key D j (Φ2 j) (h2m j) M (h2B j)]
    simp_rw [s3]
    have hperm := b2_perm_prod D (Equiv.swap i j)
      (fun p : (Fin (n + 1) → Z) × Z => Φ2 i p.1 p.2) (h2m i) M (fun p => h2B _ _ _)
    rw [← hperm]
    congr 1
    funext p
    simp only []
    rw [s2]
    simp
  have hav1 : Integrable (fun S => ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) * ∑ j, Φ1 S (S j)) μ :=
    (integrable_finset_sum _ fun j _ => hD1 j).const_mul _
  have hav2 : Integrable (fun S => ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) * ∑ j, Φ2 j S (S j)) μ :=
    (integrable_finset_sum _ fun j _ => hD2 j).const_mul _
  have ha1 := b2_avg μ (fun j S => Φ1 S (S j)) hD1 _ hdiag1 hunit
  have ha2 := b2_avg μ (fun j S => Φ2 j S (S j)) hD2 _ hdiag2 hunit
  refine ⟨?_, ?_, ?_⟩
  · rw [integral_sub hR1 hav1, hR1', ha1, integral_sub hN1 (hU1 i)]
  · rw [integral_sub hR2 hav2, hR2', ha2, sub_self]
  · rw [integral_sub hR1 hav2, hR1', ha2, integral_sub hN1 (hN2 i)]

theorem solution {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable
      (fun p : (Fin n → X × Y) × (X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2))
    (hbdd : ∃ M : ℝ, ∀ (T : Multiset (X × Y)) (z : X × Y), |Loss L (A T) z| ≤ M)
    (m : ℕ) (i : Fin m) :
    (∫ S, (GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - EmpiricalError L S (A (StabGen.Hypothesis.trainingSet S)))
        ∂(Measure.pi fun _ : Fin m => D)
      = ∫ p : (Fin m → X × Y) × (X × Y),
          (Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2 - Loss L (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt p.1 i p.2))) p.2)
          ∂((Measure.pi fun _ : Fin m => D).prod D)) ∧
    (∫ S, (GeneralizationError D L (A (StabGen.Hypothesis.removeAt S i)) - StabGen.Hypothesis.looError L A S)
        ∂(Measure.pi fun _ : Fin m => D) = 0) ∧
    (∫ S, (GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - StabGen.Hypothesis.looError L A S)
        ∂(Measure.pi fun _ : Fin m => D)
      = ∫ p : (Fin m → X × Y) × (X × Y),
          (Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2 - Loss L (A (StabGen.Hypothesis.removeAt p.1 i)) p.2)
          ∂((Measure.pi fun _ : Fin m => D).prod D)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := Nat.exists_eq_succ_of_ne_zero (by rintro rfl; exact i.elim0)
  obtain ⟨M, hM⟩ := hbdd
  have h1m : Measurable (Function.uncurry
      (fun (S : Fin (n + 1) → X × Y) (z : X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet S)) z)) :=
    hA (n + 1)
  have h2m : ∀ j : Fin (n + 1), Measurable (Function.uncurry
      (fun (S : Fin (n + 1) → X × Y) (z : X × Y) => Loss L (A (StabGen.Hypothesis.removeAt S j)) z)) := by
    intro j
    have hm : Measurable (fun p : (Fin (n + 1) → X × Y) × (X × Y) =>
        ((fun k : Fin n => p.1 (j.succAbove k)), p.2)) :=
      (measurable_pi_lambda _ fun k => (measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd
    have := (hA n).comp hm
    convert this using 1
    funext p
    simp [Function.uncurry, b2_removeAt_eq]
  have key := b2_abstract D
    (fun (S : Fin (n + 1) → X × Y) (z : X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet S)) z)
    (fun (j : Fin (n + 1)) (S : Fin (n + 1) → X × Y) (z : X × Y) => Loss L (A (StabGen.Hypothesis.removeAt S j)) z)
    M h1m h2m (fun S z => hM _ _) (fun j S z => hM _ _)
    (fun S z σ => by simp only [b2_training_perm])
    (fun S z σ i => by simp only [b2_removeAt_perm])
    (fun S z j w => by simp only [b2_removeAt_update]) i
  exact key

end
