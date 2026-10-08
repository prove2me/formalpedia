-- Prove2me | solution 1 for RadGauss.Discrepancy.rademacher_ge_expect_condSup
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:36:48.720983+00:00
-- url     : https://prove2.me/submissions/89fc78b8-53f1-4aff-b76d-804c0796731e

import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_Discrepancy_maxDiscrepancy
import Definitions.Def_RadGauss_Discrepancy_condSup

open MeasureTheory
open scoped ENNReal Pointwise


namespace RadGauss.Discrepancy

open RadGauss.RiskBound

noncomputable def rgS {X : Type*} {n : ℕ} (σ : Fin n → Bool) (f : X → ℝ) (x : Fin n → X) : ℝ :=
  ∑ i, signVal (σ i) * f (x i)

noncomputable def rgPhi {X : Type*} {n : ℕ} (F : Set (X → ℝ)) (σ : Fin n → Bool)
    (x : Fin n → X) : ℝ :=
  ⨆ f : F, rgS σ (f : X → ℝ) x

noncomputable def rgG {X : Type*} [MeasurableSpace X] (μ : Measure X) (n : ℕ)
    (F : Set (X → ℝ)) (σ : Fin n → Bool) : ℝ :=
  ∫ x, rgPhi F σ x ∂(Measure.pi fun _ : Fin n => μ)

lemma rg_signVal_abs (b : Bool) : |signVal b| = 1 := by cases b <;> simp [signVal]
lemma rg_signVal_not (b : Bool) : signVal (!b) = - signVal b := by cases b <;> simp [signVal]
lemma rg_signVal_sq (b : Bool) : signVal b ^ 2 = 1 := by cases b <;> simp [signVal]

lemma rgS_abs_le {X : Type*} {n : ℕ} (σ : Fin n → Bool) (f : X → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (-1:ℝ) 1) (x : Fin n → X) : |rgS σ f x| ≤ n := by
  unfold rgS
  calc |∑ i, signVal (σ i) * f (x i)| ≤ ∑ i, |signVal (σ i) * f (x i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, (1:ℝ) := by
        apply Finset.sum_le_sum; intro i _
        rw [abs_mul, rg_signVal_abs, one_mul, abs_le]; exact hf _
    _ = n := by simp

lemma rgS_bdd {X : Type*} {n : ℕ} (F : Set (X → ℝ))
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) (σ : Fin n → Bool) (x : Fin n → X) :
    BddAbove (Set.range fun f : F => rgS σ (f : X → ℝ) x) := by
  refine ⟨n, ?_⟩; rintro _ ⟨f, rfl⟩; exact (abs_le.1 (rgS_abs_le σ f (hFrange f f.2) x)).2

lemma le_rgPhi {X : Type*} {n : ℕ} (F : Set (X → ℝ))
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) (σ : Fin n → Bool) (x : Fin n → X)
    (f : X → ℝ) (hf : f ∈ F) : rgS σ f x ≤ rgPhi F σ x :=
  le_ciSup (f := fun f : F => rgS σ (f : X → ℝ) x) (rgS_bdd F hFrange σ x) ⟨f, hf⟩

lemma rgPhi_le {X : Type*} {n : ℕ} (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) (σ : Fin n → Bool) (x : Fin n → X) :
    rgPhi F σ x ≤ n := by
  haveI : Nonempty F := hFne.to_subtype
  exact ciSup_le fun f => (abs_le.1 (rgS_abs_le σ f (hFrange f f.2) x)).2

lemma rgPhi_abs_le {X : Type*} {n : ℕ} (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) (σ : Fin n → Bool) (x : Fin n → X) :
    |rgPhi F σ x| ≤ n := by
  obtain ⟨f, hf⟩ := hFne
  rw [abs_le]; refine ⟨?_, rgPhi_le F ⟨f, hf⟩ hFrange σ x⟩
  exact (abs_le.1 (rgS_abs_le σ f (hFrange f hf) x)).1.trans (le_rgPhi F hFrange σ x f hf)

lemma rgPhi_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {n : ℕ} (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) (σ : Fin n → Bool)
    (hm : Measurable (rgPhi F σ)) :
    Integrable (rgPhi F σ) (Measure.pi fun _ : Fin n => μ) :=
  Integrable.of_bound hm.aestronglyMeasurable n
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact rgPhi_abs_le F hFne hFrange σ x)

lemma rgPhi_comp_perm {X : Type*} {n : ℕ} (F : Set (X → ℝ)) (σ : Fin n → Bool)
    (e : Equiv.Perm (Fin n)) (x : Fin n → X) :
    rgPhi F σ (fun i => x (e.symm i)) = rgPhi F (fun i => σ (e i)) x := by
  unfold rgPhi rgS
  congr 1; ext f
  rw [← Equiv.sum_comp e]
  simp

lemma rgG_perm {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {n : ℕ} (F : Set (X → ℝ)) (σ : Fin n → Bool) (e : Equiv.Perm (Fin n)) :
    rgG μ n F (fun i => σ (e i)) = rgG μ n F σ := by
  unfold rgG
  have hmp := measurePreserving_piCongrLeft (fun _ : Fin n => μ) e
  have := hmp.integral_comp' (rgPhi F σ)
  rw [← this]
  congr 1; ext x
  rw [← rgPhi_comp_perm]
  congr 1
  ext i
  have := MeasurableEquiv.piCongrLeft_apply_apply e (β := fun _ => X) x (e.symm i)
  simpa using this.symm

lemma sumSign_eq_card {n : ℕ} (σ : Fin n → Bool) :
    sumSign σ = 2 * ((Finset.univ.filter fun i => σ i = true).card : ℤ) - n := by
  unfold sumSign
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, mul_one, mul_neg, nsmul_eq_mul]
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin n => σ i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  push_cast
  omega

lemma sumSign_real {n : ℕ} (σ : Fin n → Bool) :
    ((sumSign σ : ℤ) : ℝ) = ∑ i, signVal (σ i) := by
  unfold sumSign; push_cast
  apply Finset.sum_congr rfl; intro i _
  cases σ i <;> simp [signVal]

lemma exists_perm_of_sumSign_eq {n : ℕ} (σ τ : Fin n → Bool) (h : sumSign σ = sumSign τ) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, σ (e i) = τ i := by
  have hc : (Finset.univ.filter fun i => σ i = true).card =
      (Finset.univ.filter fun i => τ i = true).card := by
    rw [sumSign_eq_card, sumSign_eq_card] at h; omega
  have h1 : Fintype.card {i // τ i = true} = Fintype.card {i // σ i = true} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]; exact hc.symm
  have h2 : Fintype.card {i // ¬ τ i = true} = Fintype.card {i // ¬ σ i = true} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  refine ⟨Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2), fun i => ?_⟩
  by_cases hi : τ i = true
  · simp only [Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply]
    rw [Equiv.sumCompl_symm_apply_of_pos (p := fun x => τ x = true) hi]
    simp only [Sum.map_inl, Equiv.sumCompl_apply_inl]
    rw [hi]; exact (Fintype.equivOfCardEq h1 ⟨i, hi⟩).2
  · simp only [Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply]
    rw [Equiv.sumCompl_symm_apply_of_neg (p := fun x => τ x = true) hi]
    simp only [Sum.map_inr, Equiv.sumCompl_apply_inr]
    have := (Fintype.equivOfCardEq h2 ⟨i, hi⟩).2
    simp only [Bool.not_eq_true] at this hi
    rw [this, hi]

lemma condSup_eq_rgG {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (F : Set (X → ℝ)) (σ : Fin n → Bool) :
    condSup μ n F (sumSign σ) = (2 / (n:ℝ)) * rgG μ n F σ := by
  unfold condSup
  congr 1
  have hsum : ∀ τ ∈ Finset.univ.filter (fun τ : Fin n → Bool => sumSign τ = sumSign σ),
      ∫ x, (⨆ f : F, ∑ i, signVal (τ i) * (f : X → ℝ) (x i)) ∂(Measure.pi fun _ : Fin n => μ)
        = rgG μ n F σ := by
    intro τ hτ
    rw [Finset.mem_filter] at hτ
    obtain ⟨e, he⟩ := exists_perm_of_sumSign_eq σ τ hτ.2.symm
    rw [← rgG_perm μ F σ e]
    have : (fun i => σ (e i)) = τ := funext he
    rw [this]; rfl
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, nsmul_eq_mul]
  have hne : ((Finset.univ.filter fun τ : Fin n → Bool => sumSign τ = sumSign σ).card : ℝ) ≠ 0 := by
    norm_cast; exact Finset.card_ne_zero.2 ⟨σ, by simp⟩
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

lemma rgPhi_sub_le {X : Type*} {n : ℕ} (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) (σ τ : Fin n → Bool) (x : Fin n → X) :
    rgPhi F σ x - rgPhi F τ x ≤ ∑ i, |signVal (σ i) - signVal (τ i)| := by
  haveI : Nonempty F := hFne.to_subtype
  rw [sub_le_iff_le_add]
  apply ciSup_le; intro f
  have h1 := le_rgPhi F hFrange τ x f f.2
  have h2 : rgS σ f x - rgS τ f x ≤ ∑ i, |signVal (σ i) - signVal (τ i)| := by
    unfold rgS; rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum; intro i _
    rw [← sub_mul]
    calc (signVal (σ i) - signVal (τ i)) * (f : X → ℝ) (x i)
        ≤ |(signVal (σ i) - signVal (τ i)) * (f : X → ℝ) (x i)| := le_abs_self _
     _ = |signVal (σ i) - signVal (τ i)| * |(f : X → ℝ) (x i)| := abs_mul _ _
     _ ≤ |signVal (σ i) - signVal (τ i)| * 1 := by
        gcongr; exact abs_le.2 (hFrange f f.2 _)
     _ = _ := mul_one _
  linarith

lemma rgG_sub_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {n : ℕ} (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) (σ τ : Fin n → Bool)
    (hσ : Measurable (rgPhi F σ)) (hτ : Measurable (rgPhi F τ)) :
    rgG μ n F σ - rgG μ n F τ ≤ ∑ i, |signVal (σ i) - signVal (τ i)| := by
  unfold rgG
  rw [← integral_sub (rgPhi_integrable μ F hFne hFrange σ hσ)
    (rgPhi_integrable μ F hFne hFrange τ hτ)]
  calc ∫ x, (rgPhi F σ x - rgPhi F τ x) ∂(Measure.pi fun _ : Fin n => μ)
      ≤ ∫ x, (∑ i, |signVal (σ i) - signVal (τ i)|) ∂(Measure.pi fun _ : Fin n => μ) :=
        integral_mono ((rgPhi_integrable μ F hFne hFrange σ hσ).sub
          (rgPhi_integrable μ F hFne hFrange τ hτ)) (integrable_const _)
          (fun x => rgPhi_sub_le F hFne hFrange σ τ x)
    _ = _ := by simp

def rgCanon (n k : ℕ) : Fin n → Bool := fun i => decide (i.val < k)

lemma rgCanon_card (n k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter fun i => rgCanon n k i = true).card = k := by
  simp only [rgCanon, decide_eq_true_eq]
  rw [Fin.card_filter_val_lt]; omega

lemma rgCanon_sumSign {n : ℕ} (σ : Fin n → Bool) :
    sumSign (rgCanon n (Finset.univ.filter fun i => σ i = true).card) = sumSign σ := by
  rw [sumSign_eq_card, sumSign_eq_card, rgCanon_card]
  exact (Finset.card_le_univ _).trans (by simp)

lemma rgCanon_sum_abs {n k₁ k₂ : ℕ} (h : k₂ ≤ k₁) :
    ∑ i, |signVal (rgCanon n k₁ i) - signVal (rgCanon n k₂ i)|
      = ((sumSign (rgCanon n k₁) : ℤ) : ℝ) - ((sumSign (rgCanon n k₂) : ℤ) : ℝ) := by
  rw [sumSign_real, sumSign_real, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply abs_of_nonneg
  unfold rgCanon
  by_cases h1 : i.val < k₂
  · have : i.val < k₁ := by omega
    simp [h1, this, signVal]
  · by_cases h2 : i.val < k₁ <;> simp [h1, h2, signVal]

lemma condSup_lip_core {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {n : ℕ} (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hsup : ∀ σ : Fin n → Bool, Measurable (rgPhi F σ)) (σ₁ σ₂ : Fin n → Bool) :
    |condSup μ n F (sumSign σ₁) - condSup μ n F (sumSign σ₂)|
      ≤ (2 / (n:ℝ)) * |((sumSign σ₁ : ℤ) : ℝ) - ((sumSign σ₂ : ℤ) : ℝ)| := by
  rw [← rgCanon_sumSign σ₁, ← rgCanon_sumSign σ₂]
  set k₁ := (Finset.univ.filter fun i => σ₁ i = true).card
  set k₂ := (Finset.univ.filter fun i => σ₂ i = true).card
  rw [condSup_eq_rgG, condSup_eq_rgG, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hab : ∀ a b : ℕ, b ≤ a → |rgG μ n F (rgCanon n a) - rgG μ n F (rgCanon n b)|
      ≤ |((sumSign (rgCanon n a) : ℤ) : ℝ) - ((sumSign (rgCanon n b) : ℤ) : ℝ)| := by
    intro a b hba
    have e1 := rgG_sub_le μ F hFne hFrange (rgCanon n a) (rgCanon n b) (hsup _) (hsup _)
    have e2 := rgG_sub_le μ F hFne hFrange (rgCanon n b) (rgCanon n a) (hsup _) (hsup _)
    rw [rgCanon_sum_abs hba] at e1
    have e3 : ∑ i, |signVal (rgCanon n b i) - signVal (rgCanon n a i)|
        = ∑ i, |signVal (rgCanon n a i) - signVal (rgCanon n b i)| := by
      apply Finset.sum_congr rfl; intro i _; exact abs_sub_comm _ _
    rw [e3, rgCanon_sum_abs hba] at e2
    rw [abs_le]; constructor
    · have := le_abs_self (((sumSign (rgCanon n a) : ℤ) : ℝ) - ((sumSign (rgCanon n b) : ℤ) : ℝ))
      linarith
    · have := le_abs_self (((sumSign (rgCanon n a) : ℤ) : ℝ) - ((sumSign (rgCanon n b) : ℤ) : ℝ))
      linarith
  rcases le_total k₂ k₁ with h | h
  · exact hab _ _ h
  · rw [abs_sub_comm, abs_sub_comm ((sumSign (rgCanon n k₁) : ℤ) : ℝ)]; exact hab _ _ h

lemma rg_sum_signVal_mul_eq_zero {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ∑ σ : Fin n → Bool, signVal (σ i) * signVal (σ j) = 0 := by
  let e : Equiv.Perm (Fin n → Bool) :=
    Function.Involutive.toPerm (fun σ => Function.update σ i (!σ i)) (by
      intro σ; ext k; by_cases hk : k = i
      · subst hk; simp
      · simp [Function.update_of_ne hk])
  have h := Equiv.sum_comp e (fun σ => signVal (σ i) * signVal (σ j))
  have h2 : ∀ σ : Fin n → Bool, signVal (e σ i) * signVal (e σ j)
      = -(signVal (σ i) * signVal (σ j)) := by
    intro σ
    show signVal (Function.update σ i (!σ i) i) * signVal (Function.update σ i (!σ i) j) = _
    rw [Function.update_self, Function.update_of_ne hij.symm, rg_signVal_not]
    ring
  simp only [h2, Finset.sum_neg_distrib] at h
  linarith

lemma rg_sum_sq_signSum {n : ℕ} (c : Fin n → ℝ) :
    ∑ σ : Fin n → Bool, (∑ i, signVal (σ i) * c i) ^ 2 = 2 ^ n * ∑ i, c i ^ 2 := by
  have : ∀ σ : Fin n → Bool, (∑ i, signVal (σ i) * c i) ^ 2
      = ∑ i, ∑ j, (signVal (σ i) * signVal (σ j)) * (c i * c j) := by
    intro σ; rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  simp_rw [this]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single i]
  · simp_rw [← Finset.sum_mul, ← sq, rg_signVal_sq]
    simp
  · intro j _ hj
    rw [← Finset.sum_mul, rg_sum_signVal_mul_eq_zero i j (Ne.symm hj), zero_mul]
  · simp

lemma rg_avg_abs_signSum_le {n : ℕ} (c : Fin n → ℝ) :
    ((2:ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, |∑ i, signVal (σ i) * c i|
      ≤ Real.sqrt (∑ i, c i ^ 2) := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n → Bool)))
    (f := fun σ => |∑ i, signVal (σ i) * c i|)
  simp only [sq_abs, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at h
  rw [rg_sum_sq_signSum] at h
  apply Real.le_sqrt_of_sq_le
  have hp : (0:ℝ) < 2 ^ n := by positivity
  rw [mul_pow, inv_pow, inv_mul_le_iff₀ (by positivity)]
  push_cast at h
  nlinarith

lemma rg_ofReal_integral_le {α : Type*} [MeasurableSpace α] {ν : Measure α} {h : α → ℝ}
    (hi : Integrable h ν) :
    ENNReal.ofReal (∫ x, h x ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (h x) ∂ν := by
  calc ENNReal.ofReal (∫ x, h x ∂ν) ≤ ENNReal.ofReal (∫ x, max (h x) 0 ∂ν) :=
        ENNReal.ofReal_le_ofReal (integral_mono hi hi.pos_part (fun x => le_max_left _ _))
    _ = ∫⁻ x, ENNReal.ofReal (max (h x) 0) ∂ν :=
        ofReal_integral_eq_lintegral_ofReal hi.pos_part
          (Filter.Eventually.of_forall fun x => le_max_right _ _)
    _ = _ := by
        congr 1; ext x
        rcases le_total (h x) 0 with hx | hx
        · rw [max_eq_right hx, ENNReal.ofReal_of_nonpos hx, ENNReal.ofReal_zero]
        · rw [max_eq_left hx]

lemma rg_ofReal_sum_le {ι : Type*} (s : Finset ι) (b : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, b i) ≤ ∑ i ∈ s, ENNReal.ofReal (b i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha]
  exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

lemma rg_ofReal_phi_le {X : Type*} {n : ℕ} (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) (σ : Fin n → Bool) (x : Fin n → X) :
    ENNReal.ofReal ((2 / (n:ℝ)) * rgPhi F σ x)
      ≤ ⨆ g ∈ F, ENNReal.ofReal |(2 / (n:ℝ)) * ∑ i, signVal (σ i) * g (x i)| := by
  haveI : Nonempty F := hFne.to_subtype
  have hmono : Monotone (fun t : ℝ => ENNReal.ofReal ((2 / (n:ℝ)) * t)) := fun a b hab =>
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hab (by positivity))
  have hcont : Continuous (fun t : ℝ => ENNReal.ofReal ((2 / (n:ℝ)) * t)) :=
    ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
  have key := hmono.map_ciSup_of_continuousAt hcont.continuousAt (rgS_bdd F hFrange σ x)
  unfold rgPhi
  rw [key]
  apply iSup_le; intro f
  refine le_trans ?_ (le_iSup₂ (f := fun g (_ : g ∈ F) =>
    ENNReal.ofReal |(2 / (n:ℝ)) * ∑ i, signVal (σ i) * g (x i)|) f.1 f.2)
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

lemma rg_avg_condSup_eq_integral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hsup : ∀ σ : Fin n → Bool, Measurable (rgPhi F σ)) :
    ((2:ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, condSup μ n F (sumSign σ)
      = ∫ x, ((2:ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, (2 / (n:ℝ)) * rgPhi F σ x
          ∂(Measure.pi fun _ : Fin n => μ) := by
  rw [integral_const_mul, integral_finsetSum _
    (fun σ _ => (rgPhi_integrable μ F hFne hFrange σ (hsup σ)).const_mul _)]
  congr 1; apply Finset.sum_congr rfl; intro σ _
  rw [condSup_eq_rgG, integral_const_mul]; rfl

lemma rg_avg_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hsup : ∀ σ : Fin n → Bool, Measurable (rgPhi F σ)) :
    Integrable (fun x => ((2:ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, (2 / (n:ℝ)) * rgPhi F σ x)
      (Measure.pi fun _ : Fin n => μ) :=
  (integrable_finsetSum _
    (fun σ _ => (rgPhi_integrable μ F hFne hFrange σ (hsup σ)).const_mul _)).const_mul _

lemma rg_ofReal_two_pow_inv (n : ℕ) : ENNReal.ofReal (((2:ℝ) ^ n)⁻¹) = ((2:ℝ≥0∞) ^ n)⁻¹ := by
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp

lemma rgS_neg {X : Type*} {n : ℕ} (σ : Fin n → Bool) (f : X → ℝ) (x : Fin n → X) :
    rgS σ (-f) x = rgS (fun i => !σ i) f x := by
  unfold rgS; apply Finset.sum_congr rfl; intro i _
  rw [rg_signVal_not]; simp

lemma rgS_neg' {X : Type*} {n : ℕ} (σ : Fin n → Bool) (f : X → ℝ) (x : Fin n → X) :
    rgS σ (-f) x = - rgS σ f x := by
  unfold rgS; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _
  simp

theorem rademacher_ge_core {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hsup : ∀ σ : Fin n → Bool, Measurable (rgPhi F σ)) :
    ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, condSup μ n F (sumSign σ))
        ≤ RadGauss.RiskBound.rademacherComplexity μ n F ∧
      ((∀ f ∈ F, -f ∈ F) →
        RadGauss.RiskBound.rademacherComplexity μ n F =
          ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, condSup μ n F (sumSign σ))) := by
  have hint := rg_avg_integrable μ n F hFne hFrange hsup
  rw [rg_avg_condSup_eq_integral μ n F hFne hFrange hsup]
  constructor
  · refine (rg_ofReal_integral_le hint).trans (lintegral_mono fun x => ?_)
    unfold empiricalRademacher
    rw [ENNReal.ofReal_mul (by positivity), rg_ofReal_two_pow_inv]
    gcongr
    exact (rg_ofReal_sum_le _ _).trans
      (Finset.sum_le_sum fun σ _ => rg_ofReal_phi_le F hFne hFrange σ x)
  · intro hneg
    have hnn : ∀ (σ : Fin n → Bool) (x : Fin n → X), 0 ≤ rgPhi F σ x := by
      intro σ x; obtain ⟨f, hf⟩ := hFne
      have h1 := le_rgPhi F hFrange σ x f hf
      have h2 := le_rgPhi F hFrange σ x (-f) (hneg f hf)
      rw [rgS_neg'] at h2
      linarith
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => by
      have := fun σ => hnn σ x
      dsimp only [Pi.zero_apply]
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg fun σ _ => mul_nonneg (by positivity) (hnn σ x))]
    unfold rademacherComplexity
    apply lintegral_congr; intro x
    unfold empiricalRademacher
    rw [ENNReal.ofReal_mul (by positivity), rg_ofReal_two_pow_inv,
      ENNReal.ofReal_sum_of_nonneg (fun σ _ => mul_nonneg (by positivity) (hnn σ x))]
    congr 1; apply Finset.sum_congr rfl; intro σ _
    apply le_antisymm
    · apply iSup₂_le; intro g hg
      apply ENNReal.ofReal_le_ofReal
      have h1 := le_rgPhi F hFrange σ x g hg
      have h2 := le_rgPhi F hFrange σ x (-g) (hneg g hg)
      rw [rgS_neg'] at h2
      have hc : (0:ℝ) ≤ 2 / (n:ℝ) := by positivity
      change |(2 / (n:ℝ)) * rgS σ g x| ≤ _
      rw [abs_le]; constructor <;> nlinarith
    · exact rg_ofReal_phi_le F hFne hFrange σ x

lemma halfDiff_eq_rgS {X : Type*} (m : ℕ) (f : X → ℝ) (x : Fin (2 * m) → X) :
    halfDiff m f x = (2 / ((2 * m : ℕ) : ℝ)) * rgS (rgCanon (2 * m) m) f x := by
  unfold halfDiff rgS rgCanon
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1; apply Finset.sum_congr rfl; intro i _
  by_cases h : i.val < m <;> simp [h, signVal]

lemma sumSign_canon_half (m : ℕ) : sumSign (rgCanon (2 * m) m) = 0 := by
  rw [sumSign_eq_card, rgCanon_card _ _ (by omega)]; push_cast; ring

lemma emd_eq_rgPhi {X : Type*} (m : ℕ) (F : Set (X → ℝ)) (x : Fin (2 * m) → X) :
    empiricalMaxDiscrepancy m F x
      = (2 / ((2 * m : ℕ) : ℝ)) * rgPhi F (rgCanon (2 * m) m) x := by
  unfold empiricalMaxDiscrepancy rgPhi
  rw [Real.mul_iSup_of_nonneg (by positivity)]
  congr 1; ext f; exact halfDiff_eq_rgS m f x

lemma emd_eq_rgG {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (m : ℕ) (F : Set (X → ℝ)) :
    expectedMaxDiscrepancy μ m F = (2 / ((2 * m : ℕ) : ℝ)) * rgG μ (2 * m) F (rgCanon (2 * m) m) := by
  unfold expectedMaxDiscrepancy rgG
  simp_rw [emd_eq_rgPhi]
  rw [integral_const_mul]

theorem discrepancy_core {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) (F : Set (X → ℝ)) :
    expectedMaxDiscrepancy μ m F = condSup μ (2 * m) F 0 := by
  rw [← sumSign_canon_half m, condSup_eq_rgG, emd_eq_rgG]

theorem condSup_lipschitz_core {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hsup : ∀ σ : Fin n → Bool, Measurable (rgPhi F σ))
    (N₁ N₂ : ℤ) (hN₁ : ∃ σ : Fin n → Bool, sumSign σ = N₁)
    (hN₂ : ∃ σ : Fin n → Bool, sumSign σ = N₂) :
    |condSup μ n F N₁ - condSup μ n F N₂| ≤ 4 * |(N₂ : ℝ) - N₁| / n := by
  obtain ⟨σ₁, rfl⟩ := hN₁
  obtain ⟨σ₂, rfl⟩ := hN₂
  refine (condSup_lip_core μ F hFne hFrange hsup σ₁ σ₂).trans ?_
  rw [abs_sub_comm]
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have ha := abs_nonneg (((sumSign σ₂ : ℤ) : ℝ) - ((sumSign σ₁ : ℤ) : ℝ))
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hn'.le
  linarith

lemma rg_sqrt_ineq (N : ℝ) (hN : 0 < N) : (2 / N) * Real.sqrt N ≤ 4 * Real.sqrt (2 / N) := by
  have hs := Real.sqrt_pos.2 hN
  have hsq := Real.sq_sqrt hN.le
  have h2 : Real.sqrt (2 / N) = Real.sqrt 2 / Real.sqrt N := Real.sqrt_div' 2 hN.le
  have ht : 1 ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  rw [h2]
  rw [show (2 / N) * Real.sqrt N = 2 / Real.sqrt N by
    rw [eq_div_iff hs.ne', mul_assoc, Real.mul_self_sqrt hN.le, div_mul_cancel₀ _ hN.ne']]
  rw [mul_div_assoc']
  apply div_le_div_of_nonneg_right _ hs.le
  linarith

theorem deviation_core {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hsup : ∀ σ : Fin (2 * m) → Bool, Measurable (rgPhi F σ)) :
    |((2 : ℝ) ^ (2 * m))⁻¹ * ∑ σ : Fin (2 * m) → Bool, condSup μ (2 * m) F (sumSign σ)
        - condSup μ (2 * m) F 0|
      ≤ ((2 : ℝ) ^ (2 * m))⁻¹ * ∑ σ : Fin (2 * m) → Bool,
          |condSup μ (2 * m) F (sumSign σ) - condSup μ (2 * m) F 0| ∧
    ((2 : ℝ) ^ (2 * m))⁻¹ * ∑ σ : Fin (2 * m) → Bool,
          |condSup μ (2 * m) F (sumSign σ) - condSup μ (2 * m) F 0|
      ≤ (2 / ((2 * m : ℕ) : ℝ)) * Real.sqrt ((2 * m : ℕ) : ℝ) := by
  have hp : (0:ℝ) < (2:ℝ) ^ (2 * m) := by positivity
  constructor
  · have : ((2 : ℝ) ^ (2 * m))⁻¹ * ∑ σ : Fin (2 * m) → Bool, condSup μ (2 * m) F (sumSign σ)
        - condSup μ (2 * m) F 0 = ((2 : ℝ) ^ (2 * m))⁻¹ * ∑ σ : Fin (2 * m) → Bool,
          (condSup μ (2 * m) F (sumSign σ) - condSup μ (2 * m) F 0) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, mul_sub]
      push_cast
      rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
    rw [this, abs_mul, abs_of_pos (inv_pos.2 hp)]
    gcongr
    exact Finset.abs_sum_le_sum_abs _ _
  · have hl : ∀ σ : Fin (2 * m) → Bool,
        |condSup μ (2 * m) F (sumSign σ) - condSup μ (2 * m) F 0|
          ≤ (2 / ((2 * m : ℕ) : ℝ)) * |∑ i, signVal (σ i) * 1| := by
      intro σ
      have h := condSup_lip_core μ F hFne hFrange hsup σ (rgCanon (2 * m) m)
      rw [sumSign_canon_half] at h
      simpa [sumSign_real] using h
    calc ((2 : ℝ) ^ (2 * m))⁻¹ * ∑ σ : Fin (2 * m) → Bool,
          |condSup μ (2 * m) F (sumSign σ) - condSup μ (2 * m) F 0|
        ≤ ((2 : ℝ) ^ (2 * m))⁻¹ * ∑ σ : Fin (2 * m) → Bool,
          (2 / ((2 * m : ℕ) : ℝ)) * |∑ i, signVal (σ i) * 1| := by
          gcongr with σ; exact hl σ
      _ = (2 / ((2 * m : ℕ) : ℝ)) * (((2 : ℝ) ^ (2 * m))⁻¹ * ∑ σ : Fin (2 * m) → Bool,
          |∑ i, signVal (σ i) * (fun _ => (1:ℝ)) i|) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ (2 / ((2 * m : ℕ) : ℝ)) * Real.sqrt (∑ i : Fin (2 * m), (fun _ => (1:ℝ)) i ^ 2) := by
          gcongr; exact rg_avg_abs_signSum_le _
      _ = _ := by simp

end RadGauss.Discrepancy

open RadGauss.Discrepancy


theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin n → Bool,
      Measurable fun x : Fin n → X => ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i)) :
    ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, condSup μ n F (sumSign σ))
        ≤ RadGauss.RiskBound.rademacherComplexity μ n F ∧
      ((∀ f ∈ F, -f ∈ F) →
        RadGauss.RiskBound.rademacherComplexity μ n F =
          ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, condSup μ n F (sumSign σ))) := by
  exact rademacher_ge_core μ n F hFne hFrange hsup
