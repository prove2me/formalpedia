-- Prove2me | solution 1 for RadGauss.Discrepancy.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:41:29.508289+00:00
-- url     : https://prove2.me/submissions/1872125e-8b7e-4d71-a23c-e333e7dc6aa3

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

lemma rg_union_range {X : Type*} (F : Set (X → ℝ))
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
    ∀ g ∈ F ∪ -F, ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1 := by
  intro g hg x
  rcases hg with hg | hg
  · exact hFrange g hg x
  · have := hFrange (-g) hg x
    simp only [Pi.neg_apply, Set.mem_Icc] at this ⊢
    constructor <;> linarith [this.1, this.2]

lemma rg_union_closed {X : Type*} (F : Set (X → ℝ)) : ∀ g ∈ F ∪ -F, -g ∈ F ∪ -F := by
  intro g hg; rcases hg with hg | hg
  · right; rw [Set.mem_neg, neg_neg]; exact hg
  · left; exact hg

lemma rgPhi_union {X : Type*} {n : ℕ} (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) (σ : Fin n → Bool) (x : Fin n → X) :
    rgPhi (F ∪ -F) σ x = max (rgPhi F σ x) (rgPhi F (fun i => !σ i) x) := by
  have hU := rg_union_range F hFrange
  haveI : Nonempty (F ∪ -F : Set (X → ℝ)) := (hFne.mono Set.subset_union_left).to_subtype
  haveI : Nonempty F := hFne.to_subtype
  apply le_antisymm
  · apply ciSup_le; rintro ⟨g, hg⟩
    rcases hg with hg | hg
    · exact (le_rgPhi F hFrange σ x g hg).trans (le_max_left _ _)
    · have : rgS σ g x = rgS (fun i => !σ i) (-g) x := by
        rw [rgS_neg]; simp
      show rgS σ g x ≤ _
      rw [this]; exact (le_rgPhi F hFrange _ x (-g) hg).trans (le_max_right _ _)
  · apply max_le
    · apply ciSup_le; intro f; exact le_rgPhi (F ∪ -F) hU σ x f (Or.inl f.2)
    · apply ciSup_le; intro f
      show rgS (fun i => !σ i) (f : X → ℝ) x ≤ _
      rw [← rgS_neg]
      exact le_rgPhi (F ∪ -F) hU σ x (-(f : X → ℝ)) (Or.inr (by rw [Set.mem_neg, neg_neg]; exact f.2))

lemma rg_hsup_union {X : Type*} {n : ℕ} (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) [MeasurableSpace X]
    (hsup : ∀ σ : Fin n → Bool, Measurable (rgPhi F σ)) :
    ∀ σ : Fin n → Bool, Measurable (rgPhi (F ∪ -F) σ) := by
  intro σ
  have : rgPhi (F ∪ -F) σ = fun x => max (rgPhi F σ x) (rgPhi F (fun i => !σ i) x) :=
    funext (rgPhi_union F hFne hFrange σ)
  rw [this]; exact (hsup σ).max (hsup _)

lemma rademacher_union_eq {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (F : Set (X → ℝ)) :
    rademacherComplexity μ n F = rademacherComplexity μ n (F ∪ -F) := by
  unfold rademacherComplexity
  apply lintegral_congr; intro x
  unfold empiricalRademacher
  congr 1; apply Finset.sum_congr rfl; intro σ _
  apply le_antisymm
  · exact iSup₂_mono' fun g hg => ⟨g, Or.inl hg, le_rfl⟩
  · apply iSup₂_le; intro g hg
    rcases hg with hg | hg
    · exact le_iSup₂ (f := fun g (_ : g ∈ F) =>
        ENNReal.ofReal |(2 / (n:ℝ)) * ∑ i, signVal (σ i) * g (x i)|) g hg
    · refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun g (_ : g ∈ F) =>
        ENNReal.ofReal |(2 / (n:ℝ)) * ∑ i, signVal (σ i) * g (x i)|) (-g) hg)
      congr 1
      simp [Finset.sum_neg_distrib, abs_neg]

theorem union_neg_core {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hsup : ∀ σ : Fin (2 * m) → Bool, Measurable (rgPhi F σ)) :
    rademacherComplexity μ (2 * m) F = rademacherComplexity μ (2 * m) (F ∪ -F) ∧
      rademacherComplexity μ (2 * m) (F ∪ -F)
        ≤ ENNReal.ofReal (expectedMaxDiscrepancy μ m (F ∪ -F))
          + ENNReal.ofReal ((2 / ((2 * m : ℕ) : ℝ)) * Real.sqrt ((2 * m : ℕ) : ℝ)) := by
  have hU := rg_union_range F hFrange
  have hUne : (F ∪ -F).Nonempty := hFne.mono Set.subset_union_left
  have hsupU := rg_hsup_union F hFne hFrange hsup
  have h1 := (rademacher_ge_core μ (2 * m) (F ∪ -F) hUne hU hsupU).2 (rg_union_closed F)
  have h4 := deviation_core μ m hm (F ∪ -F) hUne hU hsupU
  have hD := discrepancy_core μ m (F ∪ -F)
  refine ⟨rademacher_union_eq μ _ F, ?_⟩
  rw [h1, hD]
  have habs := le_abs_self (((2 : ℝ) ^ (2 * m))⁻¹ * ∑ σ : Fin (2 * m) → Bool,
    condSup μ (2 * m) (F ∪ -F) (sumSign σ) - condSup μ (2 * m) (F ∪ -F) 0)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
  linarith [h4.1, h4.2]

lemma rg_sqrt_ineq2 (m : ℕ) (hm : 0 < m) :
    (2 / ((2 * m : ℕ) : ℝ)) * Real.sqrt (4 * m) + (2 / ((2 * m : ℕ) : ℝ)) * Real.sqrt ((2 * m : ℕ) : ℝ)
      ≤ 4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ)) := by
  have hN : (0:ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * m)
  have h4m : (4 * (m:ℝ)) = 2 * ((2 * m : ℕ) : ℝ) := by push_cast; ring
  rw [h4m, Real.sqrt_mul (by norm_num)]
  have hs := Real.sqrt_pos.2 hN
  have h2 : Real.sqrt (2 / ((2 * m : ℕ) : ℝ)) = Real.sqrt 2 / Real.sqrt ((2 * m : ℕ) : ℝ) :=
    Real.sqrt_div' 2 hN.le
  have ht : 1 ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hk : (2 / ((2 * m : ℕ) : ℝ)) * Real.sqrt ((2 * m : ℕ) : ℝ) = 2 / Real.sqrt ((2 * m : ℕ) : ℝ) := by
    rw [eq_div_iff hs.ne', mul_assoc, Real.mul_self_sqrt hN.le, div_mul_cancel₀ _ hN.ne']
  rw [h2, show (2 / ((2 * m : ℕ) : ℝ)) * (Real.sqrt 2 * Real.sqrt ((2 * m : ℕ) : ℝ))
      = Real.sqrt 2 * ((2 / ((2 * m : ℕ) : ℝ)) * Real.sqrt ((2 * m : ℕ) : ℝ)) by ring, hk]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hi := inv_pos.2 hs
  nlinarith

lemma rg_integral_perm {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {n : ℕ} (h : (Fin n → X) → ℝ) (e : Equiv.Perm (Fin n)) :
    ∫ x, h (fun i => x (e.symm i)) ∂(Measure.pi fun _ : Fin n => μ)
      = ∫ x, h x ∂(Measure.pi fun _ : Fin n => μ) := by
  have hmp := measurePreserving_piCongrLeft (fun _ : Fin n => μ) e
  rw [← hmp.integral_comp' h]
  congr 1; ext x; congr 1; ext i
  have := MeasurableEquiv.piCongrLeft_apply_apply e (β := fun _ => X) x (e.symm i)
  simpa using this.symm

lemma rgS_comp_perm {X : Type*} {n : ℕ} (σ : Fin n → Bool) (f : X → ℝ)
    (e : Equiv.Perm (Fin n)) (x : Fin n → X) :
    rgS σ f (fun i => x (e.symm i)) = rgS (fun i => σ (e i)) f x := by
  unfold rgS; rw [← Equiv.sum_comp e]; simp

lemma rgS_abs_int_eq {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {n : ℕ} (f : X → ℝ) (σ τ : Fin n → Bool) (h : sumSign σ = sumSign τ) :
    ∫ x, |rgS σ f x| ∂(Measure.pi fun _ : Fin n => μ)
      = ∫ x, |rgS τ f x| ∂(Measure.pi fun _ : Fin n => μ) := by
  obtain ⟨e, he⟩ := exists_perm_of_sumSign_eq σ τ h
  have : τ = fun i => σ (e i) := funext fun i => (he i).symm
  rw [this, ← rg_integral_perm μ (fun x => |rgS σ f x|) e]
  congr 1; ext x; rw [rgS_comp_perm]

def rgEps (m : ℕ) (ε : Fin m → Bool) : Fin (2 * m) → Bool := fun i =>
  if h : i.val < m then ε ⟨i.val, h⟩ else !ε ⟨i.val - m, by have := i.isLt; omega⟩

lemma rgEps_lo (m : ℕ) (ε : Fin m → Bool) (j : Fin m) (hj : j.val < 2 * m) :
    rgEps m ε ⟨j.val, hj⟩ = ε j := by
  simp [rgEps, j.isLt]

lemma rgEps_hi (m : ℕ) (ε : Fin m → Bool) (j : Fin m) (hj : m + j.val < 2 * m) :
    rgEps m ε ⟨m + j.val, hj⟩ = !ε j := by
  simp [rgEps]

lemma rg_sum_split {M : Type*} [AddCommMonoid M] (m : ℕ) (h : Fin (2 * m) → M) :
    ∑ i, h i = ∑ j : Fin m, (h ⟨j.val, by have := j.isLt; omega⟩
      + h ⟨m + j.val, by have := j.isLt; omega⟩) := by
  rw [Finset.sum_add_distrib]
  have e1 : ∑ i, h i = ∑ i : Fin (m + m), h ⟨i.val, by have := i.isLt; omega⟩ :=
    Fintype.sum_equiv (finCongr (by omega)) _ _ (fun i => rfl)
  rw [e1, Fin.sum_univ_add]
  rfl

lemma rgEps_sumSign (m : ℕ) (ε : Fin m → Bool) : sumSign (rgEps m ε) = 0 := by
  have : ((sumSign (rgEps m ε) : ℤ) : ℝ) = 0 := by
    rw [sumSign_real, rg_sum_split]
    apply Finset.sum_eq_zero; intro j _
    rw [rgEps_lo, rgEps_hi, rg_signVal_not]; ring
  exact_mod_cast this

lemma rgS_eps_eq {X : Type*} (m : ℕ) (ε : Fin m → Bool) (f : X → ℝ) (x : Fin (2 * m) → X) :
    rgS (rgEps m ε) f x = ∑ j : Fin m, signVal (ε j) *
      (f (x ⟨j.val, by have := j.isLt; omega⟩) - f (x ⟨m + j.val, by have := j.isLt; omega⟩)) := by
  unfold rgS; rw [rg_sum_split]
  apply Finset.sum_congr rfl; intro j _
  rw [rgEps_lo, rgEps_hi, rg_signVal_not]; ring

lemma rg_int_abs_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (m : ℕ) (f : X → ℝ) (hf : ∀ x, f x ∈ Set.Icc (-1:ℝ) 1) (hfm : Measurable f) :
    ∫ x, |rgS (rgCanon (2 * m) m) f x| ∂(Measure.pi fun _ : Fin (2 * m) => μ)
      ≤ Real.sqrt (4 * m) := by
  have hint : ∀ σ : Fin (2 * m) → Bool,
      Integrable (fun x => |rgS σ f x|) (Measure.pi fun _ : Fin (2 * m) => μ) := by
    intro σ
    refine Integrable.of_bound ?_ ((2 * m : ℕ) : ℝ) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_abs]; exact rgS_abs_le σ f hf x)
    have : Measurable (fun x : Fin (2 * m) → X => rgS σ f x) := by
      unfold rgS
      exact Finset.measurable_sum _ fun i _ => (hfm.comp (measurable_pi_apply i)).const_mul _
    exact this.abs.aestronglyMeasurable
  have heq : ∀ ε : Fin m → Bool,
      ∫ x, |rgS (rgEps m ε) f x| ∂(Measure.pi fun _ : Fin (2 * m) => μ)
        = ∫ x, |rgS (rgCanon (2 * m) m) f x| ∂(Measure.pi fun _ : Fin (2 * m) => μ) :=
    fun ε => rgS_abs_int_eq μ f _ _ (by rw [rgEps_sumSign, sumSign_canon_half])
  have hp : (0:ℝ) < 2 ^ m := by positivity
  calc ∫ x, |rgS (rgCanon (2 * m) m) f x| ∂(Measure.pi fun _ : Fin (2 * m) => μ)
      = ((2:ℝ) ^ m)⁻¹ * ∑ ε : Fin m → Bool,
          ∫ x, |rgS (rgEps m ε) f x| ∂(Measure.pi fun _ : Fin (2 * m) => μ) := by
        simp_rw [heq]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
    _ = ∫ x, ((2:ℝ) ^ m)⁻¹ * ∑ ε : Fin m → Bool, |rgS (rgEps m ε) f x|
          ∂(Measure.pi fun _ : Fin (2 * m) => μ) := by
        rw [integral_const_mul, integral_finsetSum _ (fun ε _ => hint _)]
    _ ≤ ∫ x, Real.sqrt (4 * m) ∂(Measure.pi fun _ : Fin (2 * m) => μ) := by
        apply integral_mono ((integrable_finsetSum _ (fun ε _ => hint _)).const_mul _)
          (integrable_const _)
        intro x
        simp_rw [rgS_eps_eq]
        refine (rg_avg_abs_signSum_le _).trans (Real.sqrt_le_sqrt ?_)
        calc ∑ j : Fin m, (f (x ⟨j.val, by have := j.isLt; omega⟩)
              - f (x ⟨m + j.val, by have := j.isLt; omega⟩)) ^ 2
            ≤ ∑ j : Fin m, (4:ℝ) := by
              apply Finset.sum_le_sum; intro j _
              have ha := hf (x ⟨j.val, by have := j.isLt; omega⟩)
              have hb := hf (x ⟨m + j.val, by have := j.isLt; omega⟩)
              rw [Set.mem_Icc] at ha hb
              nlinarith [ha.1, ha.2, hb.1, hb.2]
          _ = 4 * m := by simp; ring
    _ = Real.sqrt (4 * m) := by simp

lemma rg_disc_union_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin (2 * m) → Bool, Measurable (rgPhi F σ)) :
    expectedMaxDiscrepancy μ m (F ∪ -F)
      ≤ 2 * expectedMaxDiscrepancy μ m F + (2 / ((2 * m : ℕ) : ℝ)) * Real.sqrt (4 * m) := by
  have hFne' := hFne
  obtain ⟨f0, hf0⟩ := hFne'
  have hU := rg_union_range F hFrange
  have hUne : (F ∪ -F).Nonempty := hFne.mono Set.subset_union_left
  have hsupU := rg_hsup_union F hFne hFrange hsup
  rw [emd_eq_rgG, emd_eq_rgG]
  have hneg : rgG μ (2 * m) F (fun i => !rgCanon (2 * m) m i) = rgG μ (2 * m) F (rgCanon (2 * m) m) := by
    have hs : sumSign (rgCanon (2 * m) m) = sumSign (fun i => !rgCanon (2 * m) m i) := by
      have : ((sumSign (fun i => !rgCanon (2 * m) m i) : ℤ) : ℝ)
          = - ((sumSign (rgCanon (2 * m) m) : ℤ) : ℝ) := by
        rw [sumSign_real, sumSign_real, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro i _; exact rg_signVal_not _
      rw [sumSign_canon_half] at this ⊢
      simp only [Int.cast_zero, neg_zero, Int.cast_eq_zero] at this
      exact this.symm
    obtain ⟨e, he⟩ := exists_perm_of_sumSign_eq _ _ hs
    rw [← rgG_perm μ F (rgCanon (2 * m) m) e]
    congr 1; funext i; exact (he i).symm
  have hpt : ∀ x, rgPhi (F ∪ -F) (rgCanon (2 * m) m) x
      ≤ rgPhi F (rgCanon (2 * m) m) x + rgPhi F (fun i => !rgCanon (2 * m) m i) x
        + |rgS (rgCanon (2 * m) m) f0 x| := by
    intro x
    rw [rgPhi_union F hFne hFrange]
    have h1 := le_rgPhi F hFrange (rgCanon (2 * m) m) x f0 hf0
    have h2 := le_rgPhi F hFrange (fun i => !rgCanon (2 * m) m i) x f0 hf0
    rw [← rgS_neg, rgS_neg'] at h2
    have h3 := le_abs_self (rgS (rgCanon (2 * m) m) f0 x)
    have h4 := neg_abs_le (rgS (rgCanon (2 * m) m) f0 x)
    apply max_le <;> linarith
  have hI1 := rgPhi_integrable μ F hFne hFrange (rgCanon (2 * m) m) (hsup _)
  have hI2 := rgPhi_integrable μ F hFne hFrange (fun i => !rgCanon (2 * m) m i) (hsup _)
  have hIU := rgPhi_integrable μ (F ∪ -F) hUne hU (rgCanon (2 * m) m) (hsupU _)
  have hI3 : Integrable (fun x => |rgS (rgCanon (2 * m) m) f0 x|)
      (Measure.pi fun _ : Fin (2 * m) => μ) := by
    refine Integrable.of_bound ?_ ((2 * m : ℕ) : ℝ) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_abs]; exact rgS_abs_le _ f0 (hFrange f0 hf0) x)
    have : Measurable (fun x : Fin (2 * m) → X => rgS (rgCanon (2 * m) m) f0 x) := by
      unfold rgS
      exact Finset.measurable_sum _ fun i _ =>
        ((hFmeas f0 hf0).comp (measurable_pi_apply i)).const_mul _
    exact this.abs.aestronglyMeasurable
  have hg : rgG μ (2 * m) (F ∪ -F) (rgCanon (2 * m) m)
      ≤ 2 * rgG μ (2 * m) F (rgCanon (2 * m) m) + Real.sqrt (4 * m) := by
    have hle : ∫ x, rgPhi (F ∪ -F) (rgCanon (2 * m) m) x ∂(Measure.pi fun _ : Fin (2 * m) => μ)
        ≤ ∫ x, (rgPhi F (rgCanon (2 * m) m) x + rgPhi F (fun i => !rgCanon (2 * m) m i) x
          + |rgS (rgCanon (2 * m) m) f0 x|) ∂(Measure.pi fun _ : Fin (2 * m) => μ) :=
      integral_mono hIU ((hI1.add hI2).add hI3) hpt
    rw [integral_add (f := fun x => rgPhi F (rgCanon (2 * m) m) x
        + rgPhi F (fun i => !rgCanon (2 * m) m i) x)
        (g := fun x => |rgS (rgCanon (2 * m) m) f0 x|) (hI1.add hI2) hI3,
      integral_add (f := fun x => rgPhi F (rgCanon (2 * m) m) x)
        (g := fun x => rgPhi F (fun i => !rgCanon (2 * m) m i) x) hI1 hI2] at hle
    have hb := rg_int_abs_le μ m f0 (hFrange f0 hf0) (hFmeas f0 hf0)
    unfold rgG
    unfold rgG at hneg
    linarith
  have hc : (0:ℝ) ≤ 2 / ((2 * m : ℕ) : ℝ) := by positivity
  nlinarith

theorem lemma3_core {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin (2 * m) → Bool, Measurable (rgPhi F σ)) :
    (RadGauss.RiskBound.rademacherComplexity μ (2 * m) F / 2
        ≤ ENNReal.ofReal (expectedMaxDiscrepancy μ m F)
          + ENNReal.ofReal (2 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ))) ∧
      ENNReal.ofReal (expectedMaxDiscrepancy μ m F)
        ≤ RadGauss.RiskBound.rademacherComplexity μ (2 * m) F
          + ENNReal.ofReal (4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ)))) ∧
    ((∀ f ∈ F, -f ∈ F) →
      RadGauss.RiskBound.rademacherComplexity μ (2 * m) F
        ≤ ENNReal.ofReal (expectedMaxDiscrepancy μ m F)
          + ENNReal.ofReal (4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ)))) := by
  have hN : (0:ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * m)
  have h1 := rademacher_ge_core μ (2 * m) F hFne hFrange hsup
  have h4 := deviation_core μ m hm F hFne hFrange hsup
  have hD := discrepancy_core μ m F
  have hsq := rg_sqrt_ineq _ hN
  have habs := abs_le.1 (h4.1.trans h4.2)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h5 := union_neg_core μ m hm F hFne hFrange hsup
    have h6 := rg_disc_union_le μ m F hFne hFrange hFmeas hsup
    have h7 := rg_sqrt_ineq2 m hm
    apply ENNReal.div_le_of_le_mul
    rw [h5.1]
    refine h5.2.trans ?_
    have e1 : ENNReal.ofReal (2 * expectedMaxDiscrepancy μ m F)
        = ENNReal.ofReal (expectedMaxDiscrepancy μ m F) * 2 := by
      rw [mul_comm, ENNReal.ofReal_mul' (by norm_num)]; simp
    have e2 : ENNReal.ofReal (4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ)))
        = ENNReal.ofReal (2 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ))) * 2 := by
      rw [show 4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ))
          = (2 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ))) * 2 by ring, ENNReal.ofReal_mul' (by norm_num)]
      simp
    calc ENNReal.ofReal (expectedMaxDiscrepancy μ m (F ∪ -F))
          + ENNReal.ofReal ((2 / ((2 * m : ℕ) : ℝ)) * Real.sqrt ((2 * m : ℕ) : ℝ))
        ≤ ENNReal.ofReal (2 * expectedMaxDiscrepancy μ m F
            + (2 / ((2 * m : ℕ) : ℝ)) * Real.sqrt (4 * m))
          + ENNReal.ofReal ((2 / ((2 * m : ℕ) : ℝ)) * Real.sqrt ((2 * m : ℕ) : ℝ)) :=
          add_le_add (ENNReal.ofReal_le_ofReal h6) le_rfl
      _ ≤ ENNReal.ofReal (2 * expectedMaxDiscrepancy μ m F)
            + ENNReal.ofReal ((2 / ((2 * m : ℕ) : ℝ)) * Real.sqrt (4 * m))
          + ENNReal.ofReal ((2 / ((2 * m : ℕ) : ℝ)) * Real.sqrt ((2 * m : ℕ) : ℝ)) :=
          add_le_add ENNReal.ofReal_add_le le_rfl
      _ ≤ ENNReal.ofReal (2 * expectedMaxDiscrepancy μ m F)
            + ENNReal.ofReal (4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ))) := by
          rw [add_assoc]
          apply add_le_add le_rfl
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal h7
      _ = _ := by rw [e1, e2, add_mul]
  · rw [hD]
    calc ENNReal.ofReal (condSup μ (2 * m) F 0)
        ≤ ENNReal.ofReal (((2 : ℝ) ^ (2 * m))⁻¹ * ∑ σ : Fin (2 * m) → Bool,
            condSup μ (2 * m) F (sumSign σ) + 4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ))) :=
          ENNReal.ofReal_le_ofReal (by linarith [habs.1, habs.2])
      _ ≤ _ := ENNReal.ofReal_add_le
      _ ≤ _ := add_le_add h1.1 le_rfl
  · intro hneg
    rw [h1.2 hneg, hD]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
    linarith [habs.1, habs.2]

end RadGauss.Discrepancy

open RadGauss.Discrepancy


theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin (2 * m) → Bool,
      Measurable fun x : Fin (2 * m) → X => ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i)) :
    (RadGauss.RiskBound.rademacherComplexity μ (2 * m) F / 2
        ≤ ENNReal.ofReal (expectedMaxDiscrepancy μ m F)
          + ENNReal.ofReal (2 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ))) ∧
      ENNReal.ofReal (expectedMaxDiscrepancy μ m F)
        ≤ RadGauss.RiskBound.rademacherComplexity μ (2 * m) F
          + ENNReal.ofReal (4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ)))) ∧
    ((∀ f ∈ F, -f ∈ F) →
      RadGauss.RiskBound.rademacherComplexity μ (2 * m) F
        ≤ ENNReal.ofReal (expectedMaxDiscrepancy μ m F)
          + ENNReal.ofReal (4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ)))) := by
  exact lemma3_core μ m hm F hFne hFrange hFmeas hsup
