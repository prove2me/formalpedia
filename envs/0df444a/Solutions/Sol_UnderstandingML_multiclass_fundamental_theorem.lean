-- Prove2me | solution 1 for UnderstandingML.multiclass_fundamental_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T21:40:11.261516+00:00
-- url     : https://prove2.me/submissions/d0000b63-8c7c-40fb-bfde-cb575b767059

import Theorems.Thm_UnderstandingML_multiclass_uc_upper_bound
import Theorems.Thm_UnderstandingML_multiclass_agnostic_lower_bound
import Theorems.Thm_UnderstandingML_multiclass_realizable_upper_bound
import Theorems.Thm_UnderstandingML_multiclass_realizable_lower_bound

open MeasureTheory UnderstandingML

universe u v

namespace MulticlassFundamentalSketch

section Glue

variable {Z : Type*} [MeasurableSpace Z] {Hyp : Type*}

/-- Corollary 4.4: uniform convergence makes every ERM learner an agnostic PAC learner. -/
theorem erm_agnostic_of_uc (loss : Hyp → Z → ℝ) (H : Set Hyp) (mUC : ℝ → ℝ → ℕ)
    (hUC : HasUniformConvergenceWith loss H mUC) (A : Learner Z Hyp)
    (hA : IsERMLearner loss H A) :
    IsAgnosticPACWith loss H A (fun ε δ ↦ mUC (ε / 2) δ) := by
  refine ⟨fun m S ↦ (hA m S).1, ?_⟩
  intro ε δ hε hε1 hδ hδ1 D hD m hm
  refine le_trans (measure_mono ?_)
    (hUC (ε / 2) δ (by linarith) (by linarith) hδ hδ1 D hD m hm)
  rintro S ⟨h', hh', hlt⟩ hrep
  have e1 := abs_le.mp (hrep (A m S) (hA m S).1)
  have e2 := abs_le.mp (hrep h' hh')
  have e3 := (hA m S).2 h' hh'
  linarith [e1.1, e2.2]

theorem hasUC_mono (loss : Hyp → Z → ℝ) (H : Set Hyp) {m₁ m₂ : ℝ → ℝ → ℕ}
    (h : HasUniformConvergenceWith loss H m₁)
    (hle : ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → m₁ ε δ ≤ m₂ ε δ) :
    HasUniformConvergenceWith loss H m₂ :=
  fun ε δ hε hε1 hδ hδ1 D hD m hm ↦
    h ε δ hε hε1 hδ hδ1 D hD m ((hle ε δ hε hε1 hδ hδ1).trans hm)

theorem isAgnosticPAC_mono (loss : Hyp → Z → ℝ) (H : Set Hyp) (A : Learner Z Hyp)
    {m₁ m₂ : ℝ → ℝ → ℕ} (h : IsAgnosticPACWith loss H A m₁)
    (hle : ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → m₁ ε δ ≤ m₂ ε δ) :
    IsAgnosticPACWith loss H A m₂ :=
  ⟨h.1, fun ε δ hε hε1 hδ hδ1 D hD m hm ↦
    h.2 ε δ hε hε1 hδ hδ1 D hD m ((hle ε δ hε hε1 hδ hδ1).trans hm)⟩

end Glue

section Multiclass

variable {X : Type*} {Y : Type*}

theorem isMulticlassPAC_mono [MeasurableSpace X] [MeasurableSpace Y] (H : Set (X → Y))
    (A : Learner (X × Y) (X → Y)) {m₁ m₂ : ℝ → ℝ → ℕ} (h : IsMulticlassPACWith H A m₁)
    (hle : ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → m₁ ε δ ≤ m₂ ε δ) :
    IsMulticlassPACWith H A m₂ :=
  fun ε δ hε hε1 hδ hδ1 D hD f hf hr m hm ↦
    h ε δ hε hε1 hδ hδ1 D hD f hf hr m ((hle ε δ hε hε1 hδ hδ1).trans hm)

/-- An ERM learner exists for a nonempty class with finitely many labels. -/
theorem exists_erm_learner [Fintype Y] (H : Set (X → Y)) (hne : H.Nonempty) :
    ∃ A : Learner (X × Y) (X → Y), IsERMLearner lossMulti H A := by
  classical
  have key : ∀ (m : ℕ) (S : Fin m → X × Y), ∃ h, IsERM lossMulti H S h := by
    intro m S
    have hfin : ((fun h ↦ empRisk lossMulti S h) '' H).Finite := by
      refine (Set.finite_range (fun g : Fin m → Y ↦
        (∑ i, (if g i = (S i).2 then (0 : ℝ) else 1)) / (m : ℝ))).subset ?_
      rintro _ ⟨h, -, rfl⟩
      exact ⟨fun i ↦ h (S i).1, by simp [empRisk, lossMulti]⟩
    obtain ⟨_, ⟨h, hh, rfl⟩, hmin⟩ :=
      hfin.exists_minimal (hne.image (fun h ↦ empRisk lossMulti S h))
    refine ⟨h, hh, fun h' hh' ↦ ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    exact absurd (hmin ⟨h', hh', rfl⟩ hlt.le) (not_le.mpr hlt)
  exact ⟨fun m S ↦ (key m S).choose, fun m S ↦ (key m S).choose_spec⟩

/-- A class of Natarajan dimension `0` has at most one element. -/
theorem eq_of_ndim_eq_zero (H : Set (X → Y)) (h0 : ndim H = 0) {h₁ h₂ : X → Y}
    (h₁H : h₁ ∈ H) (h₂H : h₂ ∈ H) : h₁ = h₂ := by
  classical
  funext x
  by_contra hne
  have hsh : NShatters H {x} := by
    refine ⟨h₁, h₂, by simpa using hne, fun B hB ↦ ?_⟩
    rcases Finset.subset_singleton_iff.mp hB with rfl | rfl
    · exact ⟨h₂, h₂H, by simp, fun _ _ _ ↦ rfl⟩
    · exact ⟨h₁, h₁H, fun _ _ ↦ rfl, by simp⟩
  have : (({x} : Finset X).card : ℕ∞) ≤ ndim H :=
    le_iSup₂_of_le (f := fun (C : Finset X) (_ : NShatters H C) ↦ (C.card : ℕ∞)) {x} hsh le_rfl
  rw [h0] at this
  simp at this

end Multiclass

theorem log_one_div_nonneg {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : 0 ≤ Real.log (1 / δ) :=
  Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)

theorem log_card_mul_div_nonneg (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    0 ≤ Real.log ((n : ℝ) / ε) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · apply Real.log_nonneg
    rw [le_div_iff₀ hε]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith

end MulticlassFundamentalSketch

open MulticlassFundamentalSketch

theorem solution :
    ∃ C₁ C₂ ε₀ δ₀ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSingletonClass X]
        [MeasurableSpace Y] [MeasurableSingletonClass Y] [Fintype Y]
        (H : Set (X → Y)) (d : ℕ), H.Nonempty → (∀ h ∈ H, Measurable h) →
        NPointwiseSeparable H → ndim H = d →
        ((1 ≤ d → HasUniformConvergenceWith lossMulti H (fun ε δ ↦
            ⌈C₂ * (d * Real.log (Fintype.card Y) + Real.log (1 / δ)) / ε ^ 2⌉₊)) ∧
          ∀ mUC : ℝ → ℝ → ℕ, HasUniformConvergenceWith lossMulti H mUC →
            ∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < δ₀ → 2 ≤ d →
              C₁ * (d + Real.log (1 / δ)) / ε ^ 2 ≤ mUC ε δ) ∧
        ((∀ A : Learner (X × Y) (X → Y), IsERMLearner lossMulti H A →
            IsAgnosticPACWith lossMulti H A (fun ε δ ↦
              ⌈C₂ * (d * Real.log (Fintype.card Y) + Real.log (1 / δ)) / ε ^ 2⌉₊)) ∧
          ∀ (A : Learner (X × Y) (X → Y)) (mH : ℝ → ℝ → ℕ), IsAgnosticPACWith lossMulti H A mH →
            ∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < δ₀ → 2 ≤ d →
              C₁ * (d + Real.log (1 / δ)) / ε ^ 2 ≤ mH ε δ) ∧
        ((∀ A : Learner (X × Y) (X → Y), IsERMLearner lossMulti H A →
            IsMulticlassPACWith H A (fun ε δ ↦
              ⌈C₂ * (d * Real.log (Fintype.card Y * d / ε) + Real.log (1 / δ)) / ε⌉₊)) ∧
          ∀ (A : Learner (X × Y) (X → Y)) (mH : ℝ → ℝ → ℕ), IsMulticlassPACWith H A mH →
            ∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < δ₀ → 2 ≤ d →
              C₁ * (d + Real.log (1 / δ)) / ε ≤ mH ε δ) := by
  obtain ⟨Cu, hCu, hUC⟩ := multiclass_uc_upper_bound.{u, v}
  obtain ⟨Ca, εa, δa, hCa, hεa, hδa, hAL⟩ := multiclass_agnostic_lower_bound.{u, v}
  obtain ⟨Cr, hCr, hRU⟩ := multiclass_realizable_upper_bound.{u, v}
  obtain ⟨Cl, εl, δl, hCl, hεl, hδl, hRL⟩ := multiclass_realizable_lower_bound.{u, v}
  refine ⟨min (Ca / 4) Cl, max (4 * Cu) Cr, min (εa / 2) εl, min (min δa δl) (1 / 2),
    lt_min (by positivity) hCl, lt_max_of_lt_right hCr, lt_min (by positivity) hεl,
    lt_min (lt_min hδa hδl) (by norm_num), ?_⟩
  intro X Y _ _ _ _ _ H d hne hmeas hsep hdim
  have hTk : ∀ δ : ℝ, 0 < δ → δ < 1 →
      0 ≤ (d : ℝ) * Real.log (Fintype.card Y) + Real.log (1 / δ) := fun δ hδ hδ1 ↦
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
      (log_one_div_nonneg hδ hδ1)
  have hTr : ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      0 ≤ (d : ℝ) * Real.log (Fintype.card Y * d / ε) + Real.log (1 / δ) :=
    fun ε δ hε hε1 hδ hδ1 ↦
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by
      have := log_card_mul_div_nonneg (Fintype.card Y * d) hε hε1
      push_cast at this; exact this))
      (log_one_div_nonneg hδ hδ1)
  have hTd : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ (d : ℝ) + Real.log (1 / δ) := fun δ hδ hδ1 ↦
    add_nonneg (Nat.cast_nonneg _) (log_one_div_nonneg hδ hδ1)
  have hδ₀a : ∀ δ : ℝ, δ < min (min δa δl) (1 / 2) → δ < δa := fun δ h ↦
    lt_of_lt_of_le h ((min_le_left _ _).trans (min_le_left _ _))
  have hδ₀l : ∀ δ : ℝ, δ < min (min δa δl) (1 / 2) → δ < δl := fun δ h ↦
    lt_of_lt_of_le h ((min_le_left _ _).trans (min_le_right _ _))
  have hδ₀1 : ∀ δ : ℝ, δ < min (min δa δl) (1 / 2) → δ < 1 := fun δ h ↦ by
    linarith [min_le_right (min δa δl) (1 / 2)]
  have hε₀a : ∀ ε : ℝ, ε < min (εa / 2) εl → ε < εa / 2 := fun ε h ↦
    lt_of_lt_of_le h (min_le_left _ _)
  have hε₀l : ∀ ε : ℝ, ε < min (εa / 2) εl → ε < εl := fun ε h ↦
    lt_of_lt_of_le h (min_le_right _ _)
  refine ⟨⟨fun hd ↦ ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- uniform-convergence upper bound
    refine hasUC_mono _ _ (hUC H d hne hmeas hsep hdim hd) fun ε δ hε hε1 hδ hδ1 ↦ ?_
    apply Nat.ceil_mono
    gcongr
    · exact hTk δ hδ hδ1
    · exact le_trans (by linarith) (le_max_left _ _)
  · -- uniform-convergence lower bound, via an ERM learner
    intro mUC hmUC ε δ hε hεlt hδ hδlt hd
    obtain ⟨A, hA⟩ := exists_erm_learner H hne
    have h := hAL H d hmeas hdim hd A _ (erm_agnostic_of_uc _ _ _ hmUC A hA) (2 * ε) δ
      (by linarith) (by linarith [hε₀a ε hεlt]) hδ (hδ₀a δ hδlt)
    have e : 2 * ε / 2 = ε := by ring
    simp only [e] at h
    refine le_trans ?_ h
    have hT := hTd δ hδ (hδ₀1 δ hδlt)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : min (Ca / 4) Cl ≤ Ca / 4 := min_le_left _ _
    have h2 : (2 * ε) ^ 2 = 4 * ε ^ 2 := by ring
    rw [h2]
    have : 0 ≤ ε ^ 2 * (d + Real.log (1 / δ)) := by positivity
    nlinarith
  · -- agnostic upper bound for ERM learners
    intro A hA
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · refine ⟨fun m S ↦ (hA m S).1, ?_⟩
      intro ε δ hε hε1 hδ hδ1 D hD m hm
      have hsub : {S : Fin m → X × Y | ∃ h' ∈ H, risk lossMulti D h' + ε <
          risk lossMulti D (A m S)} = ∅ := by
        ext S
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
          not_lt]
        intro h' hh'
        rw [eq_of_ndim_eq_zero H (by exact_mod_cast hdim) (hA m S).1 hh']
        linarith
      rw [hsub]; simp
    · refine isAgnosticPAC_mono _ _ _
        (erm_agnostic_of_uc _ _ _ (hUC H d hne hmeas hsep hdim hd) A hA)
        fun ε δ hε hε1 hδ hδ1 ↦ ?_
      apply Nat.ceil_mono
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hT := hTk δ hδ hδ1
      have : 4 * Cu ≤ max (4 * Cu) Cr := le_max_left _ _
      have h2 : (ε / 2) ^ 2 = ε ^ 2 / 4 := by ring
      rw [h2]
      have : 0 ≤ ε ^ 2 * ((d : ℝ) * Real.log (Fintype.card Y) + Real.log (1 / δ)) := by
        positivity
      nlinarith
  · -- agnostic lower bound
    intro A mH hA ε δ hε hεlt hδ hδlt hd
    refine le_trans ?_ (hAL H d hmeas hdim hd A mH hA ε δ hε
      (by linarith [hε₀a ε hεlt]) hδ (hδ₀a δ hδlt))
    have hT := hTd δ hδ (hδ₀1 δ hδlt)
    gcongr
    exact (min_le_left _ _).trans (by linarith)
  · -- realizable upper bound
    intro A hA
    refine isMulticlassPAC_mono _ _ (hRU H d hne hmeas hsep hdim A hA)
      fun ε δ hε hε1 hδ hδ1 ↦ ?_
    apply Nat.ceil_mono
    gcongr
    · exact hTr ε δ hε hε1 hδ hδ1
    · exact le_max_right _ _
  · -- realizable lower bound
    intro A mH hA ε δ hε hεlt hδ hδlt hd
    refine le_trans ?_ (hRL H d hmeas hdim hd A mH hA ε δ hε (hε₀l ε hεlt) hδ (hδ₀l δ hδlt))
    have hT := hTd δ hδ (hδ₀1 δ hδlt)
    gcongr
    exact min_le_right _ _

