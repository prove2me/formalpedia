-- Prove2me | solution 1 for ThomsonKS.Char.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:31:20.900123+00:00
-- url     : https://prove2.me/submissions/8a2caf6e-c1b3-4f59-9bdd-447c29f0b246

import Mathlib
import Definitions.Def_ThomsonKS_Char_Setting
import Theorems.Thm_ThomsonKS_Char_theorem_1
import Theorems.Thm_ThomsonKS_Char_replica_problem_exists

open ThomsonKS.Char
open scoped Pointwise

lemma ks2_scale_mem {P : Finset ℕ} {S : Set (P → ℝ)} (hS : S ∈ DivProb P)
    {c : P → ℝ} (hc : ∀ i, 0 < c i) : scale c '' S ∈ DivProb P := by
  obtain ⟨hP, hnn, hcpt, hcvx, ⟨x0, hx0, hx0p⟩, hcomp⟩ := hS
  have hlin : IsLinearMap ℝ (scale c) :=
    ⟨fun x y => by funext i; simp [scale]; ring, fun r x => by funext i; simp [scale]; ring⟩
  have hcont : Continuous (scale c) :=
    continuous_pi fun i => continuous_const.mul (continuous_apply i)
  refine ⟨hP, ?_, hcpt.image hcont, hcvx.is_linear_image hlin, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ i
    exact mul_nonneg (hc i).le (hnn x hx i)
  · exact ⟨scale c x0, ⟨x0, hx0, rfl⟩, fun i => mul_pos (hc i) (hx0p i)⟩
  · rintro _ ⟨x, hx, rfl⟩ y hy hyx
    refine ⟨fun i => y i / c i, hcomp x hx _ ?_ ?_, ?_⟩
    · intro i; exact div_nonneg (hy i) (hc i).le
    · intro i
      have := hyx i
      simp only [scale] at this
      rw [div_le_iff₀ (hc i)]; linarith
    · funext i; simp [scale]; field_simp [(hc i).ne']

lemma ks2_relabel_eq {P P' : Finset ℕ} (γ : P ≃ P') (S : Set (P → ℝ)) :
    relabel γ S = (fun x : P → ℝ => fun i' => x (γ.symm i')) '' S := by
  ext x'
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, funext fun i' => ?_⟩
    have := h (γ.symm i')
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, fun i => by simp⟩

lemma ks2_relabel_mem {P P' : Finset ℕ} (γ : P ≃ P') {S : Set (P → ℝ)} (hS : S ∈ DivProb P) :
    relabel γ S ∈ DivProb P' := by
  rw [ks2_relabel_eq]
  obtain ⟨hP, hnn, hcpt, hcvx, ⟨x0, hx0, hx0p⟩, hcomp⟩ := hS
  set g : (P → ℝ) → (P' → ℝ) := fun x i' => x (γ.symm i') with hg
  have hlin : IsLinearMap ℝ g := ⟨fun x y => rfl, fun r x => rfl⟩
  have hcont : Continuous g := continuous_pi fun i' => continuous_apply _
  refine ⟨?_, ?_, hcpt.image hcont, hcvx.is_linear_image hlin, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hP
    exact ⟨_, (γ ⟨i, hi⟩).2⟩
  · rintro _ ⟨x, hx, rfl⟩ i'
    exact hnn x hx _
  · exact ⟨g x0, ⟨x0, hx0, rfl⟩, fun i' => hx0p _⟩
  · rintro _ ⟨x, hx, rfl⟩ y hy hyx
    refine ⟨fun i => y (γ i), hcomp x hx _ (fun i => hy _) (fun i => ?_), ?_⟩
    · have := hyx (γ i); simpa [hg] using this
    · funext i'; simp [hg]

lemma ks2_idealPt_ge {P : Finset ℕ} {S : Set (P → ℝ)} (hS : S ∈ DivProb P) {x : P → ℝ}
    (hx : x ∈ S) (i : P) : x i ≤ idealPt S i := by
  have hb : BddAbove ((fun x : P → ℝ => x i) '' S) :=
    (hS.2.2.1.image (continuous_apply i)).bddAbove
  exact le_csSup hb ⟨x, hx, rfl⟩

lemma ks2_idealPt_pos {P : Finset ℕ} {S : Set (P → ℝ)} (hS : S ∈ DivProb P) (i : P) :
    0 < idealPt S i := by
  obtain ⟨x0, hx0, hx0p⟩ := hS.2.2.2.2.1
  exact lt_of_lt_of_le (hx0p i) (ks2_idealPt_ge hS hx0 i)

lemma ks2_idealPt_scale {P : Finset ℕ} (S : Set (P → ℝ)) {c : P → ℝ} (hc : ∀ i, 0 < c i) :
    idealPt (scale c '' S) = scale c (idealPt S) := by
  funext i
  simp only [idealPt, scale]
  rw [Set.image_image]
  have : (fun x : P → ℝ => scale c x i) '' S = c i • ((fun x : P → ℝ => x i) '' S) := by
    rw [← Set.image_smul, Set.image_image]; rfl
  rw [this, Real.sSup_smul_of_nonneg (hc i).le, smul_eq_mul]

theorem solution (F : Solution) (hF : IsSolution F) (hW : WPO F) (hA : An F)
    (hI : SInv F) (hM : Mon F) : ∀ P : Finset ℕ, ∀ S ∈ DivProb P, KS P S ≤ F P S := by
  intro P S hS
  obtain ⟨hK, -, -, hKI, -, -⟩ := theorem_1
  set c : P → ℝ := fun i => 1 / idealPt S i with hc_def
  have hc : ∀ i, 0 < c i := fun i => one_div_pos.mpr (ks2_idealPt_pos hS i)
  set S' := scale c '' S with hS'_def
  have hS' : S' ∈ DivProb P := ks2_scale_mem hS hc
  have ha : idealPt S' = fun _ => 1 := by
    rw [hS'_def, ks2_idealPt_scale S hc]
    funext i
    simp only [scale, hc_def]
    field_simp [(ks2_idealPt_pos hS i).ne']
  set t : ℝ := sSup {t : ℝ | 0 ≤ t ∧ t • idealPt S' ∈ S'} with ht_def
  have hKS' : KS P S' = fun _ => t := by
    show t • idealPt S' = _
    rw [ha]; funext i; simp
  have htS : (fun _ => t) ∈ S' := hKS' ▸ hK P S' hS'
  have ht0 : 0 ≤ t := by
    have := hS'.2.1 _ htS
    obtain ⟨i, hi⟩ := hS'.1
    exact this ⟨i, hi⟩
  -- main claim: F P S' i₀ ≥ t for every i₀
  have key : ∀ i₀ : P, t ≤ F P S' i₀ := by
    intro i₀
    by_contra hlt'
    have hlt := not_le.mp hlt'
    obtain ⟨Q, hPQ, -, T, hT, hsl, haT, hrep⟩ :=
      replica_problem_exists P i₀.1 i₀.2 S' hS' ha t htS
    have hbound : ∀ j : Q, F Q T j < t := by
      intro j
      obtain ⟨Pj, hPj, hj, σ, hσ, hslj⟩ := hrep j.1 j.2
      have hrelS : relabel σ S' ∈ DivProb Pj := ks2_relabel_mem σ hS'
      have hmon := hM Pj Q hPj (relabel σ S') hrelS T hT hslj.symm ⟨j.1, hj⟩
      have han := hA P Pj σ S' hS' (relabel σ S') hrelS rfl i₀
      have han' : F Pj (relabel σ S') ⟨j.1, hj⟩ = F P S' i₀ := by rw [← hσ]; exact han
      exact lt_of_le_of_lt (le_trans hmon han'.le) hlt
    exact hW Q T hT (fun _ => t) (fun _ => ht0) hbound haT
  have hFS' : F P S' = scale c (F P S) := hI P S hS c hc
  have hKS'' : KS P S' = scale c (KS P S) := hKI P S hS c hc
  intro i
  have h1 := key i
  have h2 : KS P S' i = t := by rw [hKS']
  rw [hFS'] at h1
  rw [hKS''] at h2
  simp only [scale] at h1 h2
  have := hc i
  nlinarith
