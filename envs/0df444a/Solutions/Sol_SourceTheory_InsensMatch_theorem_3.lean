-- Prove2me | solution 1 for SourceTheory.InsensMatch.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:31:37.253714+00:00
-- url     : https://prove2.me/submissions/52784801-d949-4f1b-a4f7-9e612877b144

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model
import Theorems.Thm_SourceTheory_InsensMatch_source_prob_range
import Theorems.Thm_SourceTheory_InsensMatch_pmatcher_exists_unique
import Theorems.Thm_SourceTheory_InsensMatch_matching_partitions
import Theorems.Thm_SourceTheory_InsensMatch_weight_comparison
import Theorems.Thm_SourceTheory_InsensMatch_boundary_step
import Theorems.Thm_SourceTheory_InsensMatch_dual_step

namespace SourceTheory.InsensMatch

open Set SourceTheory.Uniform

/-- Additivity facts for a threefold partition under a probability measure on the source. -/
lemma thm3_part_sums {S : Type*} (𝒮 : Set (Set S)) (h𝒮 : MeasureTheory.IsSetAlgebra 𝒮)
    (P : Set S → ℝ) (hP : IsProbOn 𝒮 P) (X₁ X₂ X₃ : Set S) (hX : IsPartition3 𝒮 X₁ X₂ X₃) :
    0 ≤ P X₁ ∧ 0 ≤ P X₂ ∧ 0 ≤ P X₃ ∧ P X₁ + P X₂ + P X₃ = 1 := by
  obtain ⟨h1, h2, h3, d12, d13, d23, hu⟩ := hX
  obtain ⟨hPu, hPn, hPa⟩ := hP
  refine ⟨hPn _ h1, hPn _ h2, hPn _ h3, ?_⟩
  have e12 := hPa X₁ h1 X₂ h2 d12
  have e3 := hPa (X₁ ∪ X₂) (h𝒮.union_mem h1 h2) X₃ h3 (Disjoint.union_left d13 d23)
  rw [hu, hPu, e12] at e3
  linarith

/-- In a uniform source with continuous source function, any probabilities `0 ≤ q ≤ r ≤ 1`
are realised by a threefold partition with `P X₁ = q`, `P (X₁ ∪ X₂) = r`. -/
lemma thm3_exists_partition {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒮 : Set (Set S)) (h𝒮 : IsSource 𝓔 W 𝒮) (P : Set S → ℝ) (w : ℝ → ℝ)
    (hP : IsUniformWith pref U 𝒮 P) (hw : IsSourceFunction W 𝒮 P w)
    (q r : ℝ) (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ 1) :
    ∃ X₁ X₂ X₃ : Set S, IsPartition3 𝒮 X₁ X₂ X₃ ∧ P X₁ = q ∧ P X₂ = r - q := by
  obtain ⟨X₁, hX₁, hPX₁⟩ :=
    source_prob_range 𝓔 pref U W h1 𝒮 h𝒮 P w hP hw q ⟨hq, by linarith⟩
  have halg := h𝒮.algebra
  have huniv : univ ∈ 𝒮 := halg.univ_mem
  obtain ⟨⟨⟨_, hmono, _, _⟩, _⟩, hWw⟩ := hw
  obtain ⟨⟨hPu, hPn, hPa⟩, _⟩ := hP
  have hWX₁ : W X₁ = w q := by rw [hWw X₁ hX₁, hPX₁]
  have hWu : W univ = w 1 := by rw [hWw univ huniv, hPu]
  have hq01 : q ∈ Icc (0:ℝ) 1 := ⟨hq, by linarith⟩
  have hr01 : r ∈ Icc (0:ℝ) 1 := ⟨by linarith, hr⟩
  have h101 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hlo : W X₁ ≤ w r := by rw [hWX₁]; exact hmono.monotoneOn hq01 hr01 hqr
  have hhi : w r ≤ W univ := by rw [hWu]; exact hmono.monotoneOn hr01 h101 hr
  obtain ⟨E, hE, hX₁E, -, hWE⟩ :=
    h𝒮.convexRanged X₁ hX₁ univ huniv (subset_univ _) (w r) hlo hhi
  have hEc : Eᶜ ∈ 𝒮 := halg.compl_mem hE
  have hPE01 : P E ∈ Icc (0:ℝ) 1 := by
    have := hPa E hE Eᶜ hEc disjoint_compl_right
    rw [union_compl_self, hPu] at this
    have := hPn _ hEc
    exact ⟨hPn _ hE, by linarith⟩
  have hPE : P E = r := by
    apply hmono.injOn hPE01 hr01
    rw [← hWw E hE, hWE]
  have hX₂ : E \ X₁ ∈ 𝒮 := halg.sdiff_mem hE hX₁
  refine ⟨X₁, E \ X₁, Eᶜ, ⟨hX₁, hX₂, hEc, disjoint_sdiff_right, ?_, ?_, ?_⟩, hPX₁, ?_⟩
  · exact Disjoint.mono_right (compl_subset_compl.mpr hX₁E) disjoint_compl_right
  · exact Disjoint.mono_left diff_subset disjoint_compl_right
  · rw [union_diff_cancel hX₁E, union_compl_self]
  · have := hPa X₁ hX₁ (E \ X₁) hX₂ disjoint_sdiff_right
    rw [union_diff_cancel hX₁E, hPE, hPX₁] at this
    linarith

end SourceTheory.InsensMatch

open Set SourceTheory.Uniform SourceTheory.InsensMatch

theorem solution {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : SourceTheory.Uniform.Assumption2 pref U W 𝒞 𝒜 PC PA wC wA)
    (B D : Set S) (hB : B ∈ 𝒜) (hD : D ∈ 𝒜) :
    SourceTheory.Uniform.IsMoreInsensitive W 𝒜 𝒞 B D ↔
      ∃ φ : ℝ → ℝ, SourceTheory.Uniform.IsTransformation φ ∧ SourceTheory.Uniform.IsInsensitive φ (PA B) (PA D) ∧
        ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p) := by
  obtain ⟨hPC, hPA, hwC, hwA⟩ := h2
  have h2' : Assumption2 pref U W 𝒞 𝒜 PC PA wC wA := ⟨hPC, hPA, hwC, hwA⟩
  constructor
  · -- (⇒) the pmatcher is insensitive
    intro hins
    obtain ⟨φ, hφ, hφA, -⟩ := pmatcher_exists_unique 𝓔 pref U W h1 𝒜 𝒞 h𝒜 h𝒞 PC PA wC wA h2'
    refine ⟨φ, hφ, ?_, hφA⟩
    intro p₁ p₂ p₃ hp₁ hp₂ hp₃ hsum
    have hmaps := hφ.1.1
    have hmono := hφ.1.2.1
    -- an 𝒜-partition with probabilities p₁, p₂, p₃
    obtain ⟨A₁, A₂, A₃, hA, hPA₁, hPA₂⟩ :=
      thm3_exists_partition 𝓔 pref U W h1 𝒜 h𝒜 PA wA hPA hwA p₁ (p₁ + p₂) hp₁ (by linarith)
        (by linarith)
    have hPA₂' : PA A₂ = p₂ := by rw [hPA₂]; ring
    obtain ⟨-, -, -, hsA⟩ := thm3_part_sums 𝒜 h𝒜.algebra PA hPA.1 A₁ A₂ A₃ hA
    have hPA₃ : PA A₃ = p₃ := by linarith
    -- a matching 𝒞-partition with probabilities φ p₁, φ (p₁+p₂) - φ p₁, …
    have hp1 : p₁ ∈ Icc (0:ℝ) 1 := ⟨hp₁, by linarith⟩
    have hp12 : p₁ + p₂ ∈ Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
    have hφ1 := hmaps hp1
    have hφ12 := hmaps hp12
    have hle : φ p₁ ≤ φ (p₁ + p₂) := hmono.monotoneOn hp1 hp12 (by linarith)
    obtain ⟨C₁, C₂, C₃, hC, hPC₁, hPC₂⟩ :=
      thm3_exists_partition 𝓔 pref U W h1 𝒞 h𝒞 PC wC hPC hwC (φ p₁) (φ (p₁ + p₂)) hφ1.1 hle hφ12.2
    have hφ' : IsTransformation φ := hφ
    have hmatch := (matching_partitions 𝓔 pref U W h1 𝒜 𝒞 h𝒜 h𝒞 PC PA wC wA h2' φ hφ' hφA
      C₁ C₂ C₃ A₁ A₂ A₃ hC hA).mpr ⟨by rw [hPA₁, hPC₁], by rw [hPA₁, hPA₂', hPC₁, hPC₂]; ring⟩
    obtain ⟨hm₁, hm₃⟩ := hmatch
    have hwc := weight_comparison 𝓔 pref U W h1 𝒜 𝒞 h𝒜 h𝒞 PC PA wC wA h2' φ hφ' hφA
      C₁ C₂ C₃ A₁ A₂ A₃ hC hA hm₁ hm₃
    have hds := dual_step 𝓔 pref U W h1 𝒜 𝒞 h𝒜 h𝒞 PC PA wC wA h2' φ hφ' hφA
      C₁ C₂ C₃ A₁ A₂ A₃ hC hA hm₁ hm₃ B hB
    have hbs := boundary_step 𝓔 pref U W h1 𝒜 h𝒜 PA wA hPA hwA D hD A₁ A₂ A₃ hA
    obtain ⟨hI1, hI2⟩ := hins C₁ C₂ C₃ A₁ A₂ A₃ hC hA
    simp only [hPA₁, hPA₂', hPA₃] at hwc hds hbs
    constructor
    · intro hd
      exact hwc.mp (hI1 hm₁ hm₃ (hm₃ ▸ hbs.mpr hd))
    · intro hb
      exact hds.1.mp (hI2 (hds.2.mpr hb) hm₁ hm₃)
  · -- (⇐) an insensitive matcher yields more insensitivity
    rintro ⟨φ, hφ, hinsφ, hφA⟩
    intro C₁ C₂ C₃ A₁ A₂ A₃ hC hA
    obtain ⟨n₁, n₂, n₃, hs⟩ := thm3_part_sums 𝒜 h𝒜.algebra PA hPA.1 A₁ A₂ A₃ hA
    have hI := hinsφ (PA A₁) (PA A₂) (PA A₃) n₁ n₂ n₃ hs
    have hbs := boundary_step 𝓔 pref U W h1 𝒜 h𝒜 PA wA hPA hwA D hD A₁ A₂ A₃ hA
    constructor
    · intro hm₁ hm₃ hd
      have hwc := weight_comparison 𝓔 pref U W h1 𝒜 𝒞 h𝒜 h𝒞 PC PA wC wA h2' φ hφ hφA
        C₁ C₂ C₃ A₁ A₂ A₃ hC hA hm₁ hm₃
      exact hwc.mpr (hI.1 (hbs.mp (hm₃ ▸ hd)))
    · intro hb hm₁ hm₃
      have hds := dual_step 𝓔 pref U W h1 𝒜 𝒞 h𝒜 h𝒞 PC PA wC wA h2' φ hφ hφA
        C₁ C₂ C₃ A₁ A₂ A₃ hC hA hm₁ hm₃ B hB
      exact hds.1.mpr (hI.2 (hds.2.mp hb))


