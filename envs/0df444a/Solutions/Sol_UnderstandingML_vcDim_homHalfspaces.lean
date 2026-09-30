-- Prove2me | solution 1 for UnderstandingML.vcDim_homHalfspaces
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T14:55:49.309082+00:00
-- url     : https://prove2.me/submissions/ebd3acfa-05cb-4646-a14e-12367e31dc1f

import Definitions.Def_UnderstandingML_Linear

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML.HalfspaceVCProof

variable {d : ℕ}

/-- Core sign argument: if a nonzero coefficient vector `a` annihilates every realizable
score vector `φ` (i.e. `∑ a c φ c = 0`), then the labeling `c ↦ [a c > 0]` (or its sign flip)
cannot be realized by `c ↦ [φ c > 0]`. -/
lemma sign_contradiction {ι : Type*} [Fintype ι] (a : ι → ℝ) (i₀ : ι) (hi₀ : a i₀ ≠ 0)
    (hreal : ∀ g : ι → Bool, ∃ φ : ι → ℝ, (∀ c, decide (0 < φ c) = g c) ∧ ∑ c, a c * φ c = 0) :
    False := by
  have key : ∀ b : ι → ℝ, 0 < b i₀ →
      (∀ φ : ι → ℝ, (∑ c, a c * φ c = 0) → ∑ c, b c * φ c = 0) →
      (∀ g : ι → Bool, ∃ φ : ι → ℝ, (∀ c, decide (0 < φ c) = g c) ∧ ∑ c, b c * φ c = 0) →
      False := by
    intro b hb _ hrealb
    obtain ⟨φ, hφ, hsum⟩ := hrealb (fun c => decide (0 < b c))
    have hterm : ∀ c, 0 ≤ b c * φ c := by
      intro c
      have := hφ c
      by_cases hbc : 0 < b c
      · have : 0 < φ c := by simpa [hbc] using this
        positivity
      · have : ¬ 0 < φ c := by simpa [hbc] using this
        push_neg at hbc this
        nlinarith
    have hpos : 0 < b i₀ * φ i₀ := by
      have : 0 < φ i₀ := by simpa [hb] using hφ i₀
      positivity
    have : b i₀ * φ i₀ ≤ ∑ c, b c * φ c :=
      Finset.single_le_sum (fun c _ => hterm c) (Finset.mem_univ i₀)
    linarith
  rcases lt_or_gt_of_ne hi₀ with hneg | hpos
  · refine key (fun c => -a c) (by linarith) (fun φ h => ?_) (fun g => ?_)
    · simp only [neg_mul, Finset.sum_neg_distrib, h, neg_zero]
    · obtain ⟨φ, h1, h2⟩ := hreal g
      refine ⟨φ, h1, ?_⟩
      simp only [neg_mul, Finset.sum_neg_distrib, h2, neg_zero]
  · exact key a hpos (fun _ h => h) hreal

/-- A shattered set of homogenous halfspaces has at most `d` points. -/
lemma card_le_of_shatters (C : Finset (Vec d)) (hC : Shatters (homHalfspaces d) C) :
    C.card ≤ d := by
  by_contra hlt
  push_neg at hlt
  have hnot : ¬ LinearIndependent ℝ (fun c : C => (c : Vec d)) := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_coe, finrank_euclideanSpace_fin] at this
    omega
  obtain ⟨a, ha, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hnot
  refine sign_contradiction a i₀ hi₀ fun g => ?_
  obtain ⟨h, ⟨w, rfl⟩, hh⟩ := hC g
  refine ⟨fun c => ⟪w, (c : Vec d)⟫_ℝ, fun c => ?_, ?_⟩
  · rw [← hh c]; simp [halfspace]
  · have : ⟪w, ∑ c, a c • (c : Vec d)⟫_ℝ = 0 := by rw [ha, inner_zero_right]
    rw [inner_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inner_smul_right]

/-- The standard basis is shattered by homogenous halfspaces. -/
lemma exists_shattered : ∃ C : Finset (Vec d), Shatters (homHalfspaces d) C ∧ C.card = d := by
  classical
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hinj : Function.Injective (fun i => e i) := e.orthonormal.linearIndependent.injective
  refine ⟨Finset.univ.map ⟨fun i => e i, hinj⟩, fun g => ?_, by simp⟩
  have hmem : ∀ i, e i ∈ Finset.univ.map ⟨fun i => e i, hinj⟩ := fun i => by simp
  let s : Fin d → ℝ := fun i => if g ⟨e i, hmem i⟩ then 1 else -1
  refine ⟨halfspace (∑ j, s j • e j) 0, ⟨_, rfl⟩, fun c => ?_⟩
  obtain ⟨c, hc⟩ := c
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hc
  have hinner : ⟪∑ j, s j • e j, e i⟫_ℝ = s i := by
    rw [real_inner_comm, e.orthonormal.inner_right_fintype]
  show decide (0 < ⟪∑ j, s j • e j, e i⟫_ℝ + 0) = g ⟨e i, hc⟩
  rw [add_zero, hinner]
  show decide (0 < if g ⟨e i, hmem i⟩ = true then (1 : ℝ) else -1) = g ⟨e i, hmem i⟩
  cases g ⟨e i, hmem i⟩ <;> simp

end UnderstandingML.HalfspaceVCProof

open UnderstandingML UnderstandingML.HalfspaceVCProof in
theorem solution (d : ℕ) : vcDim (homHalfspaces d) = d := by
  apply le_antisymm
  · refine iSup₂_le fun C hC => ?_
    exact_mod_cast card_le_of_shatters C hC
  · obtain ⟨C, hC, hcard⟩ := exists_shattered (d := d)
    calc ((d : ℕ) : ℕ∞) = (C.card : ℕ∞) := by rw [hcard]
      _ ≤ _ := le_iSup₂ (f := fun (C : Finset (Vec d)) (_ : Shatters (homHalfspaces d) C) =>
      (C.card : ℕ∞)) C hC
