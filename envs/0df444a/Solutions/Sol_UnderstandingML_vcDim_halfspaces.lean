-- Prove2me | solution 1 for UnderstandingML.vcDim_halfspaces
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T14:57:06.378508+00:00
-- url     : https://prove2.me/submissions/41ebd09b-4fdb-4cfb-8181-86d359204df5

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

/-- A shattered set of (nonhomogenous) halfspaces has at most `d + 1` points. -/
lemma card_le_of_shatters (C : Finset (Vec d)) (hC : Shatters (halfspaces d) C) :
    C.card ≤ d + 1 := by
  by_contra hlt
  push_neg at hlt
  have hnot : ¬ LinearIndependent ℝ (fun c : C => ((c : Vec d), (1 : ℝ))) := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_coe, Module.finrank_prod, finrank_euclideanSpace_fin,
      Module.finrank_self] at this
    omega
  obtain ⟨a, ha, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hnot
  have ha1 : ∑ c, a c • (c : Vec d) = 0 := by
    have := congrArg Prod.fst ha
    simpa [Prod.fst_sum] using this
  have ha2 : ∑ c, a c = 0 := by
    have := congrArg Prod.snd ha
    simpa [Prod.snd_sum] using this
  refine sign_contradiction a i₀ hi₀ fun g => ?_
  obtain ⟨h, ⟨w, b, rfl⟩, hh⟩ := hC g
  refine ⟨fun c => ⟪w, (c : Vec d)⟫_ℝ + b, fun c => ?_, ?_⟩
  · rw [← hh c]; simp [halfspace]
  · have : ⟪w, ∑ c, a c • (c : Vec d)⟫_ℝ = 0 := by rw [ha1, inner_zero_right]
    rw [inner_sum] at this
    have h2 : ∑ c, a c * (⟪w, (c : Vec d)⟫_ℝ + b) =
        ∑ c, ⟪w, a c • (c : Vec d)⟫_ℝ + (∑ c, a c) * b := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [inner_smul_right]; ring
    rw [h2, this, ha2]; ring

/-- The origin together with the standard basis is shattered by halfspaces. -/
lemma exists_shattered :
    ∃ C : Finset (Vec d), Shatters (halfspaces d) C ∧ C.card = d + 1 := by
  classical
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hinj : Function.Injective (fun i => e i) := e.orthonormal.linearIndependent.injective
  let B : Finset (Vec d) := Finset.univ.map ⟨fun i => e i, hinj⟩
  have h0 : (0 : Vec d) ∉ B := by
    intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_map.1 h
    have := e.orthonormal.1 i
    have hi' : e i = 0 := hi
    rw [hi', norm_zero] at this
    exact zero_ne_one this
  refine ⟨insert 0 B, fun g => ?_, by rw [Finset.card_insert_of_notMem h0]; simp [B]⟩
  have hmem : ∀ i, e i ∈ insert 0 B := fun i => by simp [B]
  have hmem0 : (0 : Vec d) ∈ insert 0 B := Finset.mem_insert_self _ _
  let b : ℝ := if g ⟨0, hmem0⟩ then 1 / 2 else -1 / 2
  let s : Fin d → ℝ := fun i => (if g ⟨e i, hmem i⟩ then 1 else -1) - b
  refine ⟨halfspace (∑ j, s j • e j) b, ⟨_, _, rfl⟩, fun c => ?_⟩
  obtain ⟨c, hc⟩ := c
  rcases Finset.mem_insert.1 hc with rfl | hcB
  · show decide (0 < ⟪∑ j, s j • e j, (0 : Vec d)⟫_ℝ + b) = g ⟨0, hmem0⟩
    rw [inner_zero_right, zero_add]
    show decide (0 < if g ⟨0, hmem0⟩ = true then (1 / 2 : ℝ) else -1 / 2) = g ⟨0, hmem0⟩
    cases g ⟨0, hmem0⟩ <;> norm_num
  · obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hcB
    have hinner : ⟪∑ j, s j • e j, e i⟫_ℝ = s i := by
      rw [real_inner_comm, e.orthonormal.inner_right_fintype]
    show decide (0 < ⟪∑ j, s j • e j, e i⟫_ℝ + b) = g ⟨e i, hmem i⟩
    rw [hinner]
    show decide (0 < (if g ⟨e i, hmem i⟩ = true then (1 : ℝ) else -1) - b + b) = g ⟨e i, hmem i⟩
    rw [sub_add_cancel]
    cases g ⟨e i, hmem i⟩ <;> simp

end UnderstandingML.HalfspaceVCProof

open UnderstandingML UnderstandingML.HalfspaceVCProof in
theorem solution (d : ℕ) : vcDim (halfspaces d) = d + 1 := by
  apply le_antisymm
  · refine iSup₂_le fun C hC => ?_
    exact_mod_cast card_le_of_shatters C hC
  · obtain ⟨C, hC, hcard⟩ := exists_shattered (d := d)
    calc ((d : ℕ∞) + 1) = (C.card : ℕ∞) := by rw [hcard]; push_cast; rfl
      _ ≤ _ := le_iSup₂ (f := fun (C : Finset (Vec d)) (_ : Shatters (halfspaces d) C) =>
        (C.card : ℕ∞)) C hC
