-- Prove2me | solution 1 for UhlmannRoof.RankTwo.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:49:24.763023+00:00
-- url     : https://prove2.me/submissions/189930e6-19e5-4983-847a-70613360a2d7

import Mathlib
import Definitions.Def_UhlmannRoof_RankTwo_Model

open UhlmannRoof.RankTwo in
theorem solution {d : ℕ} (S : Set (Mat d)) (hS : IsRSet S)
    (F : Mat d → ℝ) (hF : ConvexOn ℝ S F)
    (hpure : ∀ ρ ∈ S, IsPure ρ → F ρ ≤ R ρ) :
    ∀ ω ∈ S, F ω ≤ R ω := by
  have hStnn : ∀ ρ : Mat d, IsPure ρ → 0 ≤ Stilde ρ := by
    rintro ρ ⟨ψ, hψ, rfl⟩
    unfold Stilde
    apply Finset.sum_nonneg
    intro j _
    have hjj : ((Matrix.vecMulVec ψ (star ψ)) j j).re = ‖ψ j‖ ^ 2 := by
      simp [Matrix.vecMulVec_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      norm_cast
    rw [hjj]
    apply Real.negMulLog_nonneg (by positivity)
    rw [← hψ]
    exact Finset.single_le_sum (f := fun i => ‖ψ i‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ j)
  have hRle : ∀ ρ : Mat d, IsPure ρ → R ρ ≤ Stilde ρ := by
    intro ρ hρ
    have hbdd : BddBelow {x : ℝ | ∃ (m : ℕ) (p : Fin m → ℝ) (ρ' : Fin m → Mat d),
        IsPureDecomp ρ p ρ' ∧ x = ∑ k, p k * Stilde (ρ' k)} := by
      refine ⟨0, ?_⟩
      rintro x ⟨m, p, ρ', ⟨hp, _, hpure', _⟩, rfl⟩
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (hp k).le (hStnn _ (hpure' k)))
    have hmem : Stilde ρ ∈ {x : ℝ | ∃ (m : ℕ) (p : Fin m → ℝ) (ρ' : Fin m → Mat d),
        IsPureDecomp ρ p ρ' ∧ x = ∑ k, p k * Stilde (ρ' k)} := by
      refine ⟨1, fun _ => 1, fun _ => ρ, ⟨fun _ => one_pos, by simp, fun _ => hρ, by simp⟩, by simp⟩
    exact csInf_le hbdd hmem
  intro ω hω
  obtain ⟨m, p, ρ, ⟨⟨hp, hsum, hpureρ, hdec⟩, hR⟩, hmem⟩ := hS.2.2 ω hω
  have hω' : ω = ∑ k, p k • ρ k := by
    rw [← hdec]
    apply Finset.sum_congr rfl
    intro k _
    exact Complex.coe_smul (p k) (ρ k)
  have J := hF.map_sum_le (t := Finset.univ) (w := p) (p := ρ) (fun k _ => (hp k).le) hsum
    (fun k _ => hmem k)
  rw [← hω'] at J
  calc F ω ≤ ∑ k, p k • F (ρ k) := J
    _ ≤ ∑ k, p k * Stilde (ρ k) := by
      apply Finset.sum_le_sum
      intro k _
      rw [smul_eq_mul]
      exact mul_le_mul_of_nonneg_left
        ((hpure _ (hmem k) (hpureρ k)).trans (hRle _ (hpureρ k))) (hp k).le
    _ = R ω := hR.symm
