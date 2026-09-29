-- Prove2me | solution 1 for UndecidableSpectralGap.usg_gs_energy_density
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T13:54:34.360443+00:00
-- url     : https://prove2.me/submissions/b7c818f6-af69-4c29-a47f-818f51702498

import Definitions.Def_usg_spectral_notions

set_option autoImplicit false
open scoped ComplexOrder

namespace UsgDensity

open UndecidableSpectralGap Matrix

lemma specReal_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) :
    specReal (Matrix.diagonal (fun i => ((E i : ℝ) : ℂ))) = Set.range E := by
  ext μ
  simp only [specReal, Set.mem_setOf_eq, spectrum_diagonal, Set.mem_range]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, by exact_mod_cast hi⟩
  · rintro ⟨i, hi⟩; exact ⟨i, by exact_mod_cast hi⟩

lemma gsEnergy_diag_const {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (v : ℝ) :
    gsEnergy (Matrix.diagonal (fun _ : ι => ((v : ℝ) : ℂ))) = v := by
  unfold gsEnergy
  have hs : specReal (Matrix.diagonal (fun _ : ι => ((v : ℝ) : ℂ))) = {v} := by
    rw [specReal_diagonal (fun _ : ι => v)]
    exact Set.range_const
  rw [hs, csInf_singleton]

/-- With a one-dimensional local Hilbert space and no two-body terms, the lattice
Hamiltonian is the scalar `L² · (h₁)₀₀`. -/
lemma latticeHam_onsite {L : ℕ} (A : Matrix (Fin 1) (Fin 1) ℂ) :
    latticeHam L 1 A 0 0
      = Matrix.diagonal (fun _ : Config L 1 => ((L : ℂ) ^ 2 * A 0 0)) := by
  ext c c'
  have hsub : c = c' := Subsingleton.elim c c'
  subst hsub
  have hrow : (∑ e ∈ rowEdges L, embedTwo e.1 e.2 (0 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ))
      c c = 0 := by
    rw [Matrix.sum_apply]
    exact Finset.sum_eq_zero fun e _ => by simp [embedTwo]
  have hcol : (∑ e ∈ colEdges L, embedTwo e.1 e.2 (0 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ))
      c c = 0 := by
    rw [Matrix.sum_apply]
    exact Finset.sum_eq_zero fun e _ => by simp [embedTwo]
  have hone : (∑ p : Site L, embedOne p A) c c = (L : ℂ) ^ 2 * A 0 0 := by
    rw [Matrix.sum_apply]
    have hterm : ∀ p : Site L, embedOne p A c c = A 0 0 := by
      intro p
      have : c p = 0 := Subsingleton.elim _ _
      simp [embedOne, this]
    rw [Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_const, Finset.card_univ]
    simp [Fintype.card_prod, pow_two]
  simp only [latticeHam, Matrix.add_apply, hrow, hcol, hone, Matrix.diagonal_apply_eq]
  ring

lemma opNorm_one_le : opNorm (1 : Matrix (Fin 1) (Fin 1) ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

lemma opNorm_zero_eq {ι : Type*} [Fintype ι] [DecidableEq ι] :
    opNorm (0 : Matrix ι ι ℂ) = 0 := by
  unfold opNorm
  rw [map_zero, norm_zero]

end UsgDensity

open UndecidableSpectralGap UsgDensity Matrix

open scoped Classical in
/-- **Theorem 5 of Cubitt–Pérez-García–Wolf: undecidability of the ground state energy
density.** -/
theorem solution (u : Nat.Partrec.Code) :
    ∃ (d : ℕ) (h1 : ℕ → Matrix (Fin d) (Fin d) ℂ)
      (hrow hcol : ℕ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
      (∀ n : ℕ,
        (h1 n).IsHermitian ∧ (hrow n).IsHermitian ∧ (hcol n).IsHermitian ∧
        (∀ i j, IsAlgebraic ℚ ((h1 n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hrow n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hcol n) i j)) ∧
        localInteractionStrength (h1 n) (hrow n) (hcol n) ≤ 1) ∧
      ∀ n : ℕ, ∃ E : ℝ,
        HasGsEnergyDensity d (h1 n) (hrow n) (hcol n) E ∧ 0 ≤ E ∧
        (E = 0 ↔ ¬ (u.eval n).Dom) := by
  refine ⟨1, fun n => if (u.eval n).Dom then 1 else 0, fun _ => 0, fun _ => 0, ?_, ?_⟩
  · intro n
    dsimp only
    refine ⟨?_, Matrix.isHermitian_zero, Matrix.isHermitian_zero, ?_, ?_, ?_, ?_⟩
    · split_ifs
      · exact Matrix.isHermitian_one
      · exact Matrix.isHermitian_zero
    · intro i j
      split_ifs
      · rw [Matrix.one_apply]
        split_ifs
        · exact isAlgebraic_one
        · exact isAlgebraic_zero
      · simpa using isAlgebraic_zero
    · intro i j; simpa using isAlgebraic_zero
    · intro i j; simpa using isAlgebraic_zero
    · unfold localInteractionStrength
      rw [opNorm_zero_eq]
      refine max_le ?_ (by norm_num)
      split_ifs
      · exact opNorm_one_le
      · rw [opNorm_zero_eq]; norm_num
  · intro n
    dsimp only
    refine ⟨if (u.eval n).Dom then 1 else 0, ?_, ?_, ?_⟩
    · unfold HasGsEnergyDensity
      have hval : ∀ L : ℕ,
          gsEnergy (latticeHam L 1 (if (u.eval n).Dom then 1 else 0) 0 0)
            = (L : ℝ) ^ 2 * (if (u.eval n).Dom then 1 else 0) := by
        intro L
        rw [latticeHam_onsite]
        have hAentry : ((if (u.eval n).Dom then (1 : Matrix (Fin 1) (Fin 1) ℂ) else 0) 0 0)
            = ((if (u.eval n).Dom then (1:ℝ) else 0 : ℝ) : ℂ) := by
          split_ifs <;> simp
        rw [hAentry]
        have : (fun _ : Config L 1 => (L : ℂ) ^ 2 * ((if (u.eval n).Dom then (1:ℝ) else 0 : ℝ) : ℂ))
            = fun _ : Config L 1 =>
              ((((L : ℝ) ^ 2 * (if (u.eval n).Dom then (1:ℝ) else 0)) : ℝ) : ℂ) := by
          funext _
          push_cast
          ring
        rw [this, gsEnergy_diag_const]
      have heq : ∀ L : ℕ, 1 ≤ L →
          gsEnergy (latticeHam L 1 (if (u.eval n).Dom then 1 else 0) 0 0) / (L : ℝ) ^ 2
            = (if (u.eval n).Dom then 1 else 0 : ℝ) := by
        intro L hL
        rw [hval L]
        have hL0 : ((L : ℝ)) ≠ 0 := by
          have : (0:ℝ) < L := by exact_mod_cast hL
          linarith
        field_simp
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_ge_atTop 1] with L hL
      exact (heq L hL).symm
    · split_ifs <;> norm_num
    · split_ifs with h
      · simp [h]
      · simp [h]
