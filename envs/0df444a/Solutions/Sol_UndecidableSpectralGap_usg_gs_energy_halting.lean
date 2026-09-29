-- Prove2me | solution 1 for UndecidableSpectralGap.usg_gs_energy_halting
-- status  : ACCEPTED   (disprove)
-- author  : @Lucas
-- created : 2026-09-14T10:55:48.10063+00:00
-- url     : https://prove2.me/submissions/edf15ffe-5fcc-40ea-a53c-4eab716365e3

import Definitions.Def_usg_spectral_notions

set_option autoImplicit false
open scoped ComplexOrder

open UndecidableSpectralGap

namespace UsgGsEnergyHaltingDisproof

/-- On a `1 × 1` lattice there are no horizontal edges. -/
theorem rowEdges_one_eq_empty : rowEdges 1 = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  rintro e he
  simp only [rowEdges, Finset.mem_filter] at he
  have h1 : ((e.2.2 : Fin 1) : ℕ) < 1 := e.2.2.isLt
  omega

/-- On a `1 × 1` lattice there are no vertical edges. -/
theorem colEdges_one_eq_empty : colEdges 1 = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  rintro e he
  simp only [colEdges, Finset.mem_filter] at he
  have h1 : ((e.2.1 : Fin 1) : ℕ) < 1 := e.2.1.isLt
  omega

/-- Embedding the zero on-site term gives the zero matrix. -/
theorem embedOne_zero {L d : ℕ} (p : Site L) :
    embedOne (d := d) p (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
  funext c c'
  simp [embedOne]

/-- With no on-site term, the Hamiltonian on the `1 × 1` lattice is the zero matrix:
the lattice has a single site, hence no nearest-neighbour pairs. -/
theorem latticeHam_one_eq_zero (d : ℕ)
    (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    latticeHam 1 d 0 hrow hcol = 0 := by
  simp [latticeHam, rowEdges_one_eq_empty, colEdges_one_eq_empty, embedOne_zero]

/-- Zero is the only possible spectral point of the zero matrix. -/
theorem specReal_zero_subset {n : Type} [Fintype n] [DecidableEq n] :
    specReal (0 : Matrix n n ℂ) ⊆ {0} := by
  intro μ hμ
  by_contra hne
  have hμ0 : (μ : ℂ) ≠ 0 := by
    simpa [Complex.ofReal_eq_zero] using (by simpa using hne : μ ≠ 0)
  have hmem : (μ : ℂ) ∈ spectrum ℂ (0 : Matrix n n ℂ) := hμ
  rw [spectrum.mem_iff] at hmem
  exact hmem (by
    simpa using (isUnit_iff_ne_zero.mpr hμ0).map (algebraMap ℂ (Matrix n n ℂ)))

/-- The ground state energy of the zero matrix is `0`: its real spectrum is either empty
(in the degenerate case of an empty index type) or `{0}`, and `sInf` is `0` in both cases. -/
theorem gsEnergy_zero {n : Type} [Fintype n] [DecidableEq n] :
    gsEnergy (0 : Matrix n n ℂ) = 0 := by
  rcases Set.subset_singleton_iff_eq.mp (specReal_zero_subset (n := n)) with h | h
  · simp [gsEnergy, h]
  · simp [gsEnergy, h]

/-- A concrete code whose step-bounded evaluation with fuel `1` on input `0` is undefined:
composing the successor function with itself needs two steps. -/
theorem evaln_one_comp_succ_succ :
    (Nat.Partrec.Code.evaln 1 (Nat.Partrec.Code.comp Nat.Partrec.Code.succ
      Nat.Partrec.Code.succ) 0).isNone = true := by
  simp [Nat.Partrec.Code.evaln]

/-- **Disproof of Lemma 8 as stated.** For `L = 1` the lattice `Λ(1)` consists of a single
site, so with no on-site term the Hamiltonian `H^{Λ(1)}` is the zero matrix and its ground
state energy is `0`, not `-2` — while clause (i) is applicable, since there are codes that
have not halted after one step. -/
theorem disproof : ¬ (∀ (c : Nat.Partrec.Code),
    ∃ (d : ℕ) (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
      hrow.IsHermitian ∧ hcol.IsHermitian ∧
      (∀ L : ℕ, 0 < L → (Nat.Partrec.Code.evaln L c 0).isNone = true →
        gsEnergy (latticeHam L d 0 hrow hcol) = -2 ∧
        GroundStateNondegenerate (latticeHam L d 0 hrow hcol) ∧
        (∀ μ ∈ specReal (latticeHam L d 0 hrow hcol), μ < 0 → μ = -2) ∧
        ∃ v : Fin d → ℂ, v ≠ 0 ∧
          (latticeHam L d 0 hrow hcol).mulVec (fun cfg : Config L d => ∏ s, v (cfg s))
            = (-2 : ℂ) • (fun cfg : Config L d => ∏ s, v (cfg s))) ∧
      ((c.eval 0).Dom → ∃ L0 : ℕ, ∀ L > L0, gsEnergy (latticeHam L d 0 hrow hcol) = 0)) := by
  intro h
  obtain ⟨d, hrow, hcol, -, -, hi, -⟩ :=
    h (Nat.Partrec.Code.comp Nat.Partrec.Code.succ Nat.Partrec.Code.succ)
  have hgs := (hi 1 Nat.one_pos evaln_one_comp_succ_succ).1
  rw [latticeHam_one_eq_zero, gsEnergy_zero] at hgs
  norm_num at hgs

end UsgGsEnergyHaltingDisproof

theorem solution : ¬ (∀ (c : Nat.Partrec.Code),
    ∃ (d : ℕ) (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
      hrow.IsHermitian ∧ hcol.IsHermitian ∧
      (∀ L : ℕ, 0 < L → (Nat.Partrec.Code.evaln L c 0).isNone = true →
        gsEnergy (latticeHam L d 0 hrow hcol) = -2 ∧
        GroundStateNondegenerate (latticeHam L d 0 hrow hcol) ∧
        (∀ μ ∈ specReal (latticeHam L d 0 hrow hcol), μ < 0 → μ = -2) ∧
        ∃ v : Fin d → ℂ, v ≠ 0 ∧
          (latticeHam L d 0 hrow hcol).mulVec (fun cfg : Config L d => ∏ s, v (cfg s))
            = (-2 : ℂ) • (fun cfg : Config L d => ∏ s, v (cfg s))) ∧
      ((c.eval 0).Dom → ∃ L0 : ℕ, ∀ L > L0, gsEnergy (latticeHam L d 0 hrow hcol) = 0)) :=
  UsgGsEnergyHaltingDisproof.disproof
