-- Prove2me | solution 1 for TeschlQM.OneParticle.schroedinger_selfAdjoint
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-07T15:21:10.888272+00:00
-- url     : https://prove2.me/submissions/e4d035a6-8af6-4ee4-b682-45e315b256da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_multiplicationOperator
import Definitions.Def_TeschlQM_OneParticle_freeHamiltonian
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_OneParticle_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsRelativelyCompact
import Definitions.Def_TeschlQM_OneParticle_IsBoundedBelow
import Definitions.Def_TeschlQM_OneParticle_testFunctions
import Definitions.Def_TeschlQM_OneParticle_IsBoundedVanishingAtInfinity
import Theorems.Thm_TeschlQM_OneParticle_freeHamiltonian_selfAdjoint_core
import Theorems.Thm_TeschlQM_OneParticle_potential_relativelyCompact
import Theorems.Thm_TeschlQM_OneParticle_relativelyCompact_perturbation

open MeasureTheory TeschlQM.OneParticle
open scoped InnerProductSpace

namespace SAAux

variable {n : ℕ}

open ComplexConjugate in
lemma inner_pt (a b : ℂ) : ⟪a, b⟫_ℂ = conj a * b := by simp [mul_comm]

/-- Multiplication by a real-valued function is symmetric. -/
lemma multOp_real_symm (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (x y : (multOp (fun x => (V x : ℂ))).domain) :
    ⟪multOp (fun x => (V x : ℂ)) x, (y : L2 n)⟫_ℂ =
      ⟪(x : L2 n), multOp (fun x => (V x : ℂ)) y⟫_ℂ := by
  have hx : MemLp (fun z => (V z : ℂ) * (x : L2 n) z) 2 volume := x.2
  have hy : MemLp (fun z => (V z : ℂ) * (y : L2 n) z) 2 volume := y.2
  change ⟪hx.toLp _, (y : L2 n)⟫_ℂ = ⟪(x : L2 n), hy.toLp _⟫_ℂ
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hx.coeFn_toLp, hy.coeFn_toLp] with z h1 h2
  rw [inner_pt, inner_pt, h1, h2, map_mul, Complex.conj_ofReal]
  ring

/-- The free Schrödinger operator is nonnegative. -/
lemma freeHamiltonian_boundedBelow : IsBoundedBelow (freeHamiltonian n) := by
  refine ⟨0, fun ψ => ?_⟩
  rw [zero_mul]
  set G : L2 n := fourierL2 n ψ with hGdef
  have hS : MemLp (fun ξ => laplaceSymbol n ξ * G ξ) 2 volume := ψ.2
  have hH : freeHamiltonian n ψ = (fourierL2 n).symm (hS.toLp _) := rfl
  have hF : ⟪(ψ : L2 n), freeHamiltonian n ψ⟫_ℂ = ⟪G, hS.toLp _⟫_ℂ := by
    rw [hH, ← LinearIsometryEquiv.inner_map_map (fourierL2 n),
      LinearIsometryEquiv.apply_symm_apply]
  have hval : ⟪G, hS.toLp _⟫_ℂ =
      ((∫ ξ, (2 * Real.pi * ‖ξ‖) ^ 2 * ‖G ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [hS.coeFn_toLp] with x h
    rw [inner_pt, h]
    unfold laplaceSymbol
    rw [mul_left_comm, Complex.conj_mul']
    push_cast
    ring
  rw [hF, hval, Complex.ofReal_re]
  exact integral_nonneg fun ξ => by positivity

end SAAux

open SAAux in
theorem solution (n : ℕ) (hn : 1 ≤ n) (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hV_large : 3 < n → IsBoundedVanishingAtInfinity V)
    (hV_small : n ≤ 3 → ∃ V₁ V₂ : EuclideanSpace ℝ (Fin n) → ℝ,
      IsBoundedVanishingAtInfinity V₁ ∧ MemLp V₂ 2 volume ∧ V = V₁ + V₂) :
    TeschlQM.Shared.IsRelativelyCompact (multOp (fun x => (V x : ℂ))) (freeHamiltonian n) ∧
      (freeHamiltonian n + multOp (fun x => (V x : ℂ))).domain = sobolevH2 n ∧
      IsSelfAdjoint (freeHamiltonian n + multOp (fun x => (V x : ℂ))) ∧
      IsBoundedBelow (freeHamiltonian n + multOp (fun x => (V x : ℂ))) ∧
      essentialSpectrum (freeHamiltonian n + multOp (fun x => (V x : ℂ))) =
        (fun t : ℝ => (t : ℂ)) '' Set.Ici 0 ∧
      (freeHamiltonian n + multOp (fun x => (V x : ℂ))).HasCore (testFunctions n) := by
  obtain ⟨hsa, hess, hcore⟩ := freeHamiltonian_selfAdjoint_core n hn
  have hrc := potential_relativelyCompact n hn V hV_large hV_small
  obtain ⟨hdom, hsa', hbdd', hess', hcore'⟩ :=
    relativelyCompact_perturbation (freeHamiltonian n) (multOp (fun x => (V x : ℂ))) hsa
      freeHamiltonian_boundedBelow (multOp_real_symm V) hrc
  exact ⟨hrc, hdom, hsa', hbdd', hess'.trans hess, hcore' _ hcore⟩
