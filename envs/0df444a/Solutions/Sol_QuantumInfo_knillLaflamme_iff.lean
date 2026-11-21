-- Prove2me | solution 1 for QuantumInfo.knillLaflamme_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:53:03.11914+00:00
-- url     : https://prove2.me/submissions/78fecac8-ff89-4ac2-8ce8-bfd0e26a06bb

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_exists_recovery_of_knillLaflamme
public import Theorems.Thm_QuantumInfo_knillLaflamme_of_recovery

set_option autoImplicit false
@[expose] public section
public section
open Matrix Unitary
open scoped ComplexOrder ComplexConjugate
open QuantumInfo
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} {c : Matrix ι ι ℂ}
namespace QuantumInfo
theorem _root_.solution (hP : IsCodeProjector P) (hP0 : P ≠ 0) :
    (∃ c : Matrix ι ι ℂ, KnillLaflamme P E c) ↔
      ∃ (R : Channel n n (Option ι)) (lam : ι → ℂ),
        ∀ i, ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (E i * ρ * (E i)ᴴ) = lam i • ρ := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨R, hR⟩ := exists_recovery_of_knillLaflamme hP hP0 hc
    exact ⟨R, fun i => c i i, fun i ρ hρ => hR ρ hρ i i⟩
  · rintro ⟨R, lam, h⟩
    exact knillLaflamme_of_recovery hP R lam h
end QuantumInfo
