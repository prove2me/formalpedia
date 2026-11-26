-- Prove2me | solution 1 for OpenQuantumProblem35.hasMaximallyMixedFirstReduction_of_completion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:36.137939+00:00
-- url     : https://prove2.me/submissions/1452f9ce-f4e1-4725-b9b6-9e9829b1666c

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_reducedDensityFirst_of_completion

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution
    {n d m : ℕ} (hm : m ≤ n)
    (ψ : StateVector n d)
    (completion : Config m d → Config (n - m) d)
    (coeff : ℂ)
    (hψ : ∀ x z,
      ψ (combineFirst (n := n) (d := d) m hm x z) = if z = completion x then coeff else 0)
    (hinj : Function.Injective completion)
    (hnorm : coeff * star coeff = ((Fintype.card (Config m d) : ℂ)⁻¹)) :
    HasMaximallyMixedFirstReduction (n := n) (d := d) m hm ψ := by
  rw [HasMaximallyMixedFirstReduction]
  rw [reducedDensityFirst_of_completion hm ψ completion coeff hψ hinj]
  rw [maximallyMixed, hnorm]
end OpenQuantumProblem35
