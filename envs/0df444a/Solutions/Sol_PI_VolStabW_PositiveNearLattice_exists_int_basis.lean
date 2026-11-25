-- Prove2me | solution 1 for PI.VolStabW.PositiveNearLattice.exists_int_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:06:27.209887+00:00
-- url     : https://prove2.me/submissions/b7d8c92b-bdb7-471e-ba32-43a94b6b39d2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_ReciprocityTheory_GeneralLinearIntegers_AlgebraMapIntMemOint
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.PositiveNearLattice
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace PI.VolStabW.PositiveNearLattice
theorem _root_.solution [FiniteDimensional F E] {a M : ℕ} (X0 : Fin a → Fin M → E) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ x i k, ∃ m : 𝓞 F, (m : F) = b.repr (X0 x i) k := by
  classical
  let b0 := Module.finBasis F E
  let s : Finset F := Finset.univ.image
    (fun p : Fin a × Fin M × Fin (Module.finrank F E) => b0.repr (X0 p.1 p.2.1) p.2.2)
  obtain ⟨⟨β, hβ⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F)) s
  have hβ0 : (β : F) ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hβ (RingOfIntegers.coe_eq_zero_iff.1 h)
  let u : Fin (Module.finrank F E) → Fˣ := fun _ => (Units.mk0 (β : F) hβ0)⁻¹
  refine ⟨_, b0.unitsSMul u, fun x i k => ?_⟩
  rw [Module.Basis.repr_unitsSMul]
  obtain ⟨m, hm⟩ := hint _ (Finset.mem_image.2 ⟨(x, i, k), Finset.mem_univ _, rfl⟩)
  refine ⟨m, ?_⟩
  simp only [u, inv_inv, Units.smul_def, Units.val_mk0, smul_eq_mul]
  rw [Algebra.smul_def] at hm
  exact hm
end PI.VolStabW.PositiveNearLattice
