-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.fg_of_den
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:43.926358+00:00
-- url     : https://prove2.me/submissions/e60728e8-2a0f-4fbb-9c17-396e7340ebeb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_ClassFiniteOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermSingleLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.HermLatFin
variable {E : Type} [Field E] {M : ℕ} (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E)
variable [NumberField E]
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (N : Submodule (𝓞 E) (Fin M → E)) (d : ℕ) (hd : 0 < d)
    (h : ∀ y ∈ N, ∀ j, IsIntegral ℤ ((d : E) * y j)) : N.FG := by
  classical

  let f : (Fin M → 𝓞 E) →ₗ[𝓞 E] (Fin M → E) :=
    LinearMap.pi fun j => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj j)
  let sc : (Fin M → E) →ₗ[𝓞 E] (Fin M → E) := (d : 𝓞 E) • LinearMap.id
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  have hsc : ∀ y : Fin M → E, ∀ j, sc y j = (d : E) * y j := by
    intro y j
    simp [sc, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  have hinj : Function.Injective sc := by
    intro x y hxy
    funext j
    have := congrFun hxy j
    rw [hsc, hsc] at this
    exact mul_left_cancel₀ hd' this
  have hle : N.map sc ≤ LinearMap.range f := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨fun j => ⟨(d : E) * y j, h y hy j⟩, ?_⟩
    funext j
    rw [hsc]
    rfl
  have hfg : (N.map sc).FG := by
    rw [← Submodule.map_comap_eq_of_le hle]
    exact (IsNoetherian.noetherian _).map f
  exact Submodule.fg_of_fg_map_injective sc hinj hfg
end PI.UnitaryGroupMassFormula.UJClassFin
