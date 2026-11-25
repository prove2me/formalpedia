-- Prove2me | solution 1 for PI.VolStabW.cm_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:58:21.76165+00:00
-- url     : https://prove2.me/submissions/f1053c41-3ec4-46b7-a290-713e83d758de

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_OrbRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_HformSmulLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_InclRAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_LocalSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StFix
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_ExistsOrthogonalFamily
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_OrbTupFin

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix Formalism.UG PI.VolStabW.OrbR
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (a : E) : σ a = a ↔ a ∈ (algebraMap F E).range := by
  constructor
  · intro ha
    by_contra hn
    have hli : LinearIndependent F ![(1 : E), a] := by
      rw [LinearIndependent.pair_iff]
      intro p q hpq
      by_cases hq : q = 0
      · subst hq
        simp only [zero_smul, add_zero] at hpq
        exact ⟨by simpa using hpq, rfl⟩
      · exfalso
        apply hn
        refine ⟨-(p / q), ?_⟩
        have e : q • a = -(p • (1 : E)) := by linear_combination hpq
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at e
        have hq' : algebraMap F E q ≠ 0 := by simpa using hq
        rw [map_neg, map_div₀]
        field_simp
        linear_combination -e
    have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [h.2.2.1]; rfl
    let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hid : σ.toLinearMap = LinearMap.id := by
      refine b.ext fun i => ?_
      fin_cases i
      · simp [b]
      · simp [b, ha]
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    have hreal : ComplexEmbedding.IsReal τ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq]
      have e1 := h.2.2.2 τ x
      have e2 : σ x = x := by
        have := congrArg (fun f : E →ₗ[F] E => f x) hid
        simpa using this
      rw [e2] at e1
      rw [starRingEnd_apply, ← e1]
    have hc := h.2.1.isComplex (InfinitePlace.mk τ)
    exact (InfinitePlace.not_isComplex_iff_isReal.mpr ⟨τ, hreal, rfl⟩) hc
  · rintro ⟨b, rfl⟩; exact σ.commutes b
end PI.VolStabW
