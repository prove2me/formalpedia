-- Prove2me | solution 1 for PI.VolStabW.testNear_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:09:51.58292+00:00
-- url     : https://prove2.me/submissions/07c92625-7abc-4500-9e85-4a7e05f55208

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_ReciprocityTheory_GeneralLinearIntegers_AlgebraMapIntMemOint
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_crd_map
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_crd_incl
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_continuous_crd
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_isSB_latV
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_exists_int_basis
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_continuous_orbit
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_continuous_projInf
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_continuous_projFin
import Theorems.Thm_ReciprocityTheory_GeneralLinearIntegers_GeneralLinearIntegersOpenCompact_algebraMap_int_mem_Oint
import Theorems.Thm_ReciprocityTheory_GeneralLinearIntegers_GeneralLinearIntegersOpenCompact_isOpen_Oint


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
open PositiveNearLattice
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution : TestNear := by
  intro F E _ _ _ _ _ σ hE M J _hJ _ha _hc a _ha1 _ha2 X0 _hT _hdet
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  obtain ⟨d, b, hb⟩ := exists_int_basis (F := F) X0
  obtain ⟨fi, hfc, hf0, hfx⟩ := exists_continuous_nonneg_pos (projInf (ratTup (AF F) X0))
  let ind : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℝ :=
    fun v => (latV b v).indicator (fun _ => (1 : ℝ))
  let φ : (Fin a → Fin M → AF F ⊗[F] E) → ℝ :=
    fun X => fi (projInf X) * ∏ᶠ v, ind v (projV v (projFin X))
  have hφ0 : ∀ X, 0 ≤ φ X := fun X =>
    mul_nonneg (hf0 _) (finprod_nonneg fun v => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hcast : ∀ v (Y : Fin a → Fin M → Fv F v ⊗[F] E),
      ((ind v Y : ℝ) : ℂ) = (latV b v).indicator (fun _ => (1 : ℂ)) Y := by
    intro v Y
    by_cases h : Y ∈ latV b v <;> simp [ind, h]
  have hadm : IsAdm F E (fun X => (φ X : ℂ)) := by
    refine ⟨d, b, fun Y => (fi Y : ℂ),
      fun Y => ∏ᶠ v, (latV b v).indicator (fun _ => (1 : ℂ)) (projV v Y),
      fun v => (latV b v).indicator (fun _ => (1 : ℂ)),
      Complex.continuous_ofReal.comp fi.continuous, hfc.comp_left Complex.ofReal_zero,
      ⟨fun v => isSB_latV b v a M, Filter.Eventually.of_forall fun v => rfl, fun X => rfl⟩,
      fun X => ?_⟩
    simp only [φ, Complex.ofReal_mul, ← hcast]
    congr 1
    exact Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective _
  let U : Set (HA (AF F) σ J) := {g | 0 < fi (projInf (g • ratTup (AF F) X0))} ∩
    ⋂ x, ⋂ i, ⋂ k, (fun g : HA (AF F) σ J =>
      crd b (Af F) (projFin (g • ratTup (AF F) X0) x i) k) ⁻¹' ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.Oint F
  have horb := continuous_orbit σ J (ratTup (AF F) X0)
  refine ⟨φ, hφ0, hadm, U, ?_, ⟨1, ?_⟩, ?_⟩
  · refine (isOpen_lt continuous_const
      (fi.continuous.comp ((continuous_projInf b).comp horb))).inter ?_
    refine isOpen_iInter_of_finite fun x => isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun k => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_Oint.preimage ?_
    have hpf : Continuous fun g : HA (AF F) σ J => projFin (g • ratTup (AF F) X0) :=
      (continuous_projFin b).comp horb
    exact (continuous_crd b (Af F) k).comp ((continuous_apply i).comp ((continuous_apply x).comp hpf))
  · refine ⟨?_, ?_⟩
    · show 0 < fi (projInf ((1 : HA (AF F) σ J) • ratTup (AF F) X0))
      rw [one_smul]
      exact lt_of_le_of_ne (hf0 _) (Ne.symm hfx)
    · simp only [Set.mem_iInter, Set.mem_preimage, one_smul]
      intro x i k
      obtain ⟨m, hm⟩ := hb x i k
      have e : crd b (Af F) (projFin (ratTup (AF F) X0) x i) k = algebraMap F (Af F) (m : F) := by
        simp only [projFin, ratTup, crd_map, crd_incl, AlgHom.commutes, hm]
      rw [e]
      exact ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.algebraMap_int_mem_Oint m
  · rintro g ⟨h1, h2⟩
    simp only [Set.mem_iInter, Set.mem_preimage] at h2
    have hone : ∀ v, ind v (projV v (projFin (g • ratTup (AF F) X0))) = 1 := by
      intro v
      refine Set.indicator_of_mem ?_ _
      intro x i k
      have e : (Algebra.TensorProduct.basis (Fv F v) b).repr
          (projV v (projFin (g • ratTup (AF F) X0)) x i) k =
          evalV F v (crd b (Af F) (projFin (g • ratTup (AF F) X0) x i) k) := by
        rw [← crd_map]
        rfl
      rw [e]
      exact h2 x i k v
    show 0 < fi (projInf (g • ratTup (AF F) X0)) *
      ∏ᶠ v, ind v (projV v (projFin (g • ratTup (AF F) X0)))
    simp only [hone, finprod_one, mul_one]
    exact h1
end PI.VolStabW
