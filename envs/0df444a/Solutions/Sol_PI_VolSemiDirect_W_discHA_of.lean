-- Prove2me | solution 1 for PI.VolSemiDirect.W.discHA_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:25:27.166421+00:00
-- url     : https://prove2.me/submissions/d818461d-187e-42b8-8edc-e462851c8d84

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_EqZeroOfMemNbhdA
import Theorems.Thm_PI_VolSemiDirect_W_exists_nbhd_tens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
  IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct Matrix
namespace PI.VolSemiDirect.W
theorem _root_.solution (hT : TensTop) : DiscHA := by
  intro F E _ _ _ _ _ σ hCM M J _
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨h1, -, -, -⟩ := hT F E
  constructor
  · haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
    haveI : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
    haveI : Countable (GL (Fin M) E) :=
      (Units.val_injective (α := Matrix (Fin M) (Fin M) E)).countable
    have hS : (HFin (AF F) σ J : Set (GL (Fin M) (AF F ⊗[F] E))).Countable := by
      rw [HFin, Subgroup.coe_map]
      exact (Set.to_countable _).image _
    haveI : Countable (HFin (AF F) σ J) := hS.to_subtype
    let φ : HFinIn (AF F) σ J → HFin (AF F) σ J := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩
    have hφ : Function.Injective φ := by
      intro x y h
      simp only [φ, Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h)
    exact hφ.countable
  · obtain ⟨U, hUo, hU0, hUe⟩ := exists_nbhd_tens F E
    rw [discreteTopology_iff_isOpen_singleton]
    intro x
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 x.2)
    let V : Set (HR (AF F) σ J) := {g | ∀ i j,
      ((g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j -
        ((x.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j ∈ U}
    have hVo : IsOpen V := by
      have hc : Continuous fun g : HR (AF F) σ J =>
          ((g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :=
        Units.continuous_val.comp continuous_subtype_val
      have : V = ⋂ i, ⋂ j, (fun g : HR (AF F) σ J =>
          ((g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j -
            ((x.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j) ⁻¹' U := by
        ext g
        simp [V]
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hUo.preimage (((continuous_apply j).comp ((continuous_apply i).comp hc)).sub
          continuous_const)
    rw [isOpen_induced_iff]
    refine ⟨V, hVo, Set.ext fun y => ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hy
      obtain ⟨δ, -, hδ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 y.2)
      have hent : ∀ i j, (δ : Matrix (Fin M) (Fin M) E) i j = (γ : Matrix (Fin M) (Fin M) E) i j := by
        intro i j
        have h := hy i j
        rw [← hδ, ← hγ] at h
        have h' : inclR (F := F) (AF F) ((δ : Matrix (Fin M) (Fin M) E) i j -
            (γ : Matrix (Fin M) (Fin M) E) i j) ∈ U := by
          rw [map_sub]
          exact h
        exact sub_eq_zero.1 (hUe _ h')
      have hm : δ = γ := Units.ext (Matrix.ext hent)
      apply Subtype.ext
      apply Subtype.ext
      rw [← hδ, ← hγ, hm]
    · rintro rfl i j
      simp only [sub_self]
      exact hU0
end PI.VolSemiDirect.W
