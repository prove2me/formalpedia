-- Prove2me | solution 1 for ValuationRing.exists_ne_zero_forall_smul_eq_zero_of_module_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/cc38e286-024a-5dfb-aa50-81a9c5d08f38

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationRing_exists_ne_zero_forall_smul_eq_zero_of_module_finite

open Submodule

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ a : R, a ≠ 0 ∧ ∀ m : M, (∃ c : R, c ≠ 0 ∧ c • m = 0) → a • m = 0 := by
  classical

  set T : Submodule R M := torsion R M with hT
  haveI : Module.Finite R (M ⧸ T) := inferInstance
  haveI : Module.Flat R (M ⧸ T) :=
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).mpr (Submodule.QuotientTorsion.torsion_eq_bot)
  haveI : Module.Free R (M ⧸ T) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Projective R (M ⧸ T) := Module.Projective.of_free

  obtain ⟨s, hs⟩ := Module.projective_lifting_property T.mkQ (LinearMap.id : M ⧸ T →ₗ[R] M ⧸ T)
    (Submodule.mkQ_surjective T)

  set φ : M →ₗ[R] M := LinearMap.id - s ∘ₗ T.mkQ with hφ
  have hrange : LinearMap.range φ = T := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      have : T.mkQ (φ m) = 0 := by
        have h1 : T.mkQ (s (T.mkQ m)) = T.mkQ m := by
          have := LinearMap.congr_fun hs (T.mkQ m)
          simpa using this
        simp only [Submodule.mkQ_apply] at h1
        simp only [hφ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_sub, h1, sub_self]
      simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using this
    · intro t ht
      refine ⟨t, ?_⟩
      have : T.mkQ t = 0 := by simpa [Submodule.Quotient.mk_eq_zero] using ht
      simp [hφ, this]
  haveI hTfin : Module.Finite R T := by
    rw [← hrange]
    exact Module.Finite.range φ

  have hTtors : Module.IsTorsion R T := by
    intro t
    obtain ⟨c, hc⟩ := (mem_torsion_iff (t : M)).mp t.2
    exact ⟨c, Subtype.ext (by simpa using hc)⟩
  obtain ⟨a, ha, ha0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hTtors
  refine ⟨a, nonZeroDivisors.ne_zero ha0, fun m hm => ?_⟩
  obtain ⟨c, hc0, hcm⟩ := hm
  have hmT : m ∈ T := (mem_torsion_iff m).mpr ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc0⟩, hcm⟩
  have := Submodule.mem_annihilator.mp ha ⟨m, hmT⟩ Submodule.mem_top
  simpa using congrArg Subtype.val this

end S_ValuationRing_exists_ne_zero_forall_smul_eq_zero_of_module_finite
end P2MW
export P2MW.S_ValuationRing_exists_ne_zero_forall_smul_eq_zero_of_module_finite (solution)
