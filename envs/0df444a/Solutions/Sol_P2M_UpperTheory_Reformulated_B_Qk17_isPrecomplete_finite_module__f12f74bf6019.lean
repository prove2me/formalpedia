-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:23:53.890139+00:00
-- url     : https://prove2.me/submissions/97bbd94e-8b46-4647-a353-bc2a276e395f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPrecompleteFiniteModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Qk17.pi_precomplete {R : Type*} [CommRing R] (I : Ideal R)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ι → Type*) [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] [∀ i, IsPrecomplete I (N i)] : IsPrecomplete I (∀ i, N i) := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  choose r hr using fun j : ι =>
    AdicCompletion.of_surjective I (N j) (AdicCompletion.pi I N y j)
  refine ⟨r, (AdicCompletion.piEquivOfFintype I N).injective ?_⟩
  rw [AdicCompletion.piEquivOfFintype_apply, AdicCompletion.piEquivOfFintype_apply]
  funext j
  rw [← hr j]
  exact AdicCompletion.map_of I (LinearMap.proj (R := R) (φ := N) j) r
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module
theorem _root_.solution.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) [IsAdicComplete I R] (M : Type u_2)
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] [Module.Finite R M], IsPrecomplete I M := by
  intro R _ I _ M _ _ _
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have := UpperTheory.Reformulated.B.Qk17.pi_precomplete I (fun _ : Fin n => R)
  rw [← AdicCompletion.of_surjective_iff]
  intro x
  obtain ⟨y, rfl⟩ := AdicCompletion.map_surjective I hf x
  obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective I (Fin n → R) y
  exact ⟨f r, (AdicCompletion.map_of I f r).symm⟩
end UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module
