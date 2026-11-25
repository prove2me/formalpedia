-- Prove2me | solution 1 for P2M_GlobalTheory_CoeffExt_finrank_fun__0788e41184fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:50:15.873122+00:00
-- url     : https://prove2.me/submissions/499f8a7d-3854-487e-a544-643722f905b2

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffExt
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module LL' V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V']
    {ρ : Representation LL G V} {ρ' : Representation LL' G V'}
    {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[LL] (ι → V)}
namespace GlobalTheory.CoeffExt
theorem _root_.solution {F M : Type} [Field F] [AddCommGroup M] [Module F M] (ι : Type) [Fintype ι] :
    finrank F (ι → M) = Fintype.card ι * finrank F M := by
  by_cases hM : Module.Finite F M
  · simp [Module.finrank_pi_fintype]
  · rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
    · rw [Module.finrank_zero_of_subsingleton]
      simp
    ·
      have hnot : ¬ Module.Finite F (ι → M) := fun h =>
        hM (Module.Finite.of_surjective (LinearMap.proj i : (ι → M) →ₗ[F] M)
          (fun m => ⟨fun _ => m, rfl⟩))
      rw [Module.finrank_of_not_finite hnot, Module.finrank_of_not_finite hM, mul_zero]
end GlobalTheory.CoeffExt
