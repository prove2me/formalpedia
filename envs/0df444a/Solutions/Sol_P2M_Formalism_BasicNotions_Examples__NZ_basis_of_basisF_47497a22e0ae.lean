-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_basis_of_basisF_47497a22e0ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:32:41.959814+00:00
-- url     : https://prove2.me/submissions/fdfed77c-a1d9-40ea-9bbd-27f10cb262d5

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_BasisOfBasisF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open scoped TensorProduct nonZeroDivisors
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {K F W M ι κ : Type} [Field K] [Field F] [AddCommGroup W] [Module K W] [AddCommGroup M]
    [Module F M] [Fintype ι] [Fintype κ] (σ : K →+* F) (e : W →ₛₗ[σ] M)
    (b : Module.Basis ι K W)
    (hb : LinearIndependent F (fun i => e (b i)) ∧ Submodule.span F (Set.range fun i => e (b i)) = ⊤)
    (b' : Module.Basis κ K W) :
    LinearIndependent F (fun i => e (b' i)) ∧ Submodule.span F (Set.range fun i => e (b' i)) = ⊤ := by
  have hexp' : ∀ x : W, e x = ∑ i, σ (b'.repr x i) • e (b' i) := fun x => by
    conv_lhs => rw [← b'.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.map_smulₛₗ e _ _
  have hspan : Submodule.span F (Set.range fun i => e (b' i)) = ⊤ := by
    rw [eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show e (b i) ∈ _
    rw [hexp' (b i)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨?_, hspan⟩
  have hcard : Fintype.card κ = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis b', ← Module.finrank_eq_card_basis b]
  let B : Module.Basis ι F M := Module.Basis.mk hb.1 hb.2.ge
  have hfin : Module.finrank F M = Fintype.card κ := by
    rw [Module.finrank_eq_card_basis B, hcard]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge hfin.symm
end Formalism.BasicNotions.Examples₂.NZ
