-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_basis_of_basis_e9a25ae5a81f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:32:22.305779+00:00
-- url     : https://prove2.me/submissions/cbfc047f-c48f-4a4c-b5c4-a9c37de16e0c

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA

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
open NumberField IsDedekindDomain Formalism.BasicNotions
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {K W M ι κ : Type} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup M]
    [Module ℂ M] [Fintype ι] [Fintype κ] (σ : K →+* ℂ) (e : W →ₛₗ[σ] M)
    (b : Module.Basis ι K W)
    (hb : LinearIndependent ℂ (fun i => e (b i)) ∧ Submodule.span ℂ (Set.range fun i => e (b i)) = ⊤)
    (b' : Module.Basis κ K W) :
    LinearIndependent ℂ (fun i => e (b' i)) ∧ Submodule.span ℂ (Set.range fun i => e (b' i)) = ⊤ := by
  have hexp : ∀ (c : Module.Basis ι K W) (x : W), e x = ∑ i, σ (c.repr x i) • e (c i) := fun c x => by
    conv_lhs => rw [← c.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.map_smulₛₗ e _ _
  have hexp' : ∀ x : W, e x = ∑ i, σ (b'.repr x i) • e (b' i) := fun x => by
    conv_lhs => rw [← b'.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.map_smulₛₗ e _ _
  have hspan : Submodule.span ℂ (Set.range fun i => e (b' i)) = ⊤ := by
    rw [eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show e (b i) ∈ _
    rw [hexp' (b i)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨?_, hspan⟩
  have hcard : Fintype.card κ = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis b', ← Module.finrank_eq_card_basis b]
  let B : Module.Basis ι ℂ M := Module.Basis.mk hb.1 hb.2.ge
  have hfin : Module.finrank ℂ M = Fintype.card κ := by
    rw [Module.finrank_eq_card_basis B, hcard]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge hfin.symm
end Formalism.BasicNotions.Examples₂.NZ
