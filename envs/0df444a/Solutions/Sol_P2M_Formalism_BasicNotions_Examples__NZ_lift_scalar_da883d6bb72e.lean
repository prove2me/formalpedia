-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_lift_scalar_da883d6bb72e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:10:01.281365+00:00
-- url     : https://prove2.me/submissions/8d64cdd0-24b8-478f-a45c-5cd07c9f367b

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeF
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_evS_eq_5f3a4c43d764

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
open MonoidAlgebra
attribute [local instance] Classical.propDecidable
variable {K : Type} [Field K]
variable {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
variable {L : I → Type} [∀ i, Fintype (L i)] (E : ∀ i, L i → MonoidAlgebra K (G i)) (S : (∀ i, L i) → Prop)
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {Γ V : Type} [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] (Ψ : Γ →* K)
    (F : Γ →* Module.End K V) (hF : ∀ g, F g = Ψ g • 1) (x : MonoidAlgebra K Γ) :
    MonoidAlgebra.lift K (Module.End K V) Γ F x = evS Ψ x • 1 := by
  have := Fintype.ofFinite Γ
  rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ (fun a b => b • F a) (fun _ => zero_smul _ _), evS_eq,
    Finset.sum_smul]
  exact Finset.sum_congr rfl fun g _ => by rw [hF, smul_smul]
end Formalism.BasicNotions.Examples₂.NZ
