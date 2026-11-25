-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_exists_char_2fc1fe4faba6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:39:03.703892+00:00
-- url     : https://prove2.me/submissions/d6739c8f-a285-4510-bf96-9c42236aa5ad

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_char_comm_1817172480b3

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
variable {k : Type} [Field k] {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
variable {L : I → Type} [∀ i, Fintype (L i)] [DecidableEq I] (E : ∀ i, L i → MonoidAlgebra k (G i))
  (S : (∀ i, L i) → Prop)
variable (hidem : ∀ i l, E i l * E i l = E i l) (hcen : ∀ i l a, E i l * a = a * E i l)
  (horth : ∀ i l l', l ≠ l' → E i l * E i l' = 0)
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {Γ : Type} [Group Γ] [Finite Γ] (e : MonoidAlgebra ℂ Γ)
    (hc : e ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ Γ)) (hi : e * e = e) (h0 : e ≠ 0) :
    ∃ ω : Subalgebra.center ℂ (MonoidAlgebra ℂ Γ) →ₐ[ℂ] ℂ, ω ⟨e, hc⟩ = 1 := by
  have hfd : FiniteDimensional ℂ (MonoidAlgebra ℂ Γ) :=
    Module.Finite.equiv (MonoidAlgebra.coeffLinearEquiv ℂ).symm
  exact exists_char_comm _ ⟨e, hc⟩ (Subtype.ext hi) (fun h => h0 (congrArg Subtype.val h))
end Formalism.BasicNotions.Examples₂.NZ
