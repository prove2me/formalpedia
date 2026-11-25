-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LocF_padicCharacter_spec_bf1743de53a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:32:41.11521+00:00
-- url     : https://prove2.me/submissions/928298a5-6670-43a6-b94a-98fcd07022fa

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LocF
open NumberField IsDedekindDomain HeightOneSpectrum WithZero
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable (l : ℕ) [hl : Fact l.Prime] (hv : (l : 𝓞 F) ∈ v.asIdeal)
namespace Formalism.BasicNotions.Examples₂.LocF
theorem _root_.solution (x : ℚ_[l]) : ∃ a : ℚ, (∃ n : ℕ, a.den = l ^ n) ∧ ‖x - (a : ℚ_[l])‖ ≤ 1 ∧
    psi0 l x = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) :=
  ⟨frac l x, (exists_frac l x).choose_spec.1, (exists_frac l x).choose_spec.2, rfl⟩
end Formalism.BasicNotions.Examples₂.LocF
