-- Prove2me | solution 1 for P2M_Formalism_L2_DIV_tpWild_proof__5005395ee64f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:49:20.680168+00:00
-- url     : https://prove2.me/submissions/66484139-9f2e-4838-8f9f-5facf950cb32

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_pow_mem
import Theorems.Thm_Formalism_L2_DIV_b_plc_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.DIV
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (u : (RInt F E)ˣ)
    (hu : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (u : RInt F E) - 1 ∈ P.asIdeal.map (toRInt F E)) :
    Units.map (RInt F E).subtype.toMonoidHom u ∈ wildAt E v := by
  refine ⟨⟨u, ?_, rfl⟩, hu⟩
  rw [SetLike.mem_coe, mem_kerRed]
  have hne : Ideal.span {((plc v : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact b_plc_ne_zero v
  obtain ⟨k, hk⟩ := b_pow_mem _ h _ hne
  rw [Ideal.map_span, Set.image_singleton, map_natCast] at hk
  exact ⟨k, hk⟩
end Formalism.L2.DIV
