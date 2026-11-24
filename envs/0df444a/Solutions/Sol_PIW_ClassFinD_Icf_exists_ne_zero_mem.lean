-- Prove2me | solution 1 for PIW.ClassFinD.Icf.exists_ne_zero_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:12:40.192442+00:00
-- url     : https://prove2.me/submissions/2a6ab5da-54fe-4691-b6b5-9eaa40b29f0c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_ExistsNeZeroMem
import Theorems.Thm_PIW_ClassFinD_Icf_v_mul
import Theorems.Thm_PIW_ClassFinD_Icf_v_algR
import Theorems.Thm_PIW_ClassFinD_Icf_v_unit_ne
import Theorems.Thm_PIW_ClassFinD_Icf_v_inv
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_AdeleIntA_exists_den


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.ClassFinD PIW.ClassFinD.Icf
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
namespace PIW.ClassFinD.Icf
theorem _root_.solution (b : (FiniteAdeleRing (𝓞 F) F)ˣ) : ∃ r : 𝓞 F, r ≠ 0 ∧ r ∈ latI b := by
  obtain ⟨r, hr, h⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_den
    (((b⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
  refine ⟨r, hr, fun w => ?_⟩
  have h1 : Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r *
      ((b⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) w) ≤ 1 := h w
  rw [v_mul, v_algR, v_inv] at h1
  have hpos : 0 < Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) := zero_lt_iff.2 (v_unit_ne b w)
  rw [mul_inv_le_iff₀ hpos, one_mul] at h1
  exact h1
end PIW.ClassFinD.Icf
