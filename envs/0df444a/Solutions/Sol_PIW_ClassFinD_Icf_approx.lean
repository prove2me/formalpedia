-- Prove2me | solution 1 for PIW.ClassFinD.Icf.approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:33:03.471241+00:00
-- url     : https://prove2.me/submissions/94c7ab82-aa64-42da-820c-6a7ef32a6afb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_ExistsNeZeroMem
import Theorems.Thm_PIW_ClassFinD_Icf_v_unit_ne
import Theorems.Thm_PIW_ClassFinD_Icf_exists_ne_zero_mem
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_AdeleIntA_exists_approx
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_AdeleIntA_val_R


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
theorem _root_.solution (b : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hb : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) ≤ 1)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a : 𝓞 F, a ∈ latI b ∧ Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) ≤ v.intValuation a := by
  obtain ⟨r0, hr0, hr0I⟩ := exists_ne_zero_mem b
  obtain ⟨π, hπv, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hr : r0 * π ≠ 0 := mul_ne_zero hr0 hπ0
  obtain ⟨a, ha⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx (b : FiniteAdeleRing (𝓞 F) F)
    (fun w => hb w) (r0 * π) hr
  have hA : ∀ w : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a)) = w.intValuation a :=
    fun w => Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.val_R w a
  have hsmall : ∀ w : HeightOneSpectrum (𝓞 F), w.intValuation (r0 * π) ≤ w.intValuation r0 := by
    intro w
    rw [map_mul]
    exact mul_le_of_le_one_right' (w.intValuation_le_one π)
  refine ⟨a, fun w => ?_, ?_⟩
  · rw [← hA w]
    have e : algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a) =
        (b : FiniteAdeleRing (𝓞 F) F) w -
          ((b : FiniteAdeleRing (𝓞 F) F) w - algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a)) := by
      ring
    rw [e]
    refine (Valuation.map_sub _ _ _).trans (max_le le_rfl ?_)
    exact (ha w).trans ((hsmall w).trans (hr0I w))
  · by_contra hlt
    rw [not_le] at hlt
    have hbpos : 0 < Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) := zero_lt_iff.2 (v_unit_ne b v)
    have hπlt : v.intValuation π < 1 := (v.intValuation_lt_one_iff_mem π).2 hπv
    have h2 : Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) := by
      calc _ ≤ v.intValuation (r0 * π) := ha v
        _ = v.intValuation r0 * v.intValuation π := map_mul _ _ _
        _ ≤ Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) * v.intValuation π := by
          gcongr
          exact hr0I v
        _ < Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) * 1 := by
          exact mul_lt_mul_of_pos_left hπlt hbpos
        _ = _ := mul_one _
    have e : (b : FiniteAdeleRing (𝓞 F) F) v = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) +
        ((b : FiniteAdeleRing (𝓞 F) F) v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) := by
      ring
    have h3 := Valuation.map_add (Valued.v : Valuation (v.adicCompletion F) _)
      (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
      ((b : FiniteAdeleRing (𝓞 F) F) v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
    rw [← e, hA v] at h3
    exact absurd h3 (not_le.2 (max_lt hlt h2))
end PIW.ClassFinD.Icf
