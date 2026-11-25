-- Prove2me | solution 1 for PIW.ClassFinD.Icf.val_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:40:46.200967+00:00
-- url     : https://prove2.me/submissions/855cae82-c5e8-420f-87af-8e33ff7c725f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_ExistsNeZeroMem
import Theorems.Thm_PIW_ClassFinD_Icf_approx

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
theorem _root_.solution (b b' : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hb : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) ≤ 1)
    {x y : 𝓞 F} (h : Ideal.span {x} * latI b ≤ Ideal.span {y} * latI b') (v : HeightOneSpectrum (𝓞 F)) :
    v.intValuation x * Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) ≤
      v.intValuation y * Valued.v ((b' : FiniteAdeleRing (𝓞 F) F) v) := by
  obtain ⟨a, haI, hav⟩ := approx b hb v
  obtain ⟨z, hzI, hz⟩ := (Ideal.span_singleton_mul_le_span_singleton_mul.1 h) a haI
  calc v.intValuation x * Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v)
      ≤ v.intValuation x * v.intValuation a := by gcongr
    _ = v.intValuation (x * a) := (map_mul _ _ _).symm
    _ = v.intValuation (y * z) := by rw [hz]
    _ = v.intValuation y * v.intValuation z := map_mul _ _ _
    _ ≤ v.intValuation y * Valued.v ((b' : FiniteAdeleRing (𝓞 F) F) v) := by
      gcongr
      exact hzI v
end PIW.ClassFinD.Icf
