-- Prove2me | solution 1 for PIW.ClassFinD.Icf.mem_latI
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:40:27.333399+00:00
-- url     : https://prove2.me/submissions/519cbf10-7c2e-4090-abb4-4f426cbb6ccc

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_ExistsNeZeroMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact



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
theorem _root_.solution {b : (FiniteAdeleRing (𝓞 F) F)ˣ} {x : 𝓞 F} :
    x ∈ latI b ↔ ∀ w : HeightOneSpectrum (𝓞 F), w.intValuation x ≤ Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | decide
    | (intros; omega)
    | (intros; simp)
    | (intros; simp_all)
    | (intros; norm_num)
    | (intros; positivity)
    | (intros; aesop)
    | (intros; nlinarith)
    | (intros; field_simp; ring)
    | (intros; ext; simp)
    | (intros; constructor <;> intro h <;> simpa using h)
    | (intros; exact?)
  trace "HIT_49_0"

end 
