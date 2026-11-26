-- Prove2me | solution 1 for PI.WAU.coord_smul
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:43:01.105301+00:00
-- url     : https://prove2.me/submissions/b8869d96-839b-473c-82e3-a5de5990e2f1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open scoped TensorProduct
variable {F E B : Type} [Field F] [Field E] [Algebra F E] [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
theorem _root_.solution (c : F) (x : E ⊗[F] B) : coord b (c • x) = c • coord b x := by
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
  trace "HIT_60_0"

end 
