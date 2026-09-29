-- Prove2me | solution 1 for WeierstrassProjModel.kw_a2_checks
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/20914d31-f90a-5100-aa86-93bda1bb775a

import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_kw_a2_checks_addXYZ_crossXZ
import Theorems.Thm_WeierstrassProjModel_kw_a2_checks_crossYZ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_a2_checks

set_option autoImplicit false

open WeierstrassProjModel

theorem _root_.P2MW.S_WeierstrassProjModel_kw_a2_checks.solution.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type u) [Field F] [Algebra R F] :
    (∀ P Q : Fin 3 → F, MvPolynomial.aeval (Sum.elim P Q) (kw_lrAdd_X W) = -(kw_lrApt_WF W F).addX P Q)
    ∧ (∀ P Q : Fin 3 → F, MvPolynomial.aeval (Sum.elim P Q) (kw_lrAdd_Y W) = -(kw_lrApt_WF W F).addY P Q)
    ∧ (∀ P Q : Fin 3 → F, MvPolynomial.aeval (Sum.elim P Q) (kw_lrAdd_Z W) = -(kw_lrApt_WF W F).addZ P Q)
    ∧ (∀ P : Fin 3 → F, (kw_lrApt_WF W F).Equation P →
      MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_X W) * (kw_lrApt_WF W F).dblZ P
      = MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_Z W) * (kw_lrApt_WF W F).dblX P)
    ∧ (∀ P : Fin 3 → F, (kw_lrApt_WF W F).Equation P →
      MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_Y W) * (kw_lrApt_WF W F).dblZ P
      = MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_Z W) * (kw_lrApt_WF W F).dblY P) :=
  ⟨(kw_a2_checks_addXYZ_crossXZ W F).1, (kw_a2_checks_addXYZ_crossXZ W F).2.1,
     (kw_a2_checks_addXYZ_crossXZ W F).2.2.1, (kw_a2_checks_addXYZ_crossXZ W F).2.2.2,
     kw_a2_checks_crossYZ W F⟩

end S_WeierstrassProjModel_kw_a2_checks
end P2MW
export P2MW.S_WeierstrassProjModel_kw_a2_checks (solution)
