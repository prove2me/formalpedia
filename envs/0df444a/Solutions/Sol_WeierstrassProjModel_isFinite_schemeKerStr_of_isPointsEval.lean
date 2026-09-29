-- Prove2me | solution 1 for WeierstrassProjModel.isFinite_schemeKerStr_of_isPointsEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/aca1c75c-5628-5c07-8c13-483ca487fd8c

import Definitions.Def_WeierstrassCurve_ProjModel
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_isFinite_schemeKerStr_of_isPointsEval

set_option autoImplicit false
set_option Elab.async false

noncomputable section

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_isFinite_schemeKerStr_of_isPointsEval.WeierstrassProjModel"

universe u

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "RelativeGroupLaw projModelCR projModelStrCR IsPointsEval projModelStrCR_isProper schemeNsmul_locallyQuasiFinite_of_isPointsEval"
p2m_open "WeierstrassProjModel"

namespace RelativeGroupLaw
p2m_export "WeierstrassProjModel.RelativeGroupLaw" "schemeNsmul schemeNsmul_over schemeKer schemeKerStr one"
p2m_open "WeierstrassProjModel.RelativeGroupLaw"

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

scoped instance isProper_schemeNsmul (G : RelativeGroupLaw R f) [IsProper f] (n : ℕ) :
    IsProper (G.schemeNsmul n) := by
  have : IsProper (G.schemeNsmul n ≫ f) := by
    rw [G.schemeNsmul_over n]; infer_instance
  exact IsProper.of_comp (G.schemeNsmul n) f

private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.isFinite_schemeNsmul (G : RelativeGroupLaw R f) [IsProper f]
    (hQF : ∀ n : ℕ, 0 < n → LocallyQuasiFinite (G.schemeNsmul n)) {n : ℕ} (hn : 0 < n) :
    IsFinite (G.schemeNsmul n) :=
  haveI : LocallyQuasiFinite (G.schemeNsmul n) := hQF n hn
  IsFinite.of_isProper_of_locallyQuasiFinite (G.schemeNsmul n)

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "isFinite_schemeNsmul"

theorem isFinite_schemeKer_snd (G : RelativeGroupLaw R f) [IsProper f]
    (hQF : ∀ n : ℕ, 0 < n → LocallyQuasiFinite (G.schemeNsmul n)) {n : ℕ} (hn : 0 < n) :
    IsFinite (pullback.snd (G.schemeNsmul n) (G.one (𝟙 _)).1
        : G.schemeKer n ⟶ Spec (CommRingCat.of R)) :=
  haveI : IsFinite (G.schemeNsmul n) := G.isFinite_schemeNsmul hQF hn
  inferInstance

end RelativeGroupLaw
p2m_reactivate "P2MW.S_WeierstrassProjModel_isFinite_schemeKerStr_of_isPointsEval.WeierstrassProjModel.RelativeGroupLaw"

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_isFinite_schemeKerStr_of_isPointsEval.WeierstrassProjModel.RelativeGroupLaw P2MW.S_WeierstrassProjModel_isFinite_schemeKerStr_of_isPointsEval.WeierstrassProjModel"

theorem solution
    {R : Type u} [CommRing R]
    (V : WeierstrassCurve.Projective R)
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
      Nonempty (pullback (projModelStrCR V)
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        ≅ projModelCR (V.baseChange K)))
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev)
    (hℓ : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F] [IsAlgClosed F] (ℓ : ℕ),
      ℓ.Prime → (ℓ : F) ≠ 0 →
      ∃ P : (V.baseChange F).toAffine.Point, P ≠ 0 ∧ ℓ • P = 0)
    {n : ℕ} (hn : 0 < n) :
    IsFinite (G.schemeKerStr n) :=
  haveI : AlgebraicGeometry.IsProper (projModelStrCR V) :=
    WeierstrassProjModel.projModelStrCR_isProper V
  WeierstrassProjModel.RelativeGroupLaw.isFinite_schemeKer_snd G
    (WeierstrassProjModel.schemeNsmul_locallyQuasiFinite_of_isPointsEval
      V hbc G ev hev hℓ) hn

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_isFinite_schemeKerStr_of_isPointsEval.WeierstrassProjModel.RelativeGroupLaw P2MW.S_WeierstrassProjModel_isFinite_schemeKerStr_of_isPointsEval.WeierstrassProjModel"

end S_WeierstrassProjModel_isFinite_schemeKerStr_of_isPointsEval
end P2MW
export P2MW.S_WeierstrassProjModel_isFinite_schemeKerStr_of_isPointsEval (solution)
