-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_glue_compat_chase_03a68bf6b1b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:39:36.087919+00:00
-- url     : https://prove2.me/submissions/bb41fa9c-fd7d-4df0-849d-9ad0845fc1fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_trans_right_2820c52d5ef0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_eq_refl_trans_89064d77c543
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_comp__3ff0e312897d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mapIso_pullbackCompIso_refl_d1a5cb173cc5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mapIso_pullbackIsoAlong_3c729adf96c2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry
noncomputable section
set_option linter.unusedSimpArgs false
universe u
variable {T' T Y Z : Scheme.{u}}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {X XQ Xp V U W Oa Oam ON : Scheme.{0}}
    {ιV : V ⟶ X} {ιU : U ⟶ X} {ιW : W ⟶ X} {jV : W ⟶ V} {jU : W ⟶ U}
    {bQ : XQ ⟶ X} {bp : Xp ⟶ X} {rQp : XQ ⟶ Xp} {c0 : XQ ⟶ V} {rU : Xp ⟶ U}
    {ρU : U ⟶ ON} {rN : Xp ⟶ ON} {ρa : Oa ⟶ ON} {τa : Oa ⟶ V} {cA : XQ ⟶ Oa}
    {h : Oam ⟶ Oa} {cA' : XQ ⟶ Oam} {t : W ⟶ Oam} {k : W ⟶ Oa} {q : XQ ⟶ W}
    (hV : jV ≫ ιV = ιW) (hU : jU ≫ ιU = ιW) (h0 : c0 ≫ ιV = bQ) (hp : rQp ≫ bp = bQ)
    (hrU : rU ≫ ιU = bp) (h5 : rU ≫ ρU = rN) (e1 : cA ≫ ρa = rQp ≫ rN) (e2 : cA ≫ τa = c0)
    (ee : cA' ≫ h = cA) (ek : t ≫ h = k) (e7 : k ≫ ρa = jU ≫ ρU) (e8 : k ≫ τa = jV)
    (qV : q ≫ jV = c0) (qU : q ≫ jU = rQp ≫ rU) (qt : q ≫ t = cA') (qW : q ≫ ιW = bQ)
    {E : X.Modules} {E₀ : V.Modules} {Ep : Xp.Modules} {E' : ON.Modules}
    (e₀ : (Scheme.Modules.pullback ιV).obj E ≅ E₀)
    (eU : (Scheme.Modules.pullback ιU).obj E ≅ (Scheme.Modules.pullback ρU).obj E')
    (σ : (Scheme.Modules.pullback rN).obj E' ≅ Ep)
    (β : (Scheme.Modules.pullback rQp).obj Ep ≅ (Scheme.Modules.pullback c0).obj E₀)
    (ψ : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback ρa).obj E') ≅
      (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback τa).obj E₀))
    (hψ : pullbackIsoAlong ee ψ =
      (pullbackCompIso e1 (Iso.refl ((Scheme.Modules.pullback ρa).obj E'))).symm ≪≫
        pullbackCompIso (rfl : rQp ≫ rN = rQp ≫ rN) σ ≪≫ β ≪≫
        pullbackCompIso e2 (Iso.refl ((Scheme.Modules.pullback τa).obj E₀)))
    (hglue : pullbackCompIso hV e₀ = pullbackCompIso hU eU ≪≫ starIso ek e7 e8 ψ) :
    pullbackCompIso h0 e₀ =
      pullbackCompIso hp (pullbackCompIso hrU eU ≪≫
        ((pullbackCompIso h5 (Iso.refl ((Scheme.Modules.pullback ρU).obj E'))).symm ≪≫ σ)) ≪≫ β := by
  have e'' : (rQp ≫ rU) ≫ ιU = bQ := by rw [Category.assoc, hrU, hp]
  have qk : q ≫ k = cA := by rw [← ek, ← Category.assoc, qt, ee]
  have ekk : q ≫ jU ≫ ρU = rQp ≫ rN := by rw [← Category.assoc, qU, Category.assoc, h5]
  have e6 : (rQp ≫ rU) ≫ ρU = rQp ≫ rN := by rw [Category.assoc, h5]
  have hL : pullbackCompIso h0 e₀ = pullbackCompIso e'' eU ≪≫
      (pullbackCompIso qU (Iso.refl _) ≪≫ (Scheme.Modules.pullback q).mapIso (starIso ek e7 e8 ψ) ≪≫
        (pullbackCompIso qV (Iso.refl ((Scheme.Modules.pullback jV).obj E₀))).symm) := by
    rw [pullbackCompIso_comp' q hV qV qW h0 e₀, hglue, Functor.mapIso_trans,
      pullbackCompIso_comp' q hU qU qW e'' eU]
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  have hR : pullbackCompIso hp (pullbackCompIso hrU eU ≪≫
        ((pullbackCompIso h5 (Iso.refl ((Scheme.Modules.pullback ρU).obj E'))).symm ≪≫ σ)) ≪≫ β =
      pullbackCompIso e'' eU ≪≫ (pullbackCompIso (rfl : rQp ≫ rU = rQp ≫ rU) (Iso.refl _) ≪≫
        (Scheme.Modules.pullback rQp).mapIso
          ((pullbackCompIso h5 (Iso.refl ((Scheme.Modules.pullback ρU).obj E'))).symm ≪≫ σ) ≪≫ β) := by
    rw [pullbackCompIso_trans_right, pullbackCompIso_comp' rQp hrU rfl hp e'' eU,
      pullbackCompIso_eq_refl_trans hp (pullbackCompIso hrU eU)]
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [hL, hR]
  congr 1
  simp only [starIso, Functor.mapIso_trans, Functor.mapIso_symm]
  rw [mapIso_pullbackIsoAlong q ek ee qt qk ψ, hψ, mapIso_pullbackCompIso_refl q e7 qk ekk e1 E',
    mapIso_pullbackCompIso_refl q e8 qk qV e2 E₀,
    mapIso_pullbackCompIso_refl q (rfl : jU ≫ ρU = jU ≫ ρU) qU ekk e6 E',
    mapIso_pullbackCompIso_refl rQp h5 rfl rfl e6 E',
    pullbackCompIso_eq_refl_trans (rfl : rQp ≫ rN = rQp ≫ rN) σ]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.self_symm_id_assoc,
    Iso.symm_self_id_assoc, Iso.trans_refl, Iso.self_symm_id, Iso.symm_self_id]
end GroundTheory.Heights₂.Heights.Model
