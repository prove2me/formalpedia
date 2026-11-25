-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.cardStep_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:16.130746+00:00
-- url     : https://prove2.me/submissions/e36efcc5-314d-416b-82b4-7f2d47cda909

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_ratMat_emb
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_linOf_matGL
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_linOf_inj
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_matGL_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_image_latSet
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_set_of_coords_inj
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_Lam_emb_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_emb_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_sfin_of_Lam_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_Lam_mul_sfin
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_emb_ratU
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_equivStep
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_isomStep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (hR : PI.UnitaryGroupMassFormula.UJClassFin.RatDense) (hC : CrdBounds) : CardStep := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hn hL hsig g
  obtain ⟨hb1, hb2⟩ := hC F E V M b L0 hL
  have hR' := hR F E σ M (gramOf h b) (crdOf b L0) hb1 hb2

  have wd : ∀ γ : stab (GamG σ (gramOf h b)) (SFin σ (gramOf h b) (crdOf b L0)) g,
      iotaG σ (gramOf h b) b γ.1 ∈ isom h ∧
        (iotaG σ (gramOf h b) b γ.1 : V → V) '' latSet σ (gramOf h b) b L0 g = latSet σ (gramOf h b) b L0 g := by
    intro γ
    refine ⟨isomStep F E σ V h M b L0 hσ hθ hτ hs hn hL hsig γ.1, ?_⟩
    have e1 := equivStep F E σ V h M b L0 hσ hθ hτ hs hn hL hsig g γ.1 1
    rw [← e1]
    have e2 : ((γ.1 : GamG σ (gramOf h b)) : HA (AF F) σ (gramOf h b)) * g *
        ((1 : SFin σ (gramOf h b) (crdOf b L0)) : HA (AF F) σ (gramOf h b)) =
        g * ((⟨_, γ.2⟩ : SFin σ (gramOf h b) (crdOf b L0)) : HA (AF F) σ (gramOf h b)) := by
      simp only [OneMemClass.coe_one, mul_one, mul_inv_cancel_left]
    rw [e2]
    show {v | b.equivFun v ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) (g * _)} =
      {v | b.equivFun v ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) g}
    rw [Lam_mul_sfin]
  let f : stab (GamG σ (gramOf h b)) (SFin σ (gramOf h b) (crdOf b L0)) g →
      {u : V ≃ₗ[E] V // u ∈ isom h ∧ (u : V → V) '' latSet σ (gramOf h b) b L0 g = latSet σ (gramOf h b) b L0 g} :=
    fun γ => ⟨iotaG σ (gramOf h b) b γ.1, wd γ⟩
  apply Nat.card_eq_of_bijective f
  refine ⟨?_, ?_⟩
  · intro γ γ' e
    have e1 : iotaG σ (gramOf h b) b γ.1 = iotaG σ (gramOf h b) b γ'.1 := congrArg Subtype.val e
    have e2 : ratMat σ (gramOf h b) γ.1 = ratMat σ (gramOf h b) γ'.1 := linOf_inj b e1
    have e3 : ratU σ (gramOf h b) γ.1 = ratU σ (gramOf h b) γ'.1 := Subtype.ext e2
    apply Subtype.ext
    apply Subtype.ext
    rw [← emb_ratU σ (gramOf h b) γ.1, ← emb_ratU σ (gramOf h b) γ'.1, e3]
  · rintro ⟨u, hu, hl⟩
    set U : UJ (σ : E →+* E) (gramOf h b) := ⟨matGL b u, matGL_mem σ hσ h b hu⟩ with hUdef
    let γ : GamG σ (gramOf h b) := ⟨PI.UnitaryGroupMassFormula.UJClassFin.emb σ (gramOf h b) U, PI.UnitaryGroupMassFormula.UJClassFin.emb_mem σ (gramOf h b) U⟩
    have hι : iotaG σ (gramOf h b) b γ = u := by
      show linOf b (ratMat σ (gramOf h b) γ) = u
      rw [ratMat_emb]
      exact linOf_matGL b u
    have e1 : (linOf b (matGL b u) : V → V) '' latSet σ (gramOf h b) b L0 g = latSet σ (gramOf h b) b L0 g := by
      rw [linOf_matGL]; exact hl
    rw [image_latSet] at e1
    have e2 := set_of_coords_inj b e1
    have e3 : PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) g =
        PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) ((γ : HA (AF F) σ (gramOf h b)) * g) := by
      rw [PI.UnitaryGroupMassFormula.UJClassFin.Lam_emb_mul]; exact e2.symm
    have hk := PI.UnitaryGroupMassFormula.UJClassFin.sfin_of_Lam_eq σ (gramOf h b) (crdOf b L0) hR' _ _ e3
    refine ⟨⟨γ, hk⟩, ?_⟩
    exact Subtype.ext hι
end PI.UnitaryGroupMassFormula.UJClassMass
