-- Prove2me | solution 1 for PIW.AdelClassFin.dictTop_into
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:26:12.700546+00:00
-- url     : https://prove2.me/submissions/d71a1b13-92cc-4939-867e-8034274b8c2d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (hG : MGen) (I : AutInst) (a b : I.Gf) (h : abelian₂ I a = abelian₂ I b)
    (z : Fin I.n → I.E ⊗[I.F] Af I.F) (hz : z ∈ I.Lf) : I.fmat a⁻¹ *ᵥ (I.fmat b *ᵥ z) ∈ I.Lf := by
  refine Submodule.span_induction (p := fun y _ => I.fmat a⁻¹ *ᵥ y ∈ I.Lf)
    (fun y hy => ?_) ?_ (fun y w _ _ hy hw => ?_) (fun c y _ hy => ?_) (hG I b z hz)
  · obtain ⟨v, rfl⟩ := hy
    have hv : (v : Fin I.n → I.E) ∈ abelian₂ I a := by
      rw [h]
      exact v.2
    exact hv
  · rw [Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  · rw [Matrix.mulVec_add]
    exact I.Lf.add_mem hy hw
  · show I.fmat a⁻¹ *ᵥ ((c : I.E ⊗[I.F] Af I.F) • y) ∈ I.Lf
    rw [Matrix.mulVec_smul]
    exact I.Lf.smul_mem c hy
end PIW.AdelClassFin
