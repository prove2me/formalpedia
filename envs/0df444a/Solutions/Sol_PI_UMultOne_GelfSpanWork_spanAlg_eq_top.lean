-- Prove2me | solution 1 for PI.UMultOne.GelfSpanWork.spanAlg_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:52:24.107997+00:00
-- url     : https://prove2.me/submissions/6ae06af4-ee06-472f-a84e-0202662f39dd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegralSpanAlgebra_Burnside
import Theorems.Thm_PI_UMultOne_GelfSpanWork_spanAlg_smul
import Theorems.Thm_PI_UMultOne_GelfSpanWork_spanAlg_simple
import Theorems.Thm_PI_UMultOne_GelfSpanWork_schur

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UMultOne PI.UMultOne.GelfSpanWork
open Matrix Module
variable {G : Type} [Group G] {N : ℕ}
namespace PI.UMultOne.GelfSpanWork
theorem _root_.solution (ρ : G →* GL (Fin N) ℂ) (hN : 0 < N) (hI : Irr ρ) :
    ∀ f : Module.End ℂ (Fin N → ℂ), f ∈ spanAlg ρ := by
  intro f
  have := spanAlg_simple ρ hN hI
  let F : Module.End (Module.End (spanAlg ρ) (Fin N → ℂ)) (Fin N → ℂ) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro φ v
        obtain ⟨c, hc⟩ := schur ρ hN hI φ
        simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image (fun i => Pi.single i (1 : ℂ)))
  have : (r : Module.End ℂ (Fin N → ℂ)) = f := by
    apply (Pi.basisFun ℂ (Fin N)).ext
    intro i
    have := hr (Pi.single i 1) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    rw [Pi.basisFun_apply, ← spanAlg_smul]
    exact this.symm
  exact this ▸ r.2
end PI.UMultOne.GelfSpanWork
