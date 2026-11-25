-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.tensorGK_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:05.469786+00:00
-- url     : https://prove2.me/submissions/eb214f09-6b5b-418d-9c76-276f1f7d7054

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGK
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_actT_ad
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_actT_cont
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_actT_der
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_actT_fin
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_actT_mul
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_actT_one
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_pm_actT
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_tE_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : TensorGl → TensorGK := by
  intro hT n M _ _ ι _ _ Γ _ _ bar κ E ρ hK hE P _ _ lab
  refine ⟨⟨fun τ => (hT n M P (E τ) (hE.gl τ) (fib lab τ)).1, fun τ τ' h a b c d => TGK.tE_comm E hE.comm lab τ τ' h a b c d,
    TGK.actT_one lab κ ρ hK.one hE.one, TGK.actT_mul lab κ ρ hK.mul hE.mul,
    fun γ τ a b => TGK.actT_ad lab κ E ρ hK.unit hE.ad γ τ a b, fun y => TGK.actT_fin lab κ ρ hE.fin y,
    fun y lam => TGK.actT_cont lab κ ρ hK.cont hE.cont y lam, ?_⟩,
    fun σ hσ γ => TGK.pm_actT lab κ ρ σ hσ γ⟩
  intro τ X hX
  obtain ⟨c, hc0, hd, hoth, hρ⟩ := hE.der τ X hX
  exact ⟨c, hc0, hd, hoth, fun y lam => TGK.actT_der lab κ E ρ bar τ (hK.ne τ) hE.one hK.one hK.conj X c hc0 hd hoth
    hρ y lam⟩
end PositivityTheory.Rg.Cz
