-- Prove2me | solution 1 for PI.ScRefExists.GWG.hyp_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:26:21.1948+00:00
-- url     : https://prove2.me/submissions/97c0acf0-3833-45e7-9199-aac006198eec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlobWIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GWGlue
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GWG
open PI.ScRefExists.Sk
namespace PI.ScRefExists.GWG
theorem _root_.solution {I : Formalism.MainNotions.S.AutInst} {g g' r k : ℕ} {θ : 𝓞 I.E} {e f : Fin r → Fin I.n → I.E} {M : ℕ}
    (h : Hyp I g r k θ e f M) (hd : g' ∣ g) (h1 : 1 ≤ g') : Hyp I g' r k θ e f M := by
  obtain ⟨c, rfl⟩ := hd
  have hc : ∀ u : 𝓞 I.E, (u : I.E) = algebraMap (𝓞 I.E) I.E u := fun u => rfl
  have hGE : ∀ x, GE I (g' * c) x → GE I g' x := by
    rintro x ⟨t, rfl⟩
    refine ⟨(c : 𝓞 I.E) * t, ?_⟩
    simp only [hc, map_mul, map_natCast]
    push_cast
    ring
  obtain ⟨_, hS, hT, hn, he, hf, hef, hM, hL⟩ := h
  refine ⟨h1, ?_, ⟨hGE _ hT.1, hGE _ hT.2.1, hGE _ hT.2.2⟩, hn, he, hf, hef,
    Nat.Coprime.coprime_dvd_right (Dvd.intro c rfl) hM, hL⟩
  intro v hv
  apply hS v
  rw [Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ hv
end PI.ScRefExists.GWG
