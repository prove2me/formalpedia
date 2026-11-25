-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:54:53.734879+00:00
-- url     : https://prove2.me/submissions/15e14533-fea6-49f1-a18f-97439e1cc2f5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_hM
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
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (δ : Matrix (Fin I.n) (Fin I.n) I.E) (k : ℕ) (u b' : Fin k → Fin I.n → I.E)
    (hu : LinearIndependent I.E (fun c => δ *ᵥ u c))
    (hsp : ∀ z, δ *ᵥ z ∈ Submodule.span I.E (Set.range fun c => δ *ᵥ u c))
    (hb : LinearIndependent I.E b') (hperp : ∀ a, PerpKer I δ (b' a)) :
    ∀ w, hM I b' *ᵥ w = 0 → δ *ᵥ w = 0 := by
  intro w hw
  have hle : LinearMap.ker δ.mulVecLin ≤ LinearMap.ker (hM I b').mulVecLin := by
    intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    funext a
    rw [Matrix.mulVecLin_apply, ap_hM]
    exact hperp a z hz
  have hrδ : Module.finrank I.E (LinearMap.range δ.mulVecLin) = k := by
    have hr : LinearMap.range δ.mulVecLin = Submodule.span I.E (Set.range fun c => δ *ᵥ u c) := by
      apply le_antisymm
      · rintro _ ⟨z, rfl⟩
        exact hsp z
      · rw [Submodule.span_le]
        rintro _ ⟨c, rfl⟩
        exact ⟨u c, rfl⟩
    rw [hr, finrank_span_eq_card hu, Fintype.card_fin]
  have hrows : LinearIndependent I.E (fun a => hM I b' a) := by
    rw [linearIndependent_iff'] at hb ⊢
    intro s g hg a ha
    have h1 : (∑ j ∈ s, g j • (fun i => star (b' j i))) ᵥ* I.J = 0 := by
      rw [← hg]
      funext i
      simp only [hM, Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
    have hJ : IsUnit I.J.det := isUnit_iff_ne_zero.mpr I.J_det
    have h2 : (∑ j ∈ s, g j • (fun i => star (b' j i))) = 0 := by
      have := congrArg (fun x => x ᵥ* I.J⁻¹) h1
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJ] using this
    have h3 : ∑ j ∈ s, star (g j) • b' j = 0 := by
      funext i
      have := congrArg star (congrFun h2 i)
      simpa [Finset.sum_apply, star_sum, star_mul'] using this
    have := hb s (fun j => star (g j)) h3 a ha
    simpa using this
  have hrM : Module.finrank I.E (LinearMap.range (hM I b').mulVecLin) = k := by
    have := Matrix.rank_eq_finrank_span_row (hM I b')
    have hrows' : LinearIndependent I.E (hM I b').row := by
      first
        | exact hrows
        | simpa [Matrix.row] using hrows
    rw [finrank_span_eq_card hrows', Fintype.card_fin] at this
    exact this
  have hn1 := LinearMap.finrank_range_add_finrank_ker δ.mulVecLin
  have hn2 := LinearMap.finrank_range_add_finrank_ker (hM I b').mulVecLin
  have heq : LinearMap.ker δ.mulVecLin = LinearMap.ker (hM I b').mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hw' : w ∈ LinearMap.ker (hM I b').mulVecLin := LinearMap.mem_ker.mpr hw
  rw [← heq] at hw'
  exact LinearMap.mem_ker.mp hw'
end PI.UnitaryGroupMassFormula.LCG
