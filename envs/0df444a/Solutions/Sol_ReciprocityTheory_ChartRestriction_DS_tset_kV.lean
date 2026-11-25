-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.tset_kV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:07:14.066793+00:00
-- url     : https://prove2.me/submissions/2c2e40be-800a-4209-a68a-3b9ff6ce790c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tset_conj_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tset_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tset_comb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tset_combd
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_actM_single__1981af085db5
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eeV_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eeVd_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isInLieAlgebra_I_smul_add_conjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_K_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_inG_S
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_lin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_main_G


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {D : Submodule ℂ H}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (dual : Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (f f' : Fin n → D)
    (h : (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((f c : D) : H))) :
    (fun c => ((eeF dual E f' c : D) : H)) = kDiag dual σ k (fun c => ((eeF dual E f c : D) : H)) := by
  have hu := tset_unit (rq_K_unit hk).2
  have hgen : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (v : D), σ k ((actM E X v : D) : H) =
      ((actM E (k * X * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H) := by
    intro X v
    have h0 := rq_lin hD hk v (1 / 2) (-Complex.I / 2) (rq_main_G hσ hD hk (rq_inG_S ε X) v)
      (rq_main_G hσ hD hk (isInLieAlgebra_I_smul_add_conjTranspose ε X) v)
    have hX : (1 / 2 : ℂ) • (X - Jm ε * Xᴴ * Jm ε) +
        (-Complex.I / 2) • (Complex.I • (X + Jm ε * Xᴴ * Jm ε)) = X := by
      rw [smul_smul, show -Complex.I / 2 * Complex.I = (1 / 2 : ℂ) by
          rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]; ring, ← smul_add,
        show X - Jm ε * Xᴴ * Jm ε + (X + Jm ε * Xᴴ * Jm ε) = (2 : ℂ) • X by rw [two_smul]; abel,
        smul_smul]
      norm_num
    rwa [hX] at h0
  let g : Fin n → D := fun d => ⟨σ k ((f d : D) : H), hD.kStable k hk _ (f d).2⟩
  have hsingle : ∀ x y z, σ k ((E x y (f z) : D) : H) =
      ((∑ a, ∑ b, (k a x * star (k b y)) • E a b (g z) : D) : H) := by
    intro x y z
    rw [← actM_single' E x y, hgen]
    congr 1
    unfold actM
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, tset_conj_single] <;> rfl
  cases dual
  · have hf' : ∀ r, f' r = ∑ d, k r d • g d := by
      intro r
      apply Subtype.ext
      have h1 := congrFun h r
      simp only [kDiag, cond_false] at h1
      rw [h1, Submodule.coe_sum]
      simp only [Submodule.coe_smul] <;> rfl
    funext s
    show ((eeV E f' s : D) : H) = ∑ d, k s d • σ k ((eeV E f d : D) : H)
    simp only [eeV_coord, hf', map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, hsingle]
    rw [tset_comb k hu (fun a b r => ((E a b (g r) : D) : H)) s, Finset.sum_comm]
  · have hf' : ∀ r, f' r = ∑ d, star (k r d) • g d := by
      intro r
      apply Subtype.ext
      have h1 := congrFun h r
      simp only [kDiag, cond_true] at h1
      rw [h1, Submodule.coe_sum]
      simp only [Submodule.coe_smul] <;> rfl
    funext r
    show ((eeVd E f' r : D) : H) = ∑ d, star (k r d) • σ k ((eeVd E f d : D) : H)
    simp only [eeVd_coord, hf', map_sum, map_smul, map_neg, Submodule.coe_sum, Submodule.coe_smul,
      Submodule.coe_neg, hsingle, smul_neg, Finset.sum_neg_distrib]
    rw [tset_combd k hu (fun a b s => ((E a b (g s) : D) : H)) r, Finset.sum_comm]
end ReciprocityTheory.ChartRestriction.DS
