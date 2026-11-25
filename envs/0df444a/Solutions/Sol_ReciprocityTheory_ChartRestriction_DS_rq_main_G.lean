-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rq_main_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:39:02.028873+00:00
-- url     : https://prove2.me/submissions/824c3355-743f-4a10-bbd6-29627f9e2c21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_K_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_K_UJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_KH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_UJ_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_inG_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_exp_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (v : D) :
    σ k ((actM E X v : D) : H) =
      ((actM E (k * X * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H) := by
  have hkU := rq_K_unit hk
  have hkUJ := rq_K_UJ hk
  have hkHUJ := rq_K_UJ (rq_KH hk)
  have hkinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hkU.1
  have hku : IsUnit k := ⟨⟨k, kᴴ, hkU.2, hkU.1⟩, rfl⟩
  have h2 := hD.deriv (k * X * kᴴ) (rq_inG_conj hk hX) ⟨σ k (v : H), hD.kStable k hk v v.2⟩
  have h1 : HasDerivAt (fun t : ℝ => σ k (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)))
      (σ k ((actM E X v : D) : H)) 0 := by
    have := ((σ k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hD.deriv X hX v)
    simpa [Function.comp_def] using this
  have hfun : (fun t : ℝ => σ k (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H))) =
      fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (k * X * kᴴ))) (σ k (v : H)) := by
    funext t
    have heUJ := rq_exp_mem ε X hX t
    have hexp : NormedSpace.exp ((t : ℂ) • (k * X * kᴴ)) = k * NormedSpace.exp ((t : ℂ) • X) * kᴴ := by
      rw [← hkinv, ← Matrix.exp_conj _ _ hku, Matrix.mul_smul, Matrix.smul_mul]
    rw [hexp]
    have e1 : σ (k * NormedSpace.exp ((t : ℂ) • X) * kᴴ * k) =
        (σ (k * NormedSpace.exp ((t : ℂ) • X) * kᴴ)).comp (σ k) :=
      hσ.1.2 _ (rq_UJ_mul (rq_UJ_mul hkUJ heUJ) hkHUJ) k hkUJ
    rw [mul_assoc (k * NormedSpace.exp ((t : ℂ) • X)), hkU.1, mul_one, hσ.1.2 k hkUJ _ heUJ] at e1
    exact congrArg (fun L : H →L[ℂ] H => L (v : H)) e1
  rw [hfun] at h1
  exact h1.unique h2
end ReciprocityTheory.ChartRestriction.DS
