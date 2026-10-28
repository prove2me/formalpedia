-- Prove2me | solution 1 for RiskAverseSDDP.Subdiff.normalCone_C1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:15:26.64251+00:00
-- url     : https://prove2.me/submissions/8943cdb1-4b9c-4dbc-8d89-2626863d99e4

import Mathlib
import Definitions.Def_RiskAverseSDDP_Subdiff_Model
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

open scoped RealInnerProductSpace

namespace Aux_RA_nc

open Matrix

lemma adj {m q : ℕ} (A : Matrix (Fin q) (Fin m) ℝ) (lam : EuclideanSpace ℝ (Fin q))
    (x : EuclideanSpace ℝ (Fin m)) :
    ⟪lam, Matrix.toEuclideanLin A x⟫ = ⟪Matrix.toEuclideanLin A.transpose lam, x⟫ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply, star_trivial]
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose]; exact dotProduct_comm _ _

end Aux_RA_nc

open RiskAverseSDDP.Subdiff ConvexProgram Aux_RA_nc in
theorem solution {m n q p : ℕ} (P : ConvexProgram m n q p)
    (z₀ : E m × E n) (hz₀ : z₀ ∈ P.C1) :
    normalConeProd P.C1 z₀ =
      {v | ∃ lam : E q,
        v = (Matrix.toEuclideanLin P.A.transpose lam, Matrix.toEuclideanLin P.B.transpose lam)} := by
  -- the linear map L(x, y) = A x + B y
  set L : (E m × E n) →ₗ[ℝ] E q :=
    (Matrix.toEuclideanLin P.A).coprod (Matrix.toEuclideanLin P.B) with hL
  have hLapp : ∀ w : E m × E n, L w = P.lin w.1 w.2 := fun w => rfl
  have hz0 : P.lin z₀.1 z₀.2 = P.b := hz₀
  ext v
  constructor
  · intro hv
    -- v vanishes on ker L
    set φ : (E m × E n) →ₗ[ℝ] ℝ := (innerₛₗ ℝ v.1).coprod (innerₛₗ ℝ v.2) with hφ
    have hφapp : ∀ w, φ w = pair v w := fun w => rfl
    have hker : ∀ w ∈ LinearMap.ker L, φ w = 0 := by
      intro w hw
      rw [LinearMap.mem_ker] at hw
      have hmem : ∀ c : ℝ, z₀ + c • w ∈ P.C1 := by
        intro c
        show P.lin (z₀ + c • w).1 (z₀ + c • w).2 = P.b
        rw [← hLapp, map_add, map_smul, hw, smul_zero, add_zero, hLapp, hz0]
      have h1 := hv _ (hmem 1)
      have h2 := hv _ (hmem (-1))
      rw [add_sub_cancel_left, one_smul, ← hφapp] at h1
      rw [add_sub_cancel_left, ← hφapp, map_smul, smul_eq_mul] at h2
      linarith
    have hann : φ ∈ (LinearMap.ker L).dualAnnihilator :=
      (Submodule.mem_dualAnnihilator φ).mpr hker
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hann
    obtain ⟨ψ, hψ⟩ := hann
    set lam := (InnerProductSpace.toDual ℝ (E q)).symm (LinearMap.toContinuousLinearMap ψ)
      with hlam
    have hlamψ : ∀ y, ⟪lam, y⟫ = ψ y := by
      intro y
      rw [hlam, InnerProductSpace.toDual_symm_apply]
      rfl
    have hkey : ∀ w, pair v w = ⟪lam, L w⟫ := by
      intro w
      rw [← hφapp, ← hψ, LinearMap.dualMap_apply, hlamψ]
    refine ⟨lam, ?_⟩
    have h1 : v.1 = Matrix.toEuclideanLin P.A.transpose lam := by
      apply ext_inner_right ℝ
      intro x
      have := hkey (x, 0)
      simp only [pair, inner_zero_right, add_zero] at this
      rw [this, hL, LinearMap.coprod_apply, map_zero, add_zero, adj]
    have h2 : v.2 = Matrix.toEuclideanLin P.B.transpose lam := by
      apply ext_inner_right ℝ
      intro y
      have := hkey (0, y)
      simp only [pair, inner_zero_right, zero_add] at this
      rw [this, hL, LinearMap.coprod_apply, map_zero, zero_add, adj]
    exact Prod.ext h1 h2
  · rintro ⟨lam, rfl⟩ z hz
    have hz' : P.lin z.1 z.2 = P.b := hz
    unfold pair
    simp only [Prod.fst_sub, Prod.snd_sub]
    rw [← adj, ← adj, ← inner_add_right]
    have : Matrix.toEuclideanLin P.A (z.1 - z₀.1) + Matrix.toEuclideanLin P.B (z.2 - z₀.2) =
        P.lin z.1 z.2 - P.lin z₀.1 z₀.2 := by
      unfold ConvexProgram.lin
      rw [map_sub, map_sub]; abel
    rw [this, hz', hz0, sub_self, inner_zero_right]
