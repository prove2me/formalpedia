-- Prove2me | solution 1 for PI.Dv.ProjGramW.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:35:54.766088+00:00
-- url     : https://prove2.me/submissions/bdb532a5-44ff-44cc-beed-ebf6a6d475bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
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
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.Dv.ProjGramW
theorem _root_.solution (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (hnd : ∀ x, (∀ y, h x y = 0) → x = 0)
    (φ : Module.Dual K A.V) : ∃ u, h u = φ := by
  classical
  let G : Matrix A.ι A.ι K := fun i j => h (A.b i) (A.b j)
  have hsum : ∀ (c : A.ι → K) (j : A.ι), h (∑ i, star (c i) • A.b i) (A.b j) = Matrix.vecMul c G j := by
    intro c j
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, starRingEnd_apply, star_star,
      smul_eq_mul, Matrix.vecMul, dotProduct, G]
  have key : ∀ c : A.ι → K, Matrix.vecMul c G = 0 → c = 0 := by
    intro c hc
    have hu : h (∑ i, star (c i) • A.b i) = 0 := A.b.ext fun j => by
      rw [hsum c j, hc]
      rfl
    have hu0 := hnd (∑ i, star (c i) • A.b i) (fun y => by rw [hu]; rfl)
    have h0 := (Fintype.linearIndependent_iff.mp A.b.linearIndependent) (fun i => star (c i)) hu0
    funext i
    exact star_eq_zero.mp (h0 i)
  have hinj : Function.Injective (fun c : A.ι → K => Matrix.vecMul c G) := by
    intro c c' hcc
    have := key (c - c') (by rw [Matrix.sub_vecMul]; exact sub_eq_zero.mpr hcc)
    exact sub_eq_zero.mp this
  have hsurj : Function.Surjective (fun c : A.ι → K => Matrix.vecMul c G) :=
    Matrix.vecMul_surjective_iff_isUnit.mpr (Matrix.vecMul_injective_iff_isUnit.mp hinj)
  obtain ⟨c, hc⟩ := hsurj (fun j => φ (A.b j))
  refine ⟨∑ i, star (c i) • A.b i, A.b.ext fun j => ?_⟩
  rw [hsum c j]
  exact congrFun hc j
end PI.Dv.ProjGramW
