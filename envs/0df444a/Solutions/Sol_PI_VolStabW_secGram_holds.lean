-- Prove2me | solution 1 for PI.VolStabW.secGram_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:32.533068+00:00
-- url     : https://prove2.me/submissions/1d3278fb-ed84-45b9-a141-72969a3228c8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVSecSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVSec
import Theorems.Thm_PI_VolStabW_exists_leftInv_of_linIndep
import Theorems.Thm_PI_VolStabW_hR_herm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution : SecGram := by
  intro F E _ _ _ _ _ σ hσ M J hJ hdet R _ _ hss a x hx
  have := hss
  let s := sigR R σ
  let Z : Fin a → Fin M → R ⊗[F] E := fun i => Matrix.vecMul (fun l => s (x i l)) (JR (F := F) R J)
  have hZh : ∀ i y, hR R σ J (x i) y = ∑ k, Z i k * y k := by
    intro i y
    simp only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hJu : IsUnit (JR (F := F) R J).det := by
    have e := RingHom.map_det (inclR (F := F) (E := E) R) J
    rw [RingHom.mapMatrix_apply] at e
    show IsUnit (J.map (inclR R)).det
    rw [← e]
    exact (isUnit_iff_ne_zero.2 hdet).map _
  have hZ : LinearIndependent (R ⊗[F] E) Z := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    let v : Fin M → R ⊗[F] E := fun l => ∑ i, g i * s (x i l)
    have hv0 : Matrix.vecMul v (JR (F := F) R J) = 0 := by
      funext j
      have := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct,
        Finset.mul_sum, Pi.zero_apply] at this
      simp only [Matrix.vecMul, dotProduct, v, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hv : v = 0 := by
      have := congrArg (fun u => Matrix.vecMul u (JR (F := F) R J)⁻¹) hv0
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one,
        Matrix.zero_vecMul] at this
      exact this
    have hX0 : ∑ i, s (g i) • x i = 0 := by
      funext l
      have := congrArg s (congrFun hv l)
      simp only [v, map_sum, map_mul, s, sigR_invol R σ hσ, Pi.zero_apply, map_zero] at this
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have := Fintype.linearIndependent_iff.1 hx _ hX0 i
    have e2 := congrArg s this
    simp only [s, sigR_invol R σ hσ, map_zero] at e2
    exact e2
  obtain ⟨q, hq⟩ := exists_leftInv_of_linIndep Z hZ
  refine ⟨q, fun S hS => ?_⟩
  have hh : algebraMap F (R ⊗[F] E) (1 / 2) + algebraMap F (R ⊗[F] E) (1 / 2) = 1 := by
    rw [← map_add, show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one]
  have hsh : sigR R σ (algebraMap F (R ⊗[F] E) (1 / 2)) = algebraMap F (R ⊗[F] E) (1 / 2) :=
    (Algebra.TensorProduct.map (AlgHom.id F R) σ).commutes _
  have h1 : ∀ i j, hR R σ J (x i)
      (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j) * q k i') =
        algebraMap F (R ⊗[F] E) (1 / 2) * S i j := by
    intro i j
    rw [hZh]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have e3 : ∀ i', ∑ k, Z i k * (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j * q k i') =
        algebraMap F (R ⊗[F] E) (1 / 2) * S i' j * (if i = i' then 1 else 0) := fun i' => by
      rw [← hq i i', Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [e3, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h2 : ∀ i j, hR R σ J
      (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' i) * q k i') (x j) =
        algebraMap F (R ⊗[F] E) (1 / 2) * S i j := by
    intro i j
    rw [← hR_herm R σ hσ J hJ (x j), h1 j i, map_mul, hsh, hS i j]
  funext i j
  show hR R σ J (x i) (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j) * q k i') +
    hR R σ J (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' i) * q k i') (x j) = S i j
  rw [h1, h2, ← add_mul, hh, one_mul]
end PI.VolStabW
