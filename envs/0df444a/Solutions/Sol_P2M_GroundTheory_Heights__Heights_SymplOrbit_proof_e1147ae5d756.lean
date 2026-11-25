-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplOrbit_proof_e1147ae5d756
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:13.225965+00:00
-- url     : https://prove2.me/submissions/735d79ba-196e-4986-943d-e7d2e7b0384f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplOrbit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplOrbit_smul_symplCons_a513fc6e72e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplOrbit_symplCons_one_zero_81f42b193b60

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open PSymplOrbit
namespace GroundTheory.Heights₂.Heights
namespace SymplOrbit
theorem _root_.solution (h1 : SymplExtMem.Statement) (h2 : SymplExtVecMul.Statement)
    (h3 : SymplTwoRow.Statement) (h4 : SymplGcd.Statement) (h5 : SymplCons.Statement) :
    SymplOrbit.Statement := by
  intro n
  induction n with
  | zero =>
    intro v
    obtain ⟨c, a', b', x, y, ha, hb, hxy⟩ := h4 (v (Sum.inl 0)) (v (Sum.inr 0))
    have hE := h1 ℤ 0 a' b' (-y) x 1 (by linarith) (Submonoid.one_mem _)
    refine ⟨_, hE, c, ?_⟩
    have htail : symplTail v = 0 := funext fun z => z.elim (fun i => i.elim0) (fun i => i.elim0)
    have hrow : symplExt a' b' (-y) x (1 : Matrix (Fin 0 ⊕ Fin 0) (Fin 0 ⊕ Fin 0) ℤ) (Sum.inl 0) =
        symplCons a' b' 0 :=
      rfl
    rw [hrow, smul_symplCons, ← ha, ← hb, smul_zero, ← htail]
    exact ((h5 ℤ 0).1 v).symm
  | succ n ih =>
    intro v
    obtain ⟨Q, hQ, m', hw⟩ := ih (symplTail v)
    obtain ⟨c, a', b', x, y, ha, hb, hxy⟩ := h4 (v (Sum.inl 0)) (v (Sum.inr 0))
    obtain ⟨k, c'', d'', x', y', hc, hm, hxy'⟩ := h4 c m'
    obtain ⟨P₂, hP₂, hrow₂⟩ := h3 n c'' d'' x' y' hxy'
    have hE₁ := h1 ℤ (n + 1) a' b' (-y) x 1 (by linarith) (Submonoid.one_mem _)
    have hE₂ := h1 ℤ (n + 1) 1 0 0 1 Q (by ring) hQ
    refine ⟨P₂ * symplExt 1 0 0 1 Q * symplExt a' b' (-y) x 1,
      Submonoid.mul_mem _ (Submonoid.mul_mem _ hP₂ hE₂) hE₁, k, ?_⟩
    have e1 : symplCons c 0 (symplTail v) ᵥ* symplExt a' b' (-y) x 1 = v := by
      rw [h2, vecMul_one]
      simp only [zero_mul, add_zero]
      rw [← ha, ← hb]
      exact (h5 ℤ (n + 1)).1 v
    have e2 : symplCons c 0 (symplCons m' 0 0) ᵥ* symplExt 1 0 0 1 Q = symplCons c 0 (symplTail v) := by
      rw [h2]
      simp only [mul_one, mul_zero, add_zero]
      congr 1
      have hs : symplCons m' 0 (0 : Fin n ⊕ Fin n → ℤ) = m' • symplCons 1 0 0 := by
        rw [smul_symplCons]; simp
      rw [hs, smul_vecMul, symplCons_one_zero, single_one_vecMul, hw]
      rfl
    have e3 : k • P₂ (Sum.inl 0) = symplCons c 0 (symplCons m' 0 0) := by
      rw [hrow₂, hc, hm, smul_symplCons, smul_symplCons]
      simp
    rw [mul_apply_eq_vecMul, mul_apply_eq_vecMul, ← smul_vecMul, ← smul_vecMul, e3, e2, e1]
end SymplOrbit
end GroundTheory.Heights₂.Heights
