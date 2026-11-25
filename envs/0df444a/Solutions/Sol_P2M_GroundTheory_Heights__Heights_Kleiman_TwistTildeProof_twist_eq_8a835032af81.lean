-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistTildeProof_twist_eq_8a835032af81
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:18:27.072945+00:00
-- url     : https://prove2.me/submissions/60b09919-c3ba-4de7-b6a7-799419ddb226

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistTildeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistTilde

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.TwistTildeProof
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.TwistTildeProof
theorem _root_.solution (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω)
    (I : Chart x) : ((M.tildeSys 0).twist (Q.tildeSys 0)).sub I = (prod M Q).tilde 0 I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ Q.tilde 0 I at hq
    change y ∈ M.tilde 0 I at hy
    refine smul_mem_of_mem_span ?_ hq hy
    rintro _ ⟨q, s₁, a₁, e₁, hs₁, hse₁, hq, ha₁, rfl⟩ _ ⟨m, s₂, a₂, e₂, hs₂, hse₂, hm, ha₂, rfl⟩
    refine Submodule.subset_span ⟨q • m, s₁ * s₂, a₁ + a₂, e₁ + e₂, mul_mem hs₁ hs₂, hse₁.mul hse₂,
      Submodule.subset_span ⟨a₁, a₂, q, m, hq, hm, rfl, rfl⟩, by push_cast; omega, ?_⟩
    simp only [smul_eq_mul, smul_smul, map_mul, mul_inv]
    congr 1; ring
  · obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, s, a, e, hs, hse, hp, hae, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    refine Submodule.span_induction (p := fun p _ => (aeval x s)⁻¹ • p ∈
      ((M.tildeSys 0).twist (Q.tildeSys 0)).sub I) ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨a', b', q, m, hq, hm, hab, rfl⟩
      set k := a'.toNat
      set j := (-a').toNat
      have hkj : (k : ℤ) - j = a' := Int.toNat_sub_toNat_neg a'
      have hq' : (aeval x (X i ^ k : Poly S N))⁻¹ • (aeval x (X i ^ j : Poly S N) • q) ∈
          Q.tilde 0 I := by
        have h := Q.smul_mem j a' _ q (isHomogeneous_X_pow i j) hq
        rw [show a' + (j : ℤ) = k by omega] at h
        exact Submodule.subset_span ⟨_, X i ^ k, k, k, pow_mem (X_mem_monos hi) k,
          isHomogeneous_X_pow i k, h, by simp, rfl⟩
      have hm' : (aeval x (s * X i ^ j))⁻¹ • (aeval x (X i ^ k : Poly S N) • m) ∈ M.tilde 0 I := by
        have h := M.smul_mem k b' _ m (isHomogeneous_X_pow i k) hm
        exact Submodule.subset_span ⟨_, s * X i ^ j, b' + k, e + j,
          mul_mem hs (pow_mem (X_mem_monos hi) j), hse.mul (isHomogeneous_X_pow i j), h,
          by push_cast; omega, rfl⟩
      have heq : (aeval x s)⁻¹ • (q • m) = ((aeval x (X i ^ k : Poly S N))⁻¹ •
          (aeval x (X i ^ j : Poly S N) • q)) • ((aeval x (s * X i ^ j))⁻¹ •
          (aeval x (X i ^ k : Poly S N) • m)) := by
        simp only [smul_eq_mul, smul_smul, map_mul, map_pow, aeval_X]
        congr 1
        field_simp
      rw [heq]
      exact Submodule.subset_span ⟨_, hq', _, hm', rfl⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_of_tower_mem _ r ha
end GroundTheory.Heights₂.Heights.Kleiman.TwistTildeProof
