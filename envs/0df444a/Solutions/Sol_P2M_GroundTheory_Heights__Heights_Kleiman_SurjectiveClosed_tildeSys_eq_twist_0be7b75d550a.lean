-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_tildeSys_eq_twist_0be7b75d550a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:59:32.463433+00:00
-- url     : https://prove2.me/submissions/2c23fbc9-a6be-4bf6-bc94-af3a9429f6ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_twist_sub_eq_mul_482b06edabb9

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
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
theorem _root_.solution (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ) :
    M.tildeSys c = (M.tildeSys 0).twist (twistSys S x c) := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [twist_sub_eq_mul]
  change M.tilde c I = twistMod S x c I * M.tilde 0 I
  rw [twistMod_eq_span c I hi]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    rw [SetLike.mem_coe, Submodule.mem_span_singleton_mul]
    refine ⟨(x i ^ c)⁻¹ * ((aeval x s)⁻¹ • m), ?_, mul_inv_cancel_left₀ (zpow_ne_zero c hxi) _⟩
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · refine Submodule.subset_span ⟨m, s * X i ^ n, a, e + n, mul_mem hs (pow_mem (X_mem_monos hi) n),
        hse.mul (isHomogeneous_X_pow i n), hm, by push_cast; omega, ?_⟩
      simp only [smul_eq_mul, map_mul, map_pow, aeval_X, zpow_natCast, mul_inv]
      ring
    · refine Submodule.subset_span ⟨aeval x (X i ^ n : Poly S N) • m, s, a + n, e, hs, hse,
        M.smul_mem n a _ m (isHomogeneous_X_pow i n) hm, by omega, ?_⟩
      simp only [smul_eq_mul, map_pow, aeval_X, zpow_neg, zpow_natCast, inv_inv]
      ring
  · refine Submodule.mul_le.mpr fun g hg y hy => ?_
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hg
    have hy' : y ∈ Submodule.span (chartRing S x I) {y | ∃ (m : Ω) (s : Poly S N) (a : ℤ) (e : ℕ),
        s ∈ monos I.1 ∧ s.IsHomogeneous e ∧ m ∈ M.piece a ∧ a - e = 0 ∧ y = (aeval x s)⁻¹ • m} := hy
    have key : x i ^ c * y ∈ M.tilde c I := by
      refine Submodule.span_induction (p := fun y _ => x i ^ c * y ∈ M.tilde c I) ?_ ?_ ?_ ?_ hy'
      · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
        obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
        · refine Submodule.subset_span ⟨aeval x (X i ^ n : Poly S N) • m, s, a + n, e, hs, hse,
            M.smul_mem n a _ m (isHomogeneous_X_pow i n) hm, by omega, ?_⟩
          simp only [smul_eq_mul, map_pow, aeval_X, zpow_natCast]
          ring
        · refine Submodule.subset_span ⟨m, s * X i ^ n, a, e + n,
            mul_mem hs (pow_mem (X_mem_monos hi) n), hse.mul (isHomogeneous_X_pow i n), hm,
            by push_cast; omega, ?_⟩
          simp only [smul_eq_mul, map_mul, map_pow, aeval_X, zpow_neg, zpow_natCast, mul_inv]
          ring
      · rw [mul_zero]
        exact Submodule.zero_mem _
      · intro y y' _ _ h h'
        rw [mul_add]
        exact Submodule.add_mem _ h h'
      · intro r y _ h
        rw [chartRing_smul_def, mul_left_comm]
        exact (M.tilde c I).smul_mem r h
    rw [chartRing_smul_def, mul_assoc]
    exact (M.tilde c I).smul_mem b key
end GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
