-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_mem_secsOnZChart_911075d7a669
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:57:57.090189+00:00
-- url     : https://prove2.me/submissions/b8036d08-a403-40d3-b43f-3db62acbbfd5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_smul_mem_twist_pow_5ff4c39bbc0c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_prod_pow_mem_3b44bad7dd98

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
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ} {h : Fin (r + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
theorem _root_.solution (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x)
    (hh : ∀ l, h l ∈ H.sub I) (J : Chart h) (e : E) :
    e ∈ secsOnZChart F H h I J ↔
      ∃ n : ℕ, xProd J ^ n • e ∈ (F.twist (H.pow (J.1.card * n))).sub I := by
  refine ⟨fun he => ?_, fun he => Submodule.subset_span he⟩
  refine Submodule.span_induction (p := fun e _ =>
    ∃ n : ℕ, xProd J ^ n • e ∈ (F.twist (H.pow (J.1.card * n))).sub I) (fun _ h => h) ?_ ?_ ?_ he
  · exact ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  · rintro a b _ _ ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have e1 : xProd J ^ (n + m) • (a + b) =
        xProd J ^ m • (xProd J ^ n • a) + xProd J ^ n • (xProd J ^ m • b) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm m n]
    rw [e1]
    refine Submodule.add_mem _ ?_ ?_
    · have := smul_mem_twist_pow F H I hn (prod_pow_mem H I hh J.1 m)
      rwa [← Nat.mul_add] at this
    · have := smul_mem_twist_pow F H I hm (prod_pow_mem H I hh J.1 n)
      rwa [← Nat.mul_add, Nat.add_comm m n] at this
  · rintro c a _ ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have e1 : xProd J ^ n • c • a =
        (⟨algebraMap S Ω c, Subalgebra.algebraMap_mem _ _⟩ : chartRing S x I) • (xProd J ^ n • a) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul Ω c a, smul_smul, smul_smul, mul_comm]
    rw [e1]
    exact Submodule.smul_mem _ _ hn
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
