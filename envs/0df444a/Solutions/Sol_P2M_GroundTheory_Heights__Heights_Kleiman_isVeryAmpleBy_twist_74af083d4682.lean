-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmpleBy_twist_74af083d4682
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:10.853344+00:00
-- url     : https://prove2.me/submissions/92242135-9034-48b7-8bf2-1de1780c6c4e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleTwistGenerated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_mem_ampleRing_twist_d5a9cb6bd913
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_eq_pow_ebcff08057ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_sub_eq_mul_d7e23ae652ec


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
open scoped Pointwise
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable {L G : SubSystem k x Ω} {r₁ s₁ : ℕ} {h : Fin (r₁ + 1) → Ω} {g : Fin (s₁ + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {R : ℕ} (hL : IsVeryAmpleBy L h) (hgs : ∀ j, g j ∈ G.secs)
    (hgg : ∀ I, Submodule.span (chartRing k x I) (Set.range g) = G.sub I)
    (e : Fin (R + 1) ≃ Fin (r₁ + 1) × Fin (s₁ + 1)) :
    IsVeryAmpleBy (L.twist G) (fun p => h (e p).1 * g (e p).2) := by
  have hgI : ∀ j I, g j ∈ G.sub I := fun j I => (Submodule.mem_iInf _).mp (hgs j) I
  have hmono : ∀ (l : Fin (r₁ + 1)) (j : Fin (s₁ + 1)) (I : Chart x) (z : Ω),
      z ∈ ampleChart L 1 (h l) I → z ∈ ampleChart (L.twist G) 1 (h l * g j) I := by
    intro l j I z hz
    obtain ⟨n, hn⟩ := hz
    refine ⟨n, ?_⟩
    rw [one_mul, SubSystem.pow_sub_eq_pow] at hn ⊢
    rw [SubSystem.twist_sub_eq_mul, mul_pow (L.sub I) (G.sub I), mul_pow (h l) (g j), ← mul_assoc]
    exact Submodule.mul_mem_mul hn (Submodule.pow_mem_pow _ (hgI j I) n)
  have hmonoR : ∀ (l : Fin (r₁ + 1)) (j : Fin (s₁ + 1)) (z : Ω),
      z ∈ ampleRing L 1 (h l) → z ∈ ampleRing (L.twist G) 1 (h l * g j) := fun l j z hz =>
    Set.mem_iInter.mpr fun I => hmono l j I z (Set.mem_iInter.mp hz I)
  refine ⟨fun p => ?_, fun I => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · refine (Submodule.mem_iInf _).mpr fun I => ?_
    change h (e p).1 * g (e p).2 ∈ (L.twist G).sub I
    rw [SubSystem.twist_sub_eq_mul]
    exact Submodule.mul_mem_mul ((Submodule.mem_iInf _).mp (hL.mem_secs _) I) (hgI _ I)
  · rw [SubSystem.twist_sub_eq_mul, ← hL.generates I, ← hgg I, Submodule.span_mul_span]
    congr 1
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact Set.mul_mem_mul ⟨_, rfl⟩ ⟨_, rfl⟩
    · intro hz
      obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Set.mem_mul.mp hz
      exact ⟨e.symm (a, b), by simp⟩
  · intro a ha
    refine mem_of_mem_ampleRing_twist (B := ampleBase (S := k) (fun q => h (e q).1 * g (e q).2) p)
      hL hgg (left_ne_zero_of_mul hp) (right_ne_zero_of_mul hp) (fun a' b' => ?_) ha
    unfold ampleBase
    apply Algebra.subset_adjoin
    exact ⟨e.symm (a', b'), by simp⟩
  · obtain ⟨n, A, Bv, JJ, hA, hBv, hsum, hcov⟩ := hL.affine (e p).1 (left_ne_zero_of_mul hp)
    refine ⟨n, A, Bv, JJ, fun i => hmonoR _ _ _ (hA i), fun i => hmonoR _ _ _ (hBv i), hsum,
      fun i I => ?_⟩
    obtain ⟨e', he'⟩ := hcov i I
    exact ⟨e', hmono _ _ _ _ he'⟩
end GroundTheory.Heights₂.Heights.Kleiman
