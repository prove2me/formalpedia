-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_proof_abc43faba4fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:58:12.997944+00:00
-- url     : https://prove2.me/submissions/6f438639-076e-420d-8ecb-07052ab4c80b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConstantsDescend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConstantsDescend
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_nat_mul_mem_09250f2c5a61
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_primitive_9418c28bff33
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_mem_of_unique_extension_3c111369f05d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_agree_on_adjoin_74205cd88afe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
theorem _root_.solution : ConstantsDescend.Statement := by
  intro Ω _ _ R T hR hT H
  classical

  obtain ⟨S, hS⟩ := (Module.Finite.iff_fg (N := Subalgebra.toSubmodule T)).1 hT
  have hST : ∀ s ∈ S, s ∈ T := fun s hs => by
    have : s ∈ Subalgebra.toSubmodule T := hS ▸ Submodule.subset_span hs
    exact this
  have hTspan : ∀ t ∈ T, t ∈ Submodule.span ℤ (S : Set Ω) := fun t ht => by
    rw [hS]
    exact ht
  have hintQ : ∀ s ∈ S, IsIntegral ℚ s := fun s hs =>
    ((IsIntegral.of_finite ℤ (⟨s, hST s hs⟩ : T)).map T.val).tower_top

  obtain ⟨θ, hθint, hθT', hKθ⟩ := exists_primitive S hintQ
  have hθT : θ ∈ Algebra.adjoin ℚ (T : Set Ω) := Algebra.adjoin_mono (fun s hs => hST s hs) hθT'
  have hTθ : ∀ t ∈ T, t ∈ Algebra.adjoin ℚ {θ} := fun t ht => hKθ t <|
    Submodule.span_induction (p := fun x _ => x ∈ IntermediateField.adjoin ℚ (S : Set Ω))
      (fun x hx => IntermediateField.subset_adjoin ℚ _ hx) (IntermediateField.zero_mem _)
      (fun x y _ _ hx hy => IntermediateField.add_mem _ hx hy) (fun z x _ hx => zsmul_mem hx z) (hTspan t ht)

  obtain ⟨s, hs⟩ := hR
  have hAfg : (Algebra.adjoin ℚ (R : Set Ω)).FG := ⟨s, by rw [← hs, Algebra.adjoin_adjoin_of_tower]⟩
  haveI : Algebra.FiniteType ℚ (Algebra.adjoin ℚ (R : Set Ω)) := (Subalgebra.fg_iff_finiteType _).1 hAfg

  have hθA : θ ∈ Algebra.adjoin ℚ (R : Set Ω) := by
    refine mem_of_unique_extension _ θ hθint fun w w' hw => ?_
    obtain ⟨y, hy, hyθ⟩ := Subring.mem_map.1 (agree_on_adjoin R T _
      (Algebra.adjoin (Algebra.adjoin ℚ (R : Set Ω)) {θ}) (fun r hr => Algebra.subset_adjoin hr) θ
      (Algebra.subset_adjoin (Set.mem_singleton θ)) hTθ H w w' hw θ hθT)
    have : y = ⟨θ, Algebra.subset_adjoin rfl⟩ := Subtype.ext hyθ
    rw [← this]
    exact hy

  have hTA : ∀ t ∈ T, t ∈ Algebra.adjoin ℚ (R : Set Ω) := fun t ht =>
    (Algebra.adjoin_le (Set.singleton_subset_iff.2 hθA) : Algebra.adjoin ℚ {θ} ≤ _) (hTθ t ht)

  have hn : ∀ s ∈ S, ∃ n : ℕ, 0 < n ∧ (n : Ω) * s ∈ R := fun s hs => exists_nat_mul_mem R (hTA s (hST s hs))
  choose! n hn0 hnR using hn
  refine ⟨∏ s ∈ S, n s, Finset.prod_pos hn0, fun t ht => ?_⟩
  refine Submodule.span_induction (p := fun x _ => ((∏ s ∈ S, n s : ℕ) : Ω) * x ∈ R) ?_ ?_ ?_ ?_ (hTspan t ht)
  · intro x hx
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n hx
    rw [hk, Nat.cast_mul, mul_comm ((n x : ℕ) : Ω), mul_assoc]
    exact R.mul_mem (Subalgebra.natCast_mem R k) (hnR x hx)
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact R.add_mem hx hy
  · intro z x _ hx
    rw [mul_smul_comm]
    exact zsmul_mem hx z
end GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
