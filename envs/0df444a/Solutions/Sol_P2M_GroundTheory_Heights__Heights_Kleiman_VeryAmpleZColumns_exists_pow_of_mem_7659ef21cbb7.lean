-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_exists_pow_of_mem_7659ef21cbb7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:36:11.654149+00:00
-- url     : https://prove2.me/submissions/ba47e3e8-0eef-494a-96d3-919c13df8340

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZColumnsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZColumns
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_pow_mono_40872ba2f21e

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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ}
variable {G : SubSystem S x E} {H : SubSystem S x Ω} {h : Fin (r + 1) → Ω} {I : Chart x}
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
theorem _root_.solution (hH : ∀ j, h j ∈ H.sub I) {J : Chart h} {e : E}
    (he : e ∈ secsOnZChart G H h I J) :
    ∃ n, ∀ m, n ≤ m → xProd J ^ m • e ∈ (G.twist (H.pow (J.1.card * m))).sub I := by
  suffices h0 : ∃ n, xProd J ^ n • e ∈ (G.twist (H.pow (J.1.card * n))).sub I by
    obtain ⟨n, hn⟩ := h0
    refine ⟨n, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact pow_mono hH hn k
  induction he using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨0, by rw [smul_zero]; exact zero_mem _⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨n1, h1⟩ := hy
    obtain ⟨n2, h2⟩ := hy'
    refine ⟨n1 + n2, ?_⟩
    rw [smul_add]
    refine add_mem (pow_mono hH h1 n2) ?_
    have := pow_mono hH h2 n1
    rwa [add_comm n2 n1] at this
  | smul s y _ hy =>
    obtain ⟨n, hn⟩ := hy
    refine ⟨n, ?_⟩
    rw [smul_comm]
    exact Submodule.smul_of_tower_mem _ s hn
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
