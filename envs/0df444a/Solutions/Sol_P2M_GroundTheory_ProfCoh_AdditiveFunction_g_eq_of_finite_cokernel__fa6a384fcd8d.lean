-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_AdditiveFunction_g_eq_of_finite_cokernel__fa6a384fcd8d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:37.302552+00:00
-- url     : https://prove2.me/submissions/ddc41b7e-4e2b-4df7-be2b-930e84bf7ff0

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq_of_finite_cokernel
import Theorems.Thm_GroundTheory_ProfCoh_exact_connecting_modNMap
import Theorems.Thm_GroundTheory_ProfCoh_finite_of_exact
import Theorems.Thm_GroundTheory_ProfCoh_finite_torsN_of_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open Representation
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction Γ A] [DistribMulAction Γ B] (f : B →+ A)
    (hfγ : ∀ (γ : Γ) (b : B), f (γ • b) = γ • f b) (hf : Function.Injective f)
    [Finite (A ⧸ f.range)] [Finite (ModN A l)] [Finite (TorsN A l)] : d.g A = d.g B := by
  have hfh : Function.Exact f (QuotientAddGroup.mk' f.range) :=
    fun y => by rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; rfl
  have hh := QuotientAddGroup.mk'_surjective f.range
  have := finite_torsN_of_injective (n := l) hf
  have : Finite (ModN B l) :=
    finite_of_exact (connecting hh hfh hf).toAddMonoidHom (modNMap l f).toAddMonoidHom
      (exact_connecting_modNMap hh hfh hf)
  exact d.g_eq_of_finite_cokernel f hfγ hf
end GroundTheory.ProfCoh.AdditiveFunction
