-- Prove2me | solution 1 for ReciprocityTheory.PGsh.sm_ker_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:52:03.657188+00:00
-- url     : https://prove2.me/submissions/31f60bb3-6c46-4c2a-bbc3-35a3571686fa

import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Definitions.Def_ReciprocityTheory_DualLattices_SmKerSurj
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair______56f01b043277
import Theorems.Thm_ReciprocityTheory_PGsh_FP_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
variable {R' R : LAlg R₀} (π : LHom R' R) (Dp : DualPair R)
variable {ξ : (R' : Type u)} (hsurj : Function.Surjective π.1)
  (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0)
namespace ReciprocityTheory.PGsh
theorem _root_.solution :
    Function.Surjective ((sm π Dp ξ hsurj hker hsq).1.toLinearMap.restrict
      (sm_ker π Dp hsurj hker hsq)) := by
  rintro ⟨b, hb⟩
  have hb' : b ∈ RingHom.ker π.1 := hb
  have hbξ : b ∈ Ideal.span {ξ} := by
    rw [← hker]
    exact hb'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hbξ
  have hmem : ((0 : (R' : Type u)), Dp.σ.1 (π.1 c) * Dp.η) ∈ fpSub π Dp.π := by
    rw [mem_fpSub]
    show π.1 0 = Dp.π.1 (Dp.σ.1 (π.1 c) * Dp.η)
    rw [map_zero, map_mul, Dp.π_η, mul_zero]
  have hk : (⟨_, hmem⟩ : (FP π Dp.π : Type u)) ∈ (FP.p₁ π Dp.π).ker := by
    show (0 : (R' : Type u)) = 0
    rfl
  refine ⟨⟨⟨_, hmem⟩, hk⟩, ?_⟩
  apply Subtype.ext
  show (0 : (R' : Type u)) + ell π ξ hsurj (Dp.κ (Dp.σ.1 (π.1 c) * Dp.η)) = c * ξ
  rw [Dp.κ_ση, ell_spec hsurj hker hsq, zero_add]
end ReciprocityTheory.PGsh
