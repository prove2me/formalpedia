-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_p__sqZero_400d97111e57
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:10.689555+00:00
-- url     : https://prove2.me/submissions/e26ec0ef-6454-4f36-bb87-a8a729ffe42e

import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Definitions.Def_ReciprocityTheory_DualLattices_SmKerSurj
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
namespace ReciprocityTheory.PGsh
theorem _root_.solution : (FP.p₁ π Dp.π).SqZero := by
  refine ⟨fun a => ⟨(ι₁ π Dp).1 a, rfl⟩, ?_⟩
  rw [sq, ← le_bot_iff]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  rw [RingHom.mem_ker] at hx hy
  have hx0 : x.1.1 = 0 := hx
  have hy0 : y.1.1 = 0 := hy
  have hx2 : x.1.2 ∈ Ideal.span {Dp.η} := by
    rw [← Dp.ker_eq, RingHom.mem_ker, ← FP.mem π Dp.π x, hx0, map_zero]
  have hy2 : y.1.2 ∈ Ideal.span {Dp.η} := by
    rw [← Dp.ker_eq, RingHom.mem_ker, ← FP.mem π Dp.π y, hy0, map_zero]
  rw [Ideal.mem_bot]
  apply Subtype.ext
  apply Prod.ext
  · show x.1.1 * y.1.1 = 0
    rw [hx0, zero_mul]
  · show x.1.2 * y.1.2 = 0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hx2
    obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.1 hy2
    rw [← hc, ← hc']
    calc c * Dp.η * (c' * Dp.η) = c * c' * (Dp.η * Dp.η) := by ring
      _ = 0 := by rw [Dp.η_sq, mul_zero]
end ReciprocityTheory.PGsh
