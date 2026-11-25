-- Prove2me | solution 1 for ReciprocityTheory.PGsh.isPtDer_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:16:05.88049+00:00
-- url     : https://prove2.me/submissions/fe8e7950-e409-410b-a933-cd2f0f875f02

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
namespace ReciprocityTheory.PGsh
theorem _root_.solution {δ : A →ₗ[R] R} (h1 : δ 1 = 0)
    (h2 : ∀ f ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2, δ f = 0) : IsPtDer δ := by
  intro f g
  set a := Coalgebra.counit (R := R) f
  set b := Coalgebra.counit (R := R) g
  have hf : f - algebraMap R A a ∈ RingHom.ker (Bialgebra.counitAlgHom R A) := by
    simp [RingHom.mem_ker, a]
  have hg : g - algebraMap R A b ∈ RingHom.ker (Bialgebra.counitAlgHom R A) := by
    simp [RingHom.mem_ker, b]
  have hfg := h2 _ (by rw [pow_two]; exact Ideal.mul_mem_mul hf hg)
  have e : f * g = (f - algebraMap R A a) * (g - algebraMap R A b) + a • g + b • f - (a * b) • 1 := by
    simp only [Algebra.smul_def, map_mul, mul_one]; ring
  rw [e, map_sub, map_add, map_add, hfg, map_smul, map_smul, map_smul, h1, smul_eq_mul,
    smul_eq_mul, smul_eq_mul]
  ring
end ReciprocityTheory.PGsh
