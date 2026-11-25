-- Prove2me | solution 1 for P2M_GlobalTheory_DPEval2___mul_bda55975e5d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:51:06.774752+00:00
-- url     : https://prove2.me/submissions/02209bd1-1fec-43e4-87e2-dac74a2dbc34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowerEvalTwoVarsRingHom
import Theorems.Thm_GlobalTheory_DPEval2_bv_mul
import Theorems.Thm_GlobalTheory_DPEval2_mul_mem
import Theorems.Thm_P2M_GlobalTheory_DPEval2___bv_1fa775b7a6d8
import Theorems.Thm_P2M_GlobalTheory_DPEval2___add_038c2ae041a5
import Theorems.Thm_P2M_GlobalTheory_DPEval2___zsmul_54cdf8776ef8
import Theorems.Thm_P2M_GlobalTheory_DPEval2___nsmul_635e58ae52b9
import Theorems.Thm_P2M_GlobalTheory_DPEval2___zero_cec7b4073406

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DPEval2
variable {B : Type} [CommRing B] (u v : ℕ → B)
namespace GlobalTheory.DPEval2
theorem _root_.solution (hu : ∀ m n, u m * u n = ((m + n).choose m : B) * u (m + n))
    (hv : ∀ m n, v m * v n = ((m + n).choose m : B) * v (m + n))
    {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) :
    φ u v (x * y) = φ u v x * φ u v y := by
  refine Submodule.span_induction₂ (p := fun x y hx hy ↦ φ u v (x * y) = φ u v x * φ u v y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    rw [bv_mul, φ_nsmul u v _ (bv_mem _), φ_bv, φ_bv, φ_bv, nsmul_eq_mul]
    calc ((((p.1 + q.1).choose p.1 * (p.2 + q.2).choose p.2 : ℕ)) : B) * (u (p + q).1 * v (p + q).2)
        = (((p.1 + q.1).choose p.1 : B) * u (p.1 + q.1)) * (((p.2 + q.2).choose p.2 : B) * v (p.2 + q.2)) := by
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_mul]; ring
      _ = u p.1 * v p.2 * (u q.1 * v q.2) := by rw [← hu, ← hv]; ring
  · intro y _; simp [φ_zero]
  · intro y _; simp [φ_zero]
  · intro x y z hx hy hz h1 h2
    rw [add_mul, φ_add u v (mul_mem hx hz) (mul_mem hy hz), φ_add u v hx hy, h1, h2, add_mul]
  · intro x y z hx hy hz h1 h2
    rw [mul_add, φ_add u v (mul_mem hx hy) (mul_mem hx hz), φ_add u v hy hz, h1, h2, mul_add]
  · intro r x y hx hy h
    rw [smul_mul_assoc, φ_zsmul u v r (mul_mem hx hy), φ_zsmul u v r hx, h, smul_mul_assoc]
  · intro r x y hx hy h
    rw [mul_smul_comm, φ_zsmul u v r (mul_mem hx hy), φ_zsmul u v r hy, h, mul_smul_comm]
end GlobalTheory.DPEval2
