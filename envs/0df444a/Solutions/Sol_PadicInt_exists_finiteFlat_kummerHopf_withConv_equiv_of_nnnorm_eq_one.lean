-- Prove2me | solution 1 for PadicInt.exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e0dd5742-5d66-5992-8a55-1cbc2c89fc1c

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_PadicInt_exists_finiteFlat_kummerHopf_withConv_aeval
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one
p2m_attr_erase "instance" "PadicInt.KummerCarrier.instFreeA PadicInt.KummerCarrier.instFiniteA"

open scoped NNReal

theorem solution
    (p : ℕ) [Fact p.Prime] (u : ℚ_[p]) (hu : ‖u‖₊ = 1)
    (ζ η : AlgebraicClosure ℚ_[p]) (hζ : IsPrimitiveRoot ζ p)
    (hη : η ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) u) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧
      Module.Flat ℤ_[p] H ∧
      Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ ψ : (ZMod p × ZMod p) ≃ WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
        (∀ a b, ψ (a + b) = ψ a * ψ b) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (e c : ℕ),
          σ ζ = ζ ^ e → σ η = ζ ^ c * η →
          ∀ (i j : ZMod p) (h : H),
            (ψ (e • i + c • j, j)) h = σ ((ψ (i, j)) h) := by
  obtain ⟨H, iCR, iHA, hFin, hFlat, hCoc, ψ, hψadd, F, hF⟩ :=
    PadicInt.exists_finiteFlat_kummerHopf_withConv_aeval p u hu ζ η hζ hη
  refine ⟨H, iCR, iHA, hFin, hFlat, hCoc, ψ, hψadd, ?_⟩
  intro σ e c hσζ hση i j h
  rw [hF (e • i + c • j) j h, hF i j h]

  let σZ : AlgebraicClosure ℚ_[p] ≃ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p] := σ.restrictScalars ℤ_[p]
  have hσZ : ∀ x, σ x = σZ x := fun _ => rfl
  rw [hσZ, ← Polynomial.aeval_algHom_apply σZ, ← hσZ]

  congr 1
  rw [map_mul, map_pow, map_pow, hσζ, hση, mul_pow, ← pow_mul, ← pow_mul,
    ← mul_assoc, ← pow_add]
  congr 1

  have hmod : ((e • i + c • j : ZMod p)) = ((e * i.val + c * j.val : ℕ) : ZMod p) := by
    push_cast
    simp only [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]
  rw [hmod, ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div (e * i.val + c * j.val) p, pow_add, pow_mul,
    hζ.pow_eq_one, one_pow, mul_one]

end S_PadicInt_exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one
end P2MW
export P2MW.S_PadicInt_exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one (solution)
