-- Prove2me | solution 1 for PadicInt.exists_finiteFlat_kummerHopf_withConv_aeval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4540930d-b211-5ad8-8a64-90e75a61c819

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_PadicInt_KummerCarrier
import Theorems.Thm_PadicInt_KummerCarrier_bialgebra_axioms
import Theorems.Thm_PadicInt_KummerCarrier_exists_antipode
import Theorems.Thm_PadicInt_KummerCarrier_evalAt_bijective_convHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_exists_finiteFlat_kummerHopf_withConv_aeval

open scoped NNReal TensorProduct
open PadicInt.KummerCarrier

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
        ∃ F : H → ZMod p → Polynomial ℤ_[p],
          ∀ (i j : ZMod p) (h : H),
            (ψ (i, j)) h
              = Polynomial.aeval (ζ ^ i.val * η ^ j.val) (F h j) := by

  have hu' : ‖u‖ ≤ 1 := le_of_eq (by rw [← NNReal.coe_one, ← hu]; rfl)
  let uZ : ℤ_[p] := ⟨u, hu'⟩
  have huZ_norm : ‖uZ‖ = 1 := by
    show (‖u‖₊ : ℝ) = 1; rw [hu, NNReal.coe_one]
  have huZ_unit : IsUnit uZ := PadicInt.isUnit_iff.mpr huZ_norm
  let u₀ : ℤ_[p]ˣ := huZ_unit.unit
  have hu₀ : ((u₀ : ℤ_[p]) : ℚ_[p]) = u := rfl

  obtain ⟨hcoassoc, hrT, hlT, hcocomm⟩ := PadicInt.KummerCarrier.bialgebra_axioms p u₀
  letI bialg : Bialgebra ℤ_[p] (Carrier p u₀) :=
    Bialgebra.ofAlgHom (Δ p u₀) (ε p u₀) hcoassoc hrT hlT

  obtain ⟨S', hSr, hSl⟩ := PadicInt.KummerCarrier.exists_antipode p u₀
  letI hopf : HopfAlgebra ℤ_[p] (Carrier p u₀) := {
    antipode := S'
    mul_antipode_rTensor_comul := hSr
    mul_antipode_lTensor_comul := hSl }

  haveI hCoc : Coalgebra.IsCocomm ℤ_[p] (Carrier p u₀) :=
    ⟨LinearMap.ext fun h => hcocomm h⟩

  have hη' : η ^ p = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) (u₀ : ℤ_[p]) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p])]
    refine hη.trans (congrArg _ ?_)
    exact hu₀.symm
  obtain ⟨ψ₀, hψbij, hψeval, hψΔ⟩ :=
    PadicInt.KummerCarrier.evalAt_bijective_convHom p u₀ ζ η hζ hη'

  let ψ : (ZMod p × ZMod p) ≃ WithConv (Carrier p u₀ →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) :=
    (Equiv.ofBijective ψ₀ hψbij).trans (WithConv.equiv _).symm
  have hψof : ∀ x, (ψ x).ofConv = ψ₀ x := fun _ => rfl

  refine ⟨Carrier p u₀, inferInstance, hopf, ?_, ?_, hCoc, ψ, ?_, polyLift p u₀, ?_⟩
  · exact inferInstance
  · exact inferInstance
  ·
    intro a b
    apply WithConv.ext
    rw [hψof, AlgHom.convMul_def, WithConv.ofConv_toConv, hψof, hψof]
    have hΔeq : Bialgebra.comulAlgHom ℤ_[p] (Carrier p u₀) = Δ p u₀ :=
      AlgHom.ext fun _ => rfl
    rw [hΔeq]
    exact (hψΔ a b).symm
  ·
    intro i j h
    obtain ⟨hw, heq⟩ := hψeval i j
    show (ψ (i, j)).ofConv h = _
    rw [hψof, heq, evalAt_eq_aeval_polyLift]

end S_PadicInt_exists_finiteFlat_kummerHopf_withConv_aeval
end P2MW
export P2MW.S_PadicInt_exists_finiteFlat_kummerHopf_withConv_aeval (solution)
