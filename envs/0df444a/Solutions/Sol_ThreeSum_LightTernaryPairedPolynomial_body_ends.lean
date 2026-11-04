-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPolynomial.body_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:49:20.293583+00:00
-- url     : https://prove2.me/submissions/5979c729-023a-4388-8a0e-34bf974b93e8

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_polynomial_value
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_bound_polynomial
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_compile_safe


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPolynomial
open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators
namespace ThreeSum.LightTernaryPairedPolynomial
theorem _root_.solution (m : ℕ) (T : Quad m → ℤ) (σ : State) {lim : Limits} {P : Program} {depth : ℕ}
    (U : ℤ) (hU : 0≤U)
    (hSafe : ∀ j, (atoms m j).Safe lim σ)
    (hAbs : ∀ j, |(atoms m j).val σ|≤U)
    (hWord : (polynomial m).coefficient*(U+1)^(polynomial m).degree≤lim.word)
    (hRead : ∀ q, (atomExpr m q).val σ=T q) :
    Ends lim P depth (body m) σ (time m) (fun τ => τ.loc 0=value T ∧ τ.mem=σ.mem) := by
  have hbound := ((polynomial m).bound_polynomial hU).trans hWord
  have hs := (polynomial m).compile_safe (atoms m) σ hU hSafe hAbs hbound
  apply Ends.set hs (by unfold time; omega)
  exact ⟨polynomial_value m T σ hRead,rfl⟩
end ThreeSum.LightTernaryPairedPolynomial
