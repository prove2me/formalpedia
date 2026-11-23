-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants.flowMat_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:25.271229+00:00
-- url     : https://prove2.me/submissions/934b0605-8ed5-4c77-b9d0-987bd35623d6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants
open MajorantConjugateTransfer
variable {r : ℕ} (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ)
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants
theorem _root_.solution (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (a b : ℂ) :
    X.flowMat ξ τ (a + b) = X.flowMat ξ τ a * X.flowMat ξ τ b := by
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin r) (Fin r) ℂ,
      V = Matrix.of fun a b => τ.1 (ξ a) * ∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k)) := ⟨_, rfl⟩
  have hM : ∀ s : ℂ, X.flowMat ξ τ s = 1 - (I * (X.c τ : ℂ) * s) • V := by
    intro s
    ext a b
    simp only [Data.flowMat, hV, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul]
    ring
  have h0 : ∑ k, τ.1 (ξ k) * ∑ m, τ.1 (X.Gm k m) * conj (τ.1 (ξ m)) = 0 := by
    calc _ = hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) := by
          simp only [hermC, Data.emb, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
      _ = 0 := hiso
  have hVV : V * V = 0 := by
    ext a b
    simp only [hV, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    calc ∑ k, τ.1 (ξ a) * (∑ m, τ.1 (X.Gm k m) * conj (τ.1 (ξ m))) *
          (τ.1 (ξ k) * ∑ m, τ.1 (X.Gm b m) * conj (τ.1 (ξ m)))
        = τ.1 (ξ a) * (∑ m, τ.1 (X.Gm b m) * conj (τ.1 (ξ m))) *
          ∑ k, τ.1 (ξ k) * ∑ m, τ.1 (X.Gm k m) * conj (τ.1 (ξ m)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := by rw [h0, mul_zero]
  simp only [hM, sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hVV, smul_zero, sub_zero, mul_add, add_smul]
  abel
end ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants
