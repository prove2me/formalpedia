-- Prove2me | solution 1 for Paper.Hypergraph.fractional_cover_minimax
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:51.453013+00:00
-- url     : https://prove2.me/submissions/1264a634-9d47-4ca2-bead-29f99e996555

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_cover_duality
import Theorems.Thm_Paper_Hypergraph_full_fractional_separator
import Theorems.Thm_Paper_Hypergraph_mem_separatorCube
import Theorems.Thm_Paper_Hypergraph_compact_separatorCube
import Theorems.Thm_Paper_Hypergraph_convex_separatorCube
import Theorems.Thm_Paper_Hypergraph_compact_modularCube
import Theorems.Thm_Paper_Hypergraph_convex_modularCube
import Theorems.Thm_Paper_Hypergraph_separator_restrict
import Theorems.Thm_Paper_Hypergraph_modular_restrict

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {γ : ℕ → ℝ}
    (hγ : H.EdgeWeight γ) {θ : ℝ} (hθ : 0 < θ ∧ θ < 1) :
    ∃ w, H.ModularWeight w ∧ ∀ x, H.FractionalBalanced γ θ x →
      H.beta θ γ ≤ ∑ v ∈ H.vertices, w v * x v := by
  let X := H.separatorCube γ θ
  let W := H.modularCube
  let f : (ℕ → ℝ) → (ℕ → ℝ) → ℝ := fun x w => ∑ v ∈ H.vertices, w v * x v
  have neX : X.Nonempty := ⟨_, H.separator_restrict (H.full_fractional_separator hγ hθ).1⟩
  have neW : W.Nonempty := ⟨0, by simp [W, modularCube]⟩
  have cX : Convex ℝ X := H.convex_separatorCube (fun e he => (hγ.1 e he).1) θ
  have cW : Convex ℝ W := H.convex_modularCube
  have contX (w : ℕ → ℝ) : Continuous (fun x => f x w) :=
    continuous_finsetSum _ (fun v _ => continuous_const.mul (continuous_apply v))
  have contW (x : ℕ → ℝ) : Continuous (f x) :=
    continuous_finsetSum _ (fun v _ => (continuous_apply v).mul continuous_const)
  have linX (w x y : ℕ → ℝ) (a b : ℝ) : f (a • x + b • y) w = a * f x w + b * f y w := by
    simp [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, sum_add_distrib, mul_sum, mul_left_comm]
  have linW (x w z : ℕ → ℝ) (a b : ℝ) : f x (a • w + b • z) = a * f x w + b * f x z := by
    simp [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib, mul_sum, mul_assoc]
  have cv (w : ℕ → ℝ) : ConvexOn ℝ X (fun x => f x w) := by
    refine ⟨cX, ?_⟩
    intro x hx y hy a b ha hb hab
    exact (linX w x y a b).le
  have cc (x : ℕ → ℝ) : ConcaveOn ℝ W (f x) := by
    refine ⟨cW, ?_⟩
    intro w hw z hz a b ha hb hab
    exact (linW x w z a b).ge
  obtain ⟨x0, hx0, w0, hw0, hsaddle⟩ := Sion.exists_isSaddlePointOn
    neX cX (H.compact_separatorCube γ θ)
    (fun w _ => (contX w).continuousOn.lowerSemicontinuousOn)
    (fun w _ => (cv w).quasiconvexOn)
    cW neW H.compact_modularCube
    (fun x _ => (contW x).continuousOn.upperSemicontinuousOn)
    (fun x _ => (cc x).quasiconcaveOn)
  have hx0bal : H.FractionalBalanced γ θ x0 := (H.mem_separatorCube hx0.1).mp hx0
  obtain ⟨w, hw, hdual, _⟩ := H.cover_duality hx0bal.1
  have hbeta : H.beta θ γ ≤ H.coverCost x0 := by
    refine csInf_le ⟨0, ?_⟩ ⟨x0, hx0bal, rfl⟩
    rintro r ⟨x, hx, rfl⟩
    exact H.coverCost_nonneg x
  refine ⟨w0, ⟨fun v => hw0.1.1 v, hw0.2⟩, ?_⟩
  intro x hx
  have hs := hsaddle _ (H.separator_restrict hx) _ (H.modular_restrict hw)
  have hleft : f x0 (fun v => if v ∈ H.vertices then w v else 0) = H.coverCost x0 := by
    rw [hdual]
    exact sum_congr rfl (fun v hv => by simp [hv])
  have hright : f (fun v => if v ∈ H.vertices then x v else 0) w0 =
      ∑ v ∈ H.vertices, w0 v * x v := by
    exact sum_congr rfl (fun v hv => by simp [hv])
  rw [hleft, hright] at hs
  exact hbeta.trans hs
end Paper.Hypergraph
