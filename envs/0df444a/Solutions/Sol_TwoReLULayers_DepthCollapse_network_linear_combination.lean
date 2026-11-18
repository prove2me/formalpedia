-- Prove2me | solution 1 for TwoReLULayers.DepthCollapse.network_linear_combination
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:05:35.286504+00:00
-- url     : https://prove2.me/submissions/9c3a912a-6757-493b-b68f-6507173d7d46

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

open TwoReLULayers.DepthCollapse
open Finset
noncomputable section

private def zeroNetwork {n : ℕ} (R : Subfield ℝ) : Network2 R n :=
  ⟨0, 0, Fin.elim0, Fin.elim0, ⟨Fin.elim0, 0⟩⟩

private theorem zero_mem_network {n : ℕ} (R : Subfield ℝ) :
    (0 : E n → ℝ) ∈ ReLU2 R n := by
  refine ⟨zeroNetwork R, fun x => ?_⟩
  change (0 : ℝ) = (0 : ℝ) + ∑ i : Fin 0, _
  simp

private theorem smul_mem_network {n : ℕ} (R : Subfield ℝ) (c : R)
    (f : E n → ℝ) (hf : f ∈ ReLU2 R n) :
    (fun x => (c : ℝ) * f x) ∈ ReLU2 R n := by
  obtain ⟨N, hN⟩ := hf
  refine ⟨⟨N.width₁, N.width₂, N.first, N.second,
    ⟨fun j => c * N.output.weight j, c * N.output.bias⟩⟩, fun x => ?_⟩
  change (c : ℝ) * f x = _
  rw [hN]
  simp [Network2.eval, AffineScalar.eval, Subfield.coe_mul, mul_add, Finset.mul_sum,
    mul_assoc]

private def addNetworks {n : ℕ} {R : Subfield ℝ} (N M : Network2 R n) : Network2 R n where
  width₁ := N.width₁ + M.width₁
  width₂ := N.width₂ + M.width₂
  first := Fin.append N.first M.first
  second := Fin.append
    (fun j => ⟨Fin.append (N.second j).weight (fun _ => 0), (N.second j).bias⟩)
    (fun j => ⟨Fin.append (fun _ => 0) (M.second j).weight, (M.second j).bias⟩)
  output := ⟨Fin.append N.output.weight M.output.weight, N.output.bias + M.output.bias⟩

private theorem addNetworks_eval {n : ℕ} {R : Subfield ℝ}
    (N M : Network2 R n) (x : E n) :
    (addNetworks N M).eval x = N.eval x + M.eval x := by
  dsimp only [addNetworks, Network2.eval, AffineScalar.eval, relu, affineEval]
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Subfield.coe_zero,
    zero_mul, Finset.sum_const_zero, add_zero, zero_add, Subfield.coe_add]
  ring

private theorem add_mem_network {n : ℕ} (R : Subfield ℝ) (f g : E n → ℝ)
    (hf : f ∈ ReLU2 R n) (hg : g ∈ ReLU2 R n) :
    (fun x => f x + g x) ∈ ReLU2 R n := by
  obtain ⟨N, hN⟩ := hf
  obtain ⟨M, hM⟩ := hg
  refine ⟨addNetworks N M, fun x => ?_⟩
  exact (congrArg₂ (· + ·) (hN x) (hM x)).trans (addNetworks_eval N M x).symm

theorem solution {n k : ℕ} (hn : 1 ≤ n) (R : Subfield ℝ)
    (c : Fin k → R) (f : Fin k → E n → ℝ) (hf : ∀ i, f i ∈ ReLU2 R n) :
    (fun x => ∑ i, (c i : ℝ) * f i x) ∈ ReLU2 R n := by
  induction k with
  | zero =>
    convert zero_mem_network (n := n) R using 1
    ext x
    simp
  | succ k ih =>
    have h := add_mem_network R _ _ (smul_mem_network R (c 0) (f 0) (hf 0))
      (ih (fun i => c i.succ) (fun i => f i.succ) (fun i => hf i.succ))
    simpa only [Fin.sum_univ_succ] using h
