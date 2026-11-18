-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.inner_map_map_of_map_add_map_sub_map_smul_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-18T04:17:46.183891+00:00
-- url     : https://prove2.me/submissions/8d40adc2-08f5-4cc0-b74c-22dc577b2690

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    (f : H → K)
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsub : ∀ x y, f (x - y) = f x - f y)
    (hsmul : ∀ (c : Complex) x, f (c • x) = c • f x)
    (hnorm : ∀ x, ‖f x‖ = ‖x‖)
    (x y : H) : inner Complex (f x) (f y) = inner Complex x y := by
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  have hsubI : f x - (RCLike.I : Complex) • f y =
      f (x - (RCLike.I : Complex) • y) := by
    calc
      f x - (RCLike.I : Complex) • f y =
          f x - f ((RCLike.I : Complex) • y) := by rw [hsmul]
      _ = f (x - (RCLike.I : Complex) • y) :=
        (hsub x ((RCLike.I : Complex) • y)).symm
  have haddI : f x + (RCLike.I : Complex) • f y =
      f (x + (RCLike.I : Complex) • y) := by
    calc
      f x + (RCLike.I : Complex) • f y =
          f x + f ((RCLike.I : Complex) • y) := by rw [hsmul]
      _ = f (x + (RCLike.I : Complex) • y) :=
        (hadd x ((RCLike.I : Complex) • y)).symm
  rw [← hadd, ← hsub, hsubI, haddI]
  rw [hnorm, hnorm, hnorm, hnorm]
end QEC.Bounds.BPTCommutingProjectorModel
