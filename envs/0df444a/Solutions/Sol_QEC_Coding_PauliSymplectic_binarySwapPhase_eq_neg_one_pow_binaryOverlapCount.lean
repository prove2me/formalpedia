-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.binarySwapPhase_eq_neg_one_pow_binaryOverlapCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:12:44.562215+00:00
-- url     : https://prove2.me/submissions/32232053-cd96-4086-8104-afc1a07274ae

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Classical
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution (P : Binary ι) :
    binarySwapPhase P.vector.xPart P.vector.zPart =
      (-1 : Complex) ^ binaryOverlapCount P := by
  change
    (∏ i ∈ zSupport P,
      if i ∈ xSupport P then (-1 : Complex) else 1) =
        (-1 : Complex) ^ (zSupport P ∩ xSupport P).card
  calc
    (∏ i ∈ zSupport P,
        if i ∈ xSupport P then (-1 : Complex) else 1) =
        (∏ i ∈ (zSupport P).filter (fun i => i ∈ xSupport P),
          (-1 : Complex)) *
        ∏ i ∈ (zSupport P).filter (fun i => i ∉ xSupport P),
          (1 : Complex) :=
      Finset.prod_ite (s := zSupport P) (p := fun i => i ∈ xSupport P)
        (fun _ => (-1 : Complex)) (fun _ => (1 : Complex))
    _ = (-1 : Complex) ^
        ((zSupport P).filter (fun i => i ∈ xSupport P)).card := by
          rw [Finset.prod_const, Finset.prod_const, one_pow, mul_one]
    _ = (-1 : Complex) ^ (zSupport P ∩ xSupport P).card := by
          rw [Finset.filter_mem_eq_inter]
end QEC.Coding.PauliSymplectic
