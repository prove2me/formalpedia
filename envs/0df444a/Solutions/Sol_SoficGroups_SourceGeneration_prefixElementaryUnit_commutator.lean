-- Prove2me | solution 1 for SoficGroups.SourceGeneration.prefixElementaryUnit_commutator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/3dd5b34c-2799-422b-8a20-b36729377e1b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceGeneration_prefixElementaryEntry_mul

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.SourceGeneration
open scoped commutatorElement
namespace SoficGroups.SourceGeneration
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι) (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : BinaryLeavitt) :
    ⁅prefixElementaryUnit E i j hij a,
      prefixElementaryUnit E j k hjk b⁆ =
      prefixElementaryUnit E i k hik (a * b) := by
  let x := prefixElementaryEntry E i j a
  let y := prefixElementaryEntry E j k b
  let z := prefixElementaryEntry E i k (a * b)
  have hxx : x * x = 0 := by
    change prefixElementaryEntry E i j a *
      prefixElementaryEntry E i j a = 0
    rw [prefixElementaryEntry_mul, if_neg hij.symm]
  have hyy : y * y = 0 := by
    change prefixElementaryEntry E j k b *
      prefixElementaryEntry E j k b = 0
    rw [prefixElementaryEntry_mul, if_neg hjk.symm]
  have hyx : y * x = 0 := by
    change prefixElementaryEntry E j k b *
      prefixElementaryEntry E i j a = 0
    rw [prefixElementaryEntry_mul, if_neg hik.symm]
  have hxy : x * y = z := by
    change prefixElementaryEntry E i j a *
      prefixElementaryEntry E j k b =
      prefixElementaryEntry E i k (a * b)
    rw [prefixElementaryEntry_mul, if_pos rfl]
  have hzx : z * x = 0 := by
    change prefixElementaryEntry E i k (a * b) *
      prefixElementaryEntry E i j a = 0
    rw [prefixElementaryEntry_mul, if_neg hik.symm]
  have hzy : z * y = 0 := by
    change prefixElementaryEntry E i k (a * b) *
      prefixElementaryEntry E j k b = 0
    rw [prefixElementaryEntry_mul, if_neg hjk.symm]
  have hzz : z * z = 0 := by
    change prefixElementaryEntry E i k (a * b) *
      prefixElementaryEntry E i k (a * b) = 0
    rw [prefixElementaryEntry_mul, if_neg hik.symm]
  have hxz : x * z = 0 := by
    change prefixElementaryEntry E i j a *
      prefixElementaryEntry E i k (a * b) = 0
    rw [prefixElementaryEntry_mul, if_neg hij.symm]
  have hyz : y * z = 0 := by
    change prefixElementaryEntry E j k b *
      prefixElementaryEntry E i k (a * b) = 0
    rw [prefixElementaryEntry_mul, if_neg hik.symm]
  apply Units.ext
  change (1 + x) * (1 + y) * (1 - x) * (1 - y) = 1 + z
  noncomm_ring [hxx, hyy, hyx, hxy, hzx, hzy, hzz, hxz, hyz]
end SoficGroups.SourceGeneration
