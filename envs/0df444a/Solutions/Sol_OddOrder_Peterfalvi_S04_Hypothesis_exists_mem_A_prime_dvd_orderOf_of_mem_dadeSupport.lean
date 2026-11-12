-- Prove2me | solution 1 for OddOrder.Peterfalvi.S04.Hypothesis.exists_mem_A_prime_dvd_orderOf_of_mem_dadeSupport
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:13:50.832179+00:00
-- url     : https://prove2.me/submissions/455d9757-b5ea-405c-bcb0-cd5c09c9bc5f

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S04_DadeIsometryBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_TISubset
import Definitions.Def_OddOrder_GroupTheory_CoprimeConjugacy
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassFunction
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ZIrr
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Definitions.Def_OddOrder_Peterfalvi_S04_DadeHypothesisCore
import Definitions.Def_OddOrder_Peterfalvi_S04_DadeIsometryBasic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

-- ===== OddOrder/Peterfalvi/S04_DadeIsometryBasic.lean =====
namespace OddOrder.Peterfalvi.S04

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

namespace Hypothesis

variable {A A₁ : Set G} {L : Subgroup G}

variable [Fintype G]

/-- **Order of a Dade-support element**: every `x ∈ Ã(A)` — a conjugate of `a·h` with `a ∈ A`,
`h ∈ H(a)` — has a prime divisor of `orderOf a` dividing `orderOf x`.  The parts commute
(`H(a) ≤ C_G(a)`, `centralizer_eq_sup`) with coprime orders (`centralizer_coprime` at `b = a`,
since `a ∈ C_L(a)`), so `orderOf (a·h) = orderOf a · orderOf h`, and order is a conjugacy
invariant.  This is the order-theoretic half of Peterfalvi (13.19.a)-style support
disjointness: elements of `Ã(A(L))` carry a prime of `|L_F|`. -/
theorem _root_.solution (hyp : Hypothesis G A L)
    {x : G} (hx : x ∈ hyp.dadeSupport) :
    ∃ a ∈ A, ∃ r : ℕ, r.Prime ∧ r ∣ orderOf a ∧ r ∣ orderOf x := by
  rw [hyp.mem_dadeSupport_iff] at hx
  obtain ⟨a, h, hh, hconj⟩ := hx
  -- `h` centralizes `a` (`H(a) ≤ C_G(a)`)
  have hhc : h ∈ Subgroup.centralizer ({a.1} : Set G) := by
    rw [hyp.centralizer_eq_sup a]
    exact Subgroup.mem_sup_left hh
  have hcomm : Commute a.1 h :=
    (Subgroup.mem_centralizer_singleton_iff.mp hhc).symm
  -- `orderOf a ∣ |C_L(a)|` (self-centralizing) and `orderOf h ∣ |H(a)|`, coprime
  have haC : a.1 ∈ centralizerIn L a.1 := by
    rw [mem_centralizerIn]
    exact ⟨hyp.mem_L a.2, rfl⟩
  have hdvd_a : orderOf a.1 ∣ Nat.card (centralizerIn L a.1) :=
    Subgroup.orderOf_dvd_natCard _ haC
  have hdvd_h : orderOf h ∣ Nat.card (hyp.H a) :=
    Subgroup.orderOf_dvd_natCard _ hh
  have hcop : Nat.Coprime (orderOf h) (orderOf a.1) :=
    Nat.Coprime.coprime_dvd_right hdvd_a
      (Nat.Coprime.coprime_dvd_left hdvd_h (hyp.centralizer_coprime a a))
  -- a prime of `orderOf a` (`a ≠ 1`)
  have hane : orderOf a.1 ≠ 1 := fun h1 => hyp.ne_one a.2 (orderOf_eq_one_iff.mp h1)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hane
  refine ⟨a.1, a.2, r, hr, hrdvd, ?_⟩
  -- `orderOf x = orderOf (a·h) = orderOf a · orderOf h`
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hox : orderOf x = orderOf a.1 * orderOf h := by
    have hinj : orderOf ((MulAut.conj c).toMonoidHom (a.1 * h)) = orderOf (a.1 * h) :=
      orderOf_injective (MulAut.conj c).toMonoidHom (MulEquiv.injective _) _
    rw [← hc,
      show c * (a.1 * h) * c⁻¹ = (MulAut.conj c).toMonoidHom (a.1 * h) by
        simp [MulAut.conj_apply],
      hinj, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop.symm]
  rw [hox]
  exact hrdvd.trans (dvd_mul_right _ _)

end Hypothesis

end OddOrder.Peterfalvi.S04
