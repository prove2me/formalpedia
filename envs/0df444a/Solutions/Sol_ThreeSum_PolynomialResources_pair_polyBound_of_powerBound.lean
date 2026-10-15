-- Prove2me | solution 1 for ThreeSum.PolynomialResources.pair_polyBound_of_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:44:43.172229+00:00
-- url     : https://prove2.me/submissions/947b7079-54bd-49a9-9dcd-f17c334f5634

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

section


/-!
# A polynomial bound in the parameters fits in a word

The running-time claims hold at every word size W ≥ b (log₂ p₁ + ⋯ + log₂ p_r + 1), where p₁, …, p_r
are the parameters of the instance and the slope b is chosen with the program (`Admissible`).  A
light program states its limits as a polynomial in the parameters,
`polyBound s k params` = 2^s ((p₁ + 1) ⋯ (p_r + 1))^k.

The main fact is `polyBound_le`: this bound is at most 2^W as soon as b ≥ s + k r + k.  Each factor
p + 1 is at most 2^(log₂ p + 1) (`prod_succ_le`), so with S the sum of the logarithms the bound is
at most 2^(s + k (S + r)), and s + k (S + r) ≤ (s + k r + k) (S + 1) ≤ W.
-/

@[expose] public section

namespace Light

open ThreeSumApsp.WordRam



















































/-- A number that is at most A (n + 1)^e with e ≤ k has a bound of this form in n. -/
theorem le_polyBound_of_le_pow {n A s m e k : ℕ} (he : e ≤ k) (h : m ≤ A * (n + 1) ^ e) :
    m ≤ polyBound (s + Nat.size A) k [n] := by
  have hA : A ≤ 2 ^ (s + Nat.size A) :=
    (Nat.lt_size_self A).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hn : (n + 1) ^ e ≤ (n + 1) ^ k := Nat.pow_le_pow_right (by omega) he
  have hbound : polyBound (s + Nat.size A) k [n] = 2 ^ (s + Nat.size A) * (n + 1) ^ k := by
    simp [polyBound]
  rw [hbound]
  exact h.trans (Nat.mul_le_mul hA hn)

























end Light

end
end

section


/-!
# From proved resource envelopes to the compiler's polynomial limits

An eventual power bound supplies a single polynomial valid at every input
size, by explicitly absorbing its finitely many exceptions. Multiplying
by a fixed power of the input magnitude then gives the exact two-parameter
`Light.PolyNeed` required by the verified compiler. These lemmas do not
supply resource envelopes for an algorithm; callers must prove those.
-/

namespace ThreeSum.PolynomialResources

open StageBounds Filter Real
open scoped Topology

noncomputable section

theorem natural_polynomial_of_powerBound {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) :
    ∃ C k : ℕ, ∀ n : ℕ, f n ≤ C*(n+1)^k := by
  let k : ℕ := ⌈a+1⌉₊
  have hk : a+1 ≤ (k : ℝ) := Nat.le_ceil _
  have he : ∀ᶠ n : ℕ in atTop, f n ≤ n^k := by
    filter_upwards [hf 1 (by norm_num),eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hh := hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hk)
    rw [Real.rpow_natCast] at hh
    exact_mod_cast hh
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp he
  let C : ℕ := 1+∑ i ∈ Finset.range N, f i
  have hC : 1 ≤ C := by dsimp [C]; omega
  refine ⟨C,k,fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact ((hN n hn).trans (Nat.pow_le_pow_left (by omega) k)).trans
      (Nat.le_mul_of_pos_left _ hC)
  · have hh : f n ≤ ∑ i ∈ Finset.range N, f i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    have hsmall : f n ≤ C := by dsimp [C]; omega
    exact hsmall.trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega)))

theorem polyBound_of_powerBound {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) :
    ∃ s k : ℕ, ∀ n : ℕ, f n ≤ Light.polyBound s k [n] := by
  obtain ⟨C,k,h⟩ := natural_polynomial_of_powerBound hf
  exact ⟨Nat.size C,k,fun n => by
    simpa only [zero_add] using Light.le_polyBound_of_le_pow (s := 0) le_rfl (h n)⟩

theorem pair_polyBound_of_powerBound_sourceProof {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) (e : ℕ) :
    ∃ s k : ℕ, ∀ n U : ℕ, f n*(U+1)^e ≤ Light.polyBound s k [n,U] := by
  obtain ⟨s,k,h⟩ := polyBound_of_powerBound hf
  refine ⟨s,k+e,fun n U => ?_⟩
  have hn : (n+1)^k ≤ (n+1)^(k+e) := Nat.pow_le_pow_right (by omega) (by omega)
  have hU : (U+1)^e ≤ (U+1)^(k+e) := Nat.pow_le_pow_right (by omega) (by omega)
  have hf' : f n ≤ 2^s*(n+1)^k := by simpa only [Light.polyBound,List.map_cons,
    List.map_nil,List.prod_cons,List.prod_nil,mul_one] using h n
  calc
    _ ≤ (2^s*(n+1)^k)*(U+1)^e := Nat.mul_le_mul_right _ hf'
    _ ≤ (2^s*(n+1)^(k+e))*(U+1)^(k+e) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hn) hU
    _ = Light.polyBound s (k+e) [n,U] := by simp [Light.polyBound,mul_pow,mul_assoc]

























end
end ThreeSum.PolynomialResources

end


theorem solution : ∀ {f : Nat → Nat} {a : Real},
  ThreeSum.StageBounds.PowerBound f a →
    ∀ (e : Nat),
      ∃ (s : Nat) (k : Nat),
        ∀ (n U : Nat),
          @LE.le.{0} Nat instLENat
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (f n)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) U
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                e))
            (Light.polyBound s k (@List.cons.{0} Nat n (@List.cons.{0} Nat U (@List.nil.{0} Nat)))) := by
  exact @ThreeSum.PolynomialResources.pair_polyBound_of_powerBound_sourceProof

#print axioms solution
