-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_LocAinf___ne_one_c5617a838e7d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:39:03.643887+00:00
-- url     : https://prove2.me/submissions/46ea3ffc-c71b-4e7d-bc59-f565b0975eff

import Mathlib
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementPC
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Theorems.Thm_P2M_Formalism_BasicNotions_LocAinf__2_prim_5d93beb9df99

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions
open Loc
open Formalism.BasicNotions.LocAinf
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
namespace Formalism.BasicNotions.LocAinf
theorem _root_.solution : AI.ε ≠ 1 := by
  classical
  intro hε
  have h2 := AI.ε_coeff 2
  rw [hε, map_one, ← map_one (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)})), eq_comm,
    Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h2
  obtain ⟨b, hb⟩ := h2
  have hprim := AI.ζ2_prim
  have hev := Polynomial.eval_one_cyclotomic_prime_pow (R := OC l) (p := l) 1
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hprim, Polynomial.eval_prod] at hev
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev
  set s := primitiveRoots (l ^ 2) (OC l)
  have hfac : ∀ μ ∈ s, ∃ c, 1 - μ = (1 - AI.ζ 2) * c := by
    intro μ hμ
    have hμ' := (mem_primitiveRoots (pow_pos (Fact.out : l.Prime).pos 2)).mp hμ
    obtain ⟨i, -, rfl⟩ := hprim.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    refine ⟨∑ j ∈ Finset.range i, AI.ζ 2 ^ j, ?_⟩
    linear_combination geom_sum_mul (AI.ζ 2) i
  let c : OC l → OC l := fun μ => if h : μ ∈ s then Classical.choose (hfac μ h) else 0
  have hc : ∀ μ ∈ s, 1 - μ = (1 - AI.ζ 2) * c μ := by
    intro μ hμ
    simp only [c, dif_pos hμ]
    exact Classical.choose_spec (hfac μ hμ)
  rw [Finset.prod_congr rfl hc, Finset.prod_mul_distrib, Finset.prod_const] at hev
  have hcard : s.card = l * (l - 1) := by
    rw [hprim.card_primitiveRoots, show l ^ 2 = l ^ (1 + 1) by ring,
      Nat.totient_prime_pow_succ (Fact.out : l.Prime), pow_one]
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hN : 2 ≤ s.card := by
    rw [hcard]
    have : 1 ≤ l - 1 := by omega
    nlinarith
  have h1 : 1 - AI.ζ 2 = -b * ((l : ℕ) : OC l) := by linear_combination hb
  rw [h1, mul_pow, show s.card = (s.card - 2) + 2 by omega, pow_add, pow_add] at hev
  have hl0 : ((l : ℕ) : OC l) ≠ 0 := by
    intro h0
    apply OC_l_not_unit l
    have := congrArg (fun x : OC l => (x : PadicComplex l)) h0
    simp at this
    exact absurd this (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  apply OC_l_not_unit l
  refine isUnit_iff_exists_inv.mpr ⟨(-b) ^ (s.card - 2 + 2) *
    ((l : ℕ) : OC l) ^ (s.card - 2) * ∏ μ ∈ s, c μ, ?_⟩
  apply mul_left_cancel₀ hl0
  linear_combination hev
end Formalism.BasicNotions.LocAinf
