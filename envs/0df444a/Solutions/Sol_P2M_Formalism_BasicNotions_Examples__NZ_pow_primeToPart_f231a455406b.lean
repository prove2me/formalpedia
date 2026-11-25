-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_pow_primeToPart_f231a455406b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:32:37.943945+00:00
-- url     : https://prove2.me/submissions/15b64dd7-17d4-401d-aafd-0acdcdcc49c1

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {M : Type*} [Monoid M] {ℓ : ℕ} (hℓ : ℓ.Prime) (x : M) (hx : IsOfFinOrder x) :
    primeToPart ℓ x ^ (ℓ ^ (orderOf x).factorization ℓ) = x ^ (ℓ ^ (orderOf x).factorization ℓ) := by
  set n := orderOf x with hn
  have hn0 : n ≠ 0 := (orderOf_pos_iff.mpr hx).ne'
  set a := n.factorization ℓ
  set m := n / ℓ ^ a with hm
  have hnm : ℓ ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n ℓ
  have hc : Nat.Coprime (ℓ ^ a) m := (Nat.coprime_ordCompl hℓ hn0).pow_left a
  set u := (((ℓ ^ a : ℕ) : ZMod m)⁻¹).val
  have h1 : ((ℓ ^ a * u : ℕ) : ZMod m) = 1 := by
    have hm0 : NeZero m := ⟨fun h => hn0 (by rw [← hnm, h, mul_zero])⟩
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one _ hc
  have h2 : ℓ ^ a * u ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff, h1, Nat.cast_one]
  unfold primeToPart
  rw [← pow_mul]
  have h3 : ℓ ^ a * u * ℓ ^ a ≡ ℓ ^ a [MOD n] := by
    have := h2.mul_left' (ℓ ^ a)
    rw [mul_one, hnm] at this
    rwa [mul_comm (ℓ ^ a * u) (ℓ ^ a)]
  rw [← pow_mod_orderOf x (ℓ ^ a * u * ℓ ^ a), ← pow_mod_orderOf x (ℓ ^ a)]
  exact congrArg _ h3
end Formalism.BasicNotions.Examples₂.NZ
