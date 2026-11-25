-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_exists_pow_eq_89fec43dff7b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:42:00.073739+00:00
-- url     : https://prove2.me/submissions/bb003fd9-1018-47f0-aa49-a4806c018674

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_pow_primeToPart_f231a455406b

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
theorem _root_.solution {M : Type*} [Monoid M] {ℓ : ℕ} (hℓ : ℓ.Prime) (x y : M) (hx : IsOfFinOrder x)
    (hy : IsOfFinOrder y) (h : primeToPart ℓ x = primeToPart ℓ y) : ∃ c : ℕ, x ^ ℓ ^ c = y ^ ℓ ^ c := by
  refine ⟨(orderOf x).factorization ℓ + (orderOf y).factorization ℓ, ?_⟩
  have h1 := pow_primeToPart hℓ x hx
  have h2 := pow_primeToPart hℓ y hy
  rw [pow_add, pow_mul, ← h1, h, ← pow_mul, mul_comm, pow_mul, h2, ← pow_mul]
end Formalism.BasicNotions.Examples₂.NZ
