-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_norm_le_pow_1bb8f3f89542
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:10:02.827453+00:00
-- url     : https://prove2.me/submissions/3ccc22fb-8e83-4d06-a5f8-587d273e7157

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocB
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] [CharZero Ω]
variable [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l)
variable {j} {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
include hj
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (g : G E Ω) (hg : g ∈ Dec (F := E) A) (z : Ω) (n : ℕ)
    (h : ‖j z‖ ≤ ‖((l : ℕ) : PadicAlgCl l)‖ ^ n) : ‖j (g z)‖ ≤ ‖((l : ℕ) : PadicAlgCl l)‖ ^ n := by
  have hl0 : ((l : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hl.out.ne_zero
  have hlpos : 0 < ‖((l : ℕ) : PadicAlgCl l)‖ := by
    rw [norm_pos_iff, ← map_natCast j]
    exact (map_ne_zero j).mpr hl0
  have h1 : z / ((l : ℕ) : Ω) ^ n ∈ A := by
    rw [hj, map_div₀, map_pow, map_natCast, norm_div, norm_pow]
    exact div_le_one_of_le₀ h (by positivity)
  have hg' : g • A = A := MulAction.mem_stabilizer_iff.mp hg
  have h2 : g (z / ((l : ℕ) : Ω) ^ n) ∈ A := by
    rw [← hg', ← AlgEquiv.smul_def]
    exact ValuationSubring.smul_mem_pointwise_smul g _ A h1
  rw [map_div₀, map_pow, map_natCast, hj, map_div₀, map_pow, map_natCast, norm_div, norm_pow] at h2
  exact (div_le_one (by positivity)).mp h2
end Formalism.BasicNotions.Examples₂.LB
