-- Prove2me | solution 1 for PI.SqPair.LCP.split_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:20.384026+00:00
-- url     : https://prove2.me/submissions/94cfe46a-a81c-4769-be9a-14eb25dce9ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpPair
import Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_hyp
import Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_split
import Theorems.Thm_PI_SqPair_LCP_inert_isLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
open PI.SqPair.LocCartanPairW
namespace PI.SqPair.LCP
theorem _root_.solution (hS : SplitOff) : Split := by
  intro R _ _ R₀ ϖ hI κ _ _ A A' h k a hP hak x y v w hxx hyy hxy hv hw
  have := hI.dom
  have : IsLocalRing R := inert_isLocalRing hI
  obtain ⟨⟨hAh, -⟩, ⟨hAh', -⟩, hh⟩ := hP
  have hϖ : star ϖ = ϖ := (hI.fix ϖ).mp hI.pi_mem
  have hcard : Fintype.card κ + 2 = Fintype.card (Fin 2 ⊕ κ) := by
    simp [Fintype.card_sum, add_comm]
  obtain ⟨u, ui, A₁, huv, hvu, hu0, hu1, hG⟩ := hS R (Fin 2 ⊕ κ) κ hcard A hAh x y hxx hyy hxy
  have hs : ϖ ^ (2 * k) ≠ 0 := pow_ne_zero _ hI.pi_ne
  have hc : (starRingAut : R ≃+* R) (ϖ ^ (k - a)) * ϖ ^ (k + a) = ϖ ^ (2 * k) := by
    rw [map_pow, starRingAut_apply, hϖ, ← pow_add]
    congr 1
    omega
  obtain ⟨h1, h2, h3⟩ := cmp_hyp (starRingAut : R ≃+* R) A A' h _ hs hh (ϖ ^ (k - a)) (ϖ ^ (k + a))
    hc x y v w hv hw hxx hyy hxy
  obtain ⟨u', ui', A₁', huv', -, hu0', hu1', hG'⟩ :=
    hS R (Fin 2 ⊕ κ) κ hcard A' hAh' v w h1 h2 h3
  obtain ⟨h₂, hM, -⟩ := cmp_split (starRingAut : R ≃+* R) A A' h _ hh (ϖ ^ (k - a)) (ϖ ^ (k + a))
    (pow_ne_zero _ hI.pi_ne) (pow_ne_zero _ hI.pi_ne) x y v w hv hw u u' ui A₁ A₁' huv hvu hu0 hu1
    hu0' hu1' hG hG'
  refine ⟨u, u', A₁, A₁', h₂, ![ϖ ^ (k - a), ϖ ^ (k + a)], isUnit_det_of_right_inverse huv,
    isUnit_det_of_right_inverse huv', hG, hG', ?_⟩
  rw [← hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, huv, Matrix.one_mul]
end PI.SqPair.LCP
