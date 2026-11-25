-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.single_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:03:32.346929+00:00
-- url     : https://prove2.me/submissions/02e1211f-f3c8-4f27-b269-517816c28189

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
open ZetaZeros.D.EllReg.WF
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.WF
theorem _root_.solution {m : ℕ} (p : List (Fin d) × (E d → ℂ)) (hp : p.1.length < m) (g : E d → ℂ) (y : E d) :
    ∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d,
      (if p.1 = List.ofFn w then p.2 y else 0) * dw (List.ofFn w) g y = p.2 y * dw p.1 g y := by
  obtain ⟨v, c⟩ := p
  dsimp only at hp ⊢
  have key : ∀ (n : ℕ) (w : Fin n → Fin d), (if v = List.ofFn w then c y else 0) * ZetaZeros.D.EllReg.dw (List.ofFn w) g y
      = if v = List.ofFn w then c y * ZetaZeros.D.EllReg.dw v g y else 0 := by
    intro n w
    by_cases h : v = List.ofFn w
    · rw [if_pos h, if_pos h, h]
    · rw [if_neg h, if_neg h, zero_mul]
  simp only [key]
  rw [Finset.sum_eq_single v.length]
  · rw [Finset.sum_eq_single v.get]
    · rw [if_pos (List.ofFn_get v).symm]
    · intro w _ hw
      rw [if_neg]
      intro h
      apply hw
      have h' : List.ofFn w = List.ofFn v.get := by rw [← h, List.ofFn_get]
      exact List.ofFn_injective h'
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro n _ hn
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg]
    intro h
    apply hn
    rw [h, List.length_ofFn]
  · intro h
    exact absurd (Finset.mem_range.mpr hp) h
end ZetaZeros.D.EllReg.WF
