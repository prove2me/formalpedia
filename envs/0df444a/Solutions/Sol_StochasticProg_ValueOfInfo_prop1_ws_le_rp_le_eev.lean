-- Prove2me | solution 1 for StochasticProg.ValueOfInfo.prop1_ws_le_rp_le_eev
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T11:47:42.325795+00:00
-- url     : https://prove2.me/submissions/5ac0b429-24d8-48c2-832b-bfd0161e6ba2

import Mathlib
import Definitions.Def_StochasticProg_ValueOfInfo_Instance
import Definitions.Def_StochasticProg_ValueOfInfo_RP

set_option autoImplicit false

theorem voi_bsum_mono_aux {ι : Type*} [Fintype ι] (f g : ι → EReal) (h : ∀ i, f i ≤ g i) :
    StochasticProg.ValueOfInfo.bsum f ≤ StochasticProg.ValueOfInfo.bsum g := by
  unfold StochasticProg.ValueOfInfo.bsum
  by_cases hg : ∃ i, g i = ⊤
  · rw [if_pos hg]; exact le_top
  · have hf : ¬ ∃ i, f i = ⊤ := by
      rintro ⟨i, hi⟩
      apply hg
      refine ⟨i, top_le_iff.mp ?_⟩
      rw [← hi]; exact h i
    rw [if_neg hf, if_neg hg]
    exact Finset.sum_le_sum (fun i _ => h i)

open StochasticProg.ValueOfInfo in
theorem solution {n1 d K : ℕ} (I : Instance n1 d K)
    (xBar : Fin n1 → ℝ) (hxBar_mem : xBar ∈ I.K1)
    (hxBar_opt : I.z xBar (xiBar I) = EV I) :
    WS I ≤ RP I ∧ RP I ≤ EEV I xBar := by
  constructor
  · unfold WS RP
    refine le_iInf₂ (fun x hx => ?_)
    unfold expect
    apply voi_bsum_mono_aux
    intro k
    apply mul_le_mul_of_nonneg_left
    · exact iInf₂_le x hx
    · exact_mod_cast I.p_nonneg k
  · unfold RP EEV
    exact iInf₂_le xBar hxBar_mem

