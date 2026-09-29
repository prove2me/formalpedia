-- Prove2me | solution 1 for StochasticProg.ValueOfInfo.prop5a_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T11:47:42.104605+00:00
-- url     : https://prove2.me/submissions/ff30b8fa-d7ea-4a65-b102-e98f21246d62

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
theorem voi_prop1_aux {n1 d K : ℕ} (I : Instance n1 d K)
    (xBar : Fin n1 → ℝ) (hxBar_mem : xBar ∈ I.K1) :
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

theorem voi_bsub_nonneg_aux {a b : EReal} (h : b ≤ a) :
    (0 : EReal) ≤ StochasticProg.ValueOfInfo.bsub a b := by
  unfold StochasticProg.ValueOfInfo.bsub StochasticProg.ValueOfInfo.badd
  split_ifs with hc
  · exact le_top
  · obtain ⟨ha, hb⟩ := not_or.mp hc
    have hb' : b ≠ ⊥ := by
      intro hb0
      apply hb
      rw [hb0]
      rfl
    rw [← sub_eq_add_neg]
    exact (EReal.sub_nonneg (Or.inl ha) (Or.inr hb')).mpr h

open StochasticProg.ValueOfInfo in
theorem solution {n1 d K : ℕ} (I : Instance n1 d K)
    (xBar : Fin n1 → ℝ) (hxBar_mem : xBar ∈ I.K1)
    (hxBar_opt : I.z xBar (xiBar I) = EV I) :
    (0 : EReal) ≤ EVPI I ∧ (0 : EReal) ≤ VSS I xBar := by
  obtain ⟨h1, h2⟩ := voi_prop1_aux I xBar hxBar_mem
  exact ⟨voi_bsub_nonneg_aux h1, voi_bsub_nonneg_aux h2⟩
