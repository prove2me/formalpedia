-- Prove2me | solution 1 for WilliamsonShmoys.planar_finite_step_completion__p2m_3b9c1b25_36f2_49fb_9760_e5ee7be0caf4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:21:19.714587+00:00
-- url     : https://prove2.me/submissions/adf2035f-b3ce-4b4e-a412-499949d4a829

import Mathlib
import Theorems.Thm_bounded_strict_progress_has_terminal__p2m_a9a5aac4_cf42_46e5_abca_ec8765edbc1f_a1
import Theorems.Thm_edgeFinset_card_strict_of_extension__p2m_a9a5aac4_cf42_46e5_abca_ec8765edbc1f_a2

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (J : SimpleGraph V) (hJ : P J)
    (hstep : ∀ G : SimpleGraph V, P G →
      letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
        fun K => Classical.decRel K.Adj
      ∀ u v : V, ¬ Nonempty (G.Walk u v) →
        ∃ H : SimpleGraph V,
          P H ∧ G.edgeFinset ⊆ H.edgeFinset ∧ H.Adj u v) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ H : SimpleGraph V,
      P H ∧
      (∀ u v : V, Nonempty (H.Walk u v)) ∧
      J.edgeFinset ⊆ H.edgeFinset := by
  classical
  let R : SimpleGraph V → Prop :=
    fun G => P G ∧ J.edgeFinset ⊆ G.edgeFinset
  let μ : SimpleGraph V → Nat := fun G => G.edgeFinset.card
  have hbase : ∃ G : SimpleGraph V, R G := by
    exact ⟨J, hJ, Finset.Subset.rfl⟩
  have hbound : ∀ G : SimpleGraph V, R G → μ G ≤ Fintype.card (Sym2 V) := by
    intro G hG
    dsimp [μ]
    exact Finset.card_le_univ G.edgeFinset
  have hprogress :
      ∀ G : SimpleGraph V, R G →
        ¬ (∀ u v : V, Nonempty (G.Walk u v)) →
          ∃ H : SimpleGraph V, R H ∧ μ G < μ H := by
    intro G hG hdisconnected
    have hpair : ∃ u v : V, ¬ Nonempty (G.Walk u v) := by
      simpa only [not_forall] using hdisconnected
    obtain ⟨u, v, hwalk⟩ := hpair
    obtain ⟨H, hPH, hsub, hAdj⟩ := hstep G hG.1 u v hwalk
    have hstrict := edgeFinset_card_strict_of_extension__p2m_a9a5aac4_cf42_46e5_abca_ec8765edbc1f_a2
      G H u v hsub hAdj hwalk
    exact ⟨H, ⟨hPH, Finset.Subset.trans hG.2 hsub⟩, hstrict⟩
  obtain ⟨H, hRH, hconn⟩ :=
    bounded_strict_progress_has_terminal__p2m_a9a5aac4_cf42_46e5_abca_ec8765edbc1f_a1
      R (fun G : SimpleGraph V => ∀ u v : V, Nonempty (G.Walk u v))
      μ (Fintype.card (Sym2 V)) hbase hbound hprogress
  exact ⟨H, hRH.1, hconn, hRH.2⟩