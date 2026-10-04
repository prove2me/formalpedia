-- Prove2me | solution 1 for ProcessingNetworks.PacketNetworks.rps_fluid_model_eq_pf_fluid_model
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:24:12.353038+00:00
-- url     : https://prove2.me/submissions/7e83f1ff-27bb-4284-8abc-86e3cd102aed

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSFluidModel

namespace ProcessingNetworks.PacketNetworks.RPSPFCE

open ProcessingNetworks.PacketNetworks

def cfg : LinkConfigData 1 1 where
  A := 1
  hA := fun j => ⟨0, by fin_cases j; rfl, fun k _ => Subsingleton.elim k 0⟩
  hA0 := fun j k h => absurd (by fin_cases j; fin_cases k; rfl) h
  C := ∅

def dat : PacketNetworkData 1 1 := ⟨id, fun _ => none⟩

def fr : FixedRoutingData 1 1 where
  dat := dat
  u_id := rfl
  cfg := cfg
  linkDesig := id
  A_desig := fun k i => by fin_cases k; fin_cases i; rfl

theorem h121 : SatisfiesAssumption121 fr.dat :=
  ⟨fun i => ⟨i, rfl⟩, fun n js hc => by have := hc 0; simp [fr, dat] at this⟩

noncomputable def Dh (t : ℝ) : Fin 1 → ℝ := fun _ => if t < 0 then 5 else 0

theorem psi_zero (y : Fin 1 → ℝ) (k : Fin 1) :
    ProportionalFairness.psi (hullFinset fr.cfg.C) y k = 0 := by
  unfold ProportionalFairness.psi
  have : ¬ ∃ x, ProportionalFairness.IsPFMaximizer (hullFinset fr.cfg.C) y x := by
    rintro ⟨x, hx, -⟩
    simp [hullFinset, fr, cfg] at hx
  split_ifs <;> rfl

theorem hsol : IsRPSFluidModelSolution fr {0} 0 Dh (fun t _ => t) (fun _ _ => 1) := by
  refine ⟨⟨fun t ht i => ?_, by simp, fun _ _ _ => zero_le_one, fun t ht j => ?_, fun t _ => by simp,
    ⟨fun s _ a b hab => hab, 1, fun s _ t1 t2 _ h12 => ?_⟩⟩, fun t ht i _ => ?_⟩
  · have : Dh t = 0 := funext fun _ => by simp [Dh, not_lt.mpr ht]
    rw [this, Matrix.mulVec_zero]; simp
  · simp [Dh, not_lt.mpr ht]
  · rw [abs_of_nonneg (by linarith)]; linarith
  · rw [psi_zero, mul_zero]
    refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds ht] with u hu
    simp [Dh, not_lt.mpr hu.le]

end ProcessingNetworks.PacketNetworks.RPSPFCE

open ProcessingNetworks.PacketNetworks in
theorem solution : ¬ (∀ {I K : ℕ} (fr : FixedRoutingData I K) (h121 : SatisfiesAssumption121 fr.dat)
    (S : Finset (Fin I → ℕ)) (lam : Fin I → ℝ)
    (Dh : ℝ → Fin I → ℝ) (Th : ℝ → (Fin I → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ)
    (h : IsRPSFluidModelSolution fr S lam Dh Th Zh),
    ProcessingNetworks.ProportionalFairness.IsPFFluidModelSolution (toPFData fr lam)
      (fun t i => lam i * t + ∑ k, RouteMatrix fr k i * Dh t k) Dh Dh Zh) := by
  intro h
  obtain ⟨-, -, -, -, ⟨-, hmono, -⟩, -⟩ := h RPSPFCE.fr RPSPFCE.h121 {0} 0 _ _ _ RPSPFCE.hsol
  have := hmono (show (-1 : ℝ) ≤ 0 by norm_num) 0
  simp [RPSPFCE.Dh] at this
  linarith


