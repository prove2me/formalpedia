-- Prove2me | solution 1 for RockafellianRelax.eq_A2_clusterPt_mem_argmin
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-07T13:52:30.093827+00:00
-- url     : https://prove2.me/submissions/ba470a71-4127-42fe-9a70-85c51c3f27b1

import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_PerspEpi_SeqEpiConv
import Mathlib.Topology.Bases

open Filter Topology RockafellianRelax

theorem solution {α : Type*} [TopologicalSpace α] [FirstCountableTopology α]
    (Ψ : ℕ → α → EReal) (ψ : α → EReal) (hepi : PerspEpi.SeqEpiConv Ψ ψ)
    (hdom : (AubinLipschitz.effDom ψ).Nonempty) (ε : ℕ → ℝ) (hε0 : ∀ ν, 0 ≤ ε ν)
    (hε : Tendsto ε atTop (𝓝 0)) (z : ℕ → α) (hz : ∀ ν, z ν ∈ epsArgmin (Ψ ν) (ε ν))
    (zhat : α) (hzhat : MapClusterPt zhat atTop z) :
    zhat ∈ argmin ψ := by
  classical
  obtain ⟨σ, hσ, hsub⟩ := hzhat.tendsto_subseq
  have hσat : Tendsto σ atTop atTop := hσ.tendsto_atTop
  let w (k : ℕ) : α := if k ∈ Set.range σ then z k else zhat
  have hw : Tendsto w atTop (𝓝 zhat) := by
    rw [tendsto_def]
    intro U hU
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hsub.eventually_mem hU)
    filter_upwards [eventually_ge_atTop (σ N)] with k hk
    change w k ∈ U
    by_cases h : k ∈ Set.range σ
    · obtain ⟨j, rfl⟩ := h
      have hj : N ≤ j := hσ.le_iff_le.mp hk
      simpa [w, Set.mem_range_self, Function.comp_apply] using hN j hj
    · rw [show w k = zhat from if_neg h]
      exact mem_of_mem_nhds hU
  have hlow : ψ zhat ≤ liminf (fun k => Ψ (σ k) (z (σ k))) atTop := by
    have h := hσat.liminf_le_liminf_comp (u := fun n => Ψ n (w n))
    have heq : (fun n => Ψ n (w n)) ∘ σ = fun k => Ψ (σ k) (z (σ k)) := by
      funext k
      change Ψ (σ k) (w (σ k)) = _
      rw [show w (σ k) = z (σ k) from if_pos (Set.mem_range_self k)]
    rw [heq] at h
    exact ((hepi zhat).1 w hw).trans h
  have hall (y : α) : ψ zhat ≤ ψ y := by
    obtain ⟨ys, _, hys⟩ := (hepi y).2
    let u (k : ℕ) : EReal := Ψ (σ k) (ys (σ k))
    let v (k : ℕ) : EReal := (ε (σ k) : EReal)
    have hv : Tendsto v atTop (𝓝 0) := by
      have h := (continuous_coe_real_ereal.continuousAt.tendsto.comp hε).comp hσat
      rw [show ((Real.toEReal ∘ ε) ∘ σ) = v from rfl, EReal.coe_zero] at h
      exact h
    have hshift : limsup v atTop = 0 := hv.limsup_eq
    have hsum := EReal.limsup_add_le (u := u) (v := v) (f := atTop)
      (Or.inr (by simp [hshift])) (Or.inr (by simp [hshift]))
    have hcmp : ∀ᶠ k in atTop, Ψ (σ k) (z (σ k)) ≤ (u + v) k :=
      Eventually.of_forall fun k =>
        (hz (σ k)).2.trans (add_le_add_left (iInf_le (Ψ (σ k)) (ys (σ k))) _)
    calc
      ψ zhat ≤ liminf (fun k => Ψ (σ k) (z (σ k))) atTop := hlow
      _ ≤ limsup (fun k => Ψ (σ k) (z (σ k))) atTop := liminf_le_limsup
      _ ≤ limsup (u + v) atTop := limsup_le_limsup hcmp
      _ ≤ limsup u atTop := by simpa only [hshift, add_zero] using hsum
      _ ≤ limsup (fun n => Ψ n (ys n)) atTop :=
        hσat.limsup_comp_le_limsup (u := fun n => Ψ n (ys n))
      _ ≤ ψ y := hys
  obtain ⟨y, hy⟩ := hdom
  refine ⟨?_, ?_⟩
  · change ψ y ≠ ⊤ at hy
    exact (lt_of_le_of_lt (hall y) (lt_top_iff_ne_top.mpr hy)).ne
  · change ψ zhat ≤ (⨅ y, ψ y) + ((0 : ℝ) : EReal)
    simpa only [EReal.coe_zero, add_zero] using le_iInf hall

#print axioms solution
