-- Prove2me | solution 1 for RockafellianRelax.tilt_epiConverges
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-07T13:44:46.098528+00:00
-- url     : https://prove2.me/submissions/7db33801-3b4b-4f37-a8be-6222645b54f0

import Definitions.Def_RockafellianRelax_tilt
import Definitions.Def_PerspEpi_SeqEpiConv
import Mathlib.Topology.Algebra.Ring.Basic

open Filter Topology RockafellianRelax

theorem solution {m n : ℕ} (F : ℕ → (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal) (ybar : Fin m → ℝ) (y : ℕ → Fin m → ℝ)
    (hy : Tendsto y atTop (𝓝 ybar)) (hF : PerspEpi.SeqEpiConv F f) :
    PerspEpi.SeqEpiConv (fun ν => tilt (F ν) (y ν)) (tilt f ybar) := by
  have shift_tendsto (x : (Fin m → ℝ) × (Fin n → ℝ))
      (xs : ℕ → (Fin m → ℝ) × (Fin n → ℝ)) (hxs : Tendsto xs atTop (𝓝 x)) :
      Tendsto (fun ν => -((y ν ⬝ᵥ (xs ν).1 : ℝ) : EReal)) atTop
        (𝓝 (-((ybar ⬝ᵥ x.1 : ℝ) : EReal))) := by
    have hxs₁ : Tendsto (fun ν => (xs ν).1) atTop (𝓝 x.1) := continuous_fst.continuousAt.tendsto.comp hxs
    have hd : Tendsto (fun ν => y ν ⬝ᵥ (xs ν).1) atTop (𝓝 (ybar ⬝ᵥ x.1)) := by
      unfold dotProduct
      exact tendsto_finsetSum _ fun i _ =>
        ((tendsto_pi_nhds.mp hy) i).mul ((tendsto_pi_nhds.mp hxs₁) i)
    exact (continuous_coe_real_ereal.continuousAt.tendsto.comp hd).neg
  intro x
  constructor
  · intro xs hxs
    have hs := shift_tendsto x xs hxs
    have hlow := (hF x).1 xs hxs
    have hsum := EReal.le_liminf_add (u := fun ν => F ν (xs ν))
      (v := fun ν => -((y ν ⬝ᵥ (xs ν).1 : ℝ) : EReal)) (f := atTop)
    rw [hs.liminf_eq] at hsum
    exact (add_le_add_left hlow _).trans hsum
  · obtain ⟨xs, hxs, hupper⟩ := (hF x).2
    refine ⟨xs, hxs, ?_⟩
    have hs := shift_tendsto x xs hxs
    have hsum := EReal.limsup_add_le (u := fun ν => F ν (xs ν))
      (v := fun ν => -((y ν ⬝ᵥ (xs ν).1 : ℝ) : EReal)) (f := atTop)
      (Or.inr (by rw [hs.limsup_eq]; simp)) (Or.inr (by rw [hs.limsup_eq]; simp))
    rw [hs.limsup_eq] at hsum
    exact hsum.trans (add_le_add_left hupper _)

#print axioms solution

