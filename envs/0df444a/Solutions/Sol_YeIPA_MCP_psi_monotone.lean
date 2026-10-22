-- Prove2me | solution 1 for YeIPA.MCP.psi_monotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:26:48.458234+00:00
-- url     : https://prove2.me/submissions/872efdf4-f428-4444-81fc-7e7ce112d0de

import Mathlib
import Definitions.Def_YeIPA_MCP_HomogeneousModel

open Matrix
open YeIPA.MCP

theorem g69c_dot_psi {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (w z : Fin (n + 1) → ℝ) :
    w ⬝ᵥ psi f z = (z (Fin.last n) • Fin.init w - w (Fin.last n) • Fin.init z) ⬝ᵥ
      f (fun j => Fin.init z j / z (Fin.last n)) := by
  unfold psi
  generalize f (fun j => Fin.init z j / z (Fin.last n)) = F
  simp only [dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Fin.init, sub_mul, Finset.sum_sub_distrib]
  rw [mul_neg, Finset.mul_sum]
  have : ∀ x : Fin n, w x.castSucc * (z (Fin.last n) * F x) = z (Fin.last n) * w x.castSucc * F x :=
    fun x => by ring
  simp only [this]
  have : ∀ x : Fin n, w (Fin.last n) * (z x.castSucc * F x) = w (Fin.last n) * z x.castSucc * F x :=
    fun x => by ring
  simp only [this]
  ring

theorem g69c_self_dot_psi {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (z : Fin (n + 1) → ℝ) :
    z ⬝ᵥ psi f z = 0 := by
  rw [g69c_dot_psi, sub_self, zero_dotProduct]

theorem g69c_init_pos {n : ℕ} (z : Fin (n + 1) → ℝ) (hz : z ∈ posOrthant (n + 1)) :
    (fun j => Fin.init z j / z (Fin.last n)) ∈ posOrthant n :=
  fun j => div_pos (hz _) (hz _)

theorem g69c_psi_cont {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_cont : ContinuousOn f (posOrthant n)) :
    ContinuousOn (psi f) (posOrthant (n + 1)) := by
  have hu : ContinuousOn (fun z : Fin (n + 1) → ℝ => fun j => Fin.init z j / z (Fin.last n))
      (posOrthant (n + 1)) := by
    apply continuousOn_pi.mpr
    intro j
    exact ((continuous_apply _).continuousOn).div (continuous_apply _).continuousOn
      (fun z hz => (hz _).ne')
  have hfu : ContinuousOn (fun z : Fin (n + 1) → ℝ => f (fun j => Fin.init z j / z (Fin.last n)))
      (posOrthant (n + 1)) :=
    hf_cont.comp hu (fun z hz => g69c_init_pos z hz)
  apply continuousOn_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [psi, Fin.snoc_last]
    simp only [dotProduct]
    apply ContinuousOn.neg
    apply continuousOn_finsetSum
    intro k _
    exact ((continuous_apply _).continuousOn).mul
      ((continuous_apply k).comp_continuousOn hfu)
  · simp only [psi, Fin.snoc_castSucc]
    exact ((continuous_apply _).continuousOn).mul ((continuous_apply k).comp_continuousOn hfu)

theorem g69c_psi_mono {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (hf_mono : MonotoneOnPos f) :
    MonotoneOnPos (psi f) := by
  intro z1 hz1 z2 hz2
  have e : (z1 - z2) ⬝ᵥ (psi f z1 - psi f z2) = -(z1 ⬝ᵥ psi f z2) - z2 ⬝ᵥ psi f z1 := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, g69c_self_dot_psi, g69c_self_dot_psi]
    ring
  rw [e, g69c_dot_psi, g69c_dot_psi]
  set t1 := z1 (Fin.last n)
  set t2 := z2 (Fin.last n)
  have ht1 : 0 < t1 := hz1 _
  have ht2 : 0 < t2 := hz2 _
  set u1 : Fin n → ℝ := fun j => Fin.init z1 j / t1 with hu1
  set u2 : Fin n → ℝ := fun j => Fin.init z2 j / t2 with hu2
  have k1 : t2 • Fin.init z1 - z1 (Fin.last n) • Fin.init z2 = (t1 * t2) • (u1 - u2) := by
    funext j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hu1, hu2]
    field_simp
    ring
  have k2 : t1 • Fin.init z2 - z2 (Fin.last n) • Fin.init z1 = -((t1 * t2) • (u1 - u2)) := by
    funext j
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hu1, hu2]
    field_simp
    ring
  rw [k1, k2, neg_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have hm := hf_mono u1 (g69c_init_pos z1 hz1) u2 (g69c_init_pos z2 hz2)
  rw [dotProduct_sub] at hm
  have hp : 0 < t1 * t2 := mul_pos ht1 ht2
  nlinarith

theorem solution {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_cont : ContinuousOn f (posOrthant n)) (hf_mono : MonotoneOnPos f) :
    ContinuousOn (psi f) (posOrthant (n + 1)) ∧ MonotoneOnPos (psi f) :=
  ⟨g69c_psi_cont f hf_cont, g69c_psi_mono f hf_mono⟩
