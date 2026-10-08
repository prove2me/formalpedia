-- Prove2me | solution 1 for TeschlODE.Shared.flow_periodic_orbit_global_everywhere
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T09:33:20.276041+00:00
-- url     : https://prove2.me/submissions/0935587c-3099-4783-8129-215e88a5d000

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

namespace CexEF75

open TeschlODE.Shared Set

def M : Set (Fin 1 → ℝ) := {x | x 0 < 0} ∪ {x | 0 < x 0 ∧ x 0 < 1}

noncomputable def f : (Fin 1 → ℝ) → (Fin 1 → ℝ) := fun x => fun _ => if 0 < x 0 then 1 else 0

noncomputable def I : (Fin 1 → ℝ) → Set ℝ := fun x => if 0 < x 0 then Ioo (-x 0) (1 - x 0) else univ

noncomputable def Φ : ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) := fun t x => if 0 < x 0 then (fun i => x i + t) else x

theorem M_open : IsOpen M := by
  apply IsOpen.union
  · exact isOpen_lt (continuous_apply 0) continuous_const
  · exact (isOpen_lt continuous_const (continuous_apply 0)).inter
      (isOpen_lt (continuous_apply 0) continuous_const)

theorem mem_M_ne {x : Fin 1 → ℝ} (hx : x ∈ M) : x 0 ≠ 0 := by
  rcases hx with h | h
  · exact ne_of_lt h
  · exact ne_of_gt h.1

/-- sign preservation along an integral curve -/
theorem sign_pos {J : Set ℝ} {ψ : ℝ → (Fin 1 → ℝ)} (hψ : IsIntegralCurve f M J ψ)
    (h0 : (0 : ℝ) ∈ J) (hpos : 0 < ψ 0 0) : ∀ t ∈ J, 0 < ψ t 0 := by
  obtain ⟨_, hJc, hM, hd⟩ := hψ
  intro t ht
  by_contra hneg
  rw [not_lt] at hneg
  have hcont : ContinuousOn (fun s => ψ s 0) J := fun s hs =>
    ((continuous_apply 0).continuousAt.comp (hd s hs).continuousAt).continuousWithinAt
  have := hJc.isPreconnected.intermediate_value ht h0 hcont ⟨hneg, hpos.le⟩
  obtain ⟨s, hs, hs0⟩ := this
  exact mem_M_ne (hM s hs) hs0

theorem sign_neg {J : Set ℝ} {ψ : ℝ → (Fin 1 → ℝ)} (hψ : IsIntegralCurve f M J ψ)
    (h0 : (0 : ℝ) ∈ J) (hneg : ψ 0 0 < 0) : ∀ t ∈ J, ψ t 0 < 0 := by
  obtain ⟨_, hJc, hM, hd⟩ := hψ
  intro t ht
  by_contra hpos
  rw [not_lt] at hpos
  have hcont : ContinuousOn (fun s => ψ s 0) J := fun s hs =>
    ((continuous_apply 0).continuousAt.comp (hd s hs).continuousAt).continuousWithinAt
  have := hJc.isPreconnected.intermediate_value h0 ht hcont ⟨hneg.le, hpos⟩
  obtain ⟨s, hs, hs0⟩ := this
  exact mem_M_ne (hM s hs) hs0

theorem maxflow : IsMaximalFlow f M I Φ := by
  intro x hx
  rcases lt_or_gt_of_ne (mem_M_ne hx) with hneg | hpos
  · -- negative branch: constant curve
    have hnp : ¬ (0 < x 0) := not_lt.mpr hneg.le
    have hfx : f x = 0 := by funext i; simp [f, hnp]
    have hI : I x = univ := by simp [I, hnp]
    have hΦ : ∀ t, Φ t x = x := fun t => by simp [Φ, hnp]
    refine ⟨⟨by rw [hI]; exact isOpen_univ, by rw [hI]; exact ordConnected_univ,
      fun t _ => by show Φ t x ∈ M; rw [hΦ]; exact hx, fun t _ => ?_⟩, by rw [hI]; trivial, hΦ 0, ?_⟩
    · simp only [hΦ, hfx]; exact hasDerivAt_const t x
    · intro J ψ hψ hJ0 hψ0
      refine ⟨by rw [hI]; exact subset_univ _, fun t ht => ?_⟩
      have hs := sign_neg hψ hJ0 (by rw [hψ0]; exact hneg)
      obtain ⟨hJo, hJc, _, hd⟩ := hψ
      have heq := hJo.eqOn_of_deriv_eq (f := ψ) (g := fun _ => x) hJc.isPreconnected
        (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
        (fun s _ => (differentiableAt_const x).differentiableWithinAt)
        (fun s hs' => by
          have h1 : f (ψ s) = 0 := by funext i; simp [f, not_lt.mpr (hs s hs').le]
          rw [(hd s hs').deriv, h1, deriv_const])
        hJ0 hψ0 ht
      rw [heq, hΦ]
  · -- positive branch: translation
    have hx1 : x 0 < 1 := by
      rcases hx with h | h
      · exact absurd h (not_lt.mpr hpos.le)
      · exact h.2
    have hI : I x = Ioo (-x 0) (1 - x 0) := by simp [I, hpos]
    have hΦ : ∀ t, Φ t x = fun i => x i + t := fun t => by simp [Φ, hpos]
    have hder : ∀ t, HasDerivAt (fun t => fun i => x i + t) (fun _ : Fin 1 => (1:ℝ)) t :=
      fun t => hasDerivAt_pi.2 (fun i => (hasDerivAt_id t).const_add (x i))
    refine ⟨⟨by rw [hI]; exact isOpen_Ioo, by rw [hI]; exact ordConnected_Ioo,
      fun t ht => ?_, fun t ht => ?_⟩, ?_, ?_, ?_⟩
    · rw [hI] at ht
      show Φ t x ∈ M
      rw [hΦ]
      right
      exact ⟨by simp; linarith [ht.1], by simp; linarith [ht.2]⟩
    · rw [hI] at ht
      have hp : 0 < (Φ t x) 0 := by rw [hΦ]; simp; linarith [ht.1]
      have h1 : f (Φ t x) = fun _ => 1 := by funext i; simp [f, hp]
      rw [h1]
      simp only [hΦ]
      exact hder t
    · rw [hI]; exact ⟨by linarith, by linarith⟩
    · funext i; simp [hΦ]
    · intro J ψ hψ hJ0 hψ0
      have hs := sign_pos hψ hJ0 (by rw [hψ0]; exact hpos)
      have hψM := hψ.2.2.1
      obtain ⟨hJo, hJc, _, hd⟩ := hψ
      have heq := hJo.eqOn_of_deriv_eq (f := ψ) (g := fun t => fun i => x i + t)
        hJc.isPreconnected
        (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
        (fun s _ => (hder s).differentiableAt.differentiableWithinAt)
        (fun s hs' => by
          have h1 : f (ψ s) = fun _ => 1 := by funext i; simp [f, hs s hs']
          rw [(hd s hs').deriv, h1, (hder s).deriv])
        hJ0 (by rw [hψ0]; funext i; simp)
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · rw [hI]
        have h1 := hs t ht
        have h2 : ψ t 0 < 1 := by
          rcases hψM t ht with h | h
          · exact absurd h (not_lt.mpr h1.le)
          · exact h.2
        rw [heq ht] at h1 h2
        simp at h1 h2
        exact ⟨by linarith, by linarith⟩
      · rw [heq ht, hΦ]

end CexEF75

open TeschlODE.Shared in
theorem solution : ¬ (∀ {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M)
    (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (hΦ : IsMaximalFlow f M I Φ) (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ M) (T : ℝ)
    (hT0 : 0 < T) (hTI : T ∈ I x₀) (hper : Φ T x₀ = x₀),
    ∀ z ∈ M, I z = Set.univ) := by
  intro h
  have hx₀ : (fun _ : Fin 1 => (-1 : ℝ)) ∈ CexEF75.M := Or.inl (by norm_num)
  have hTI : (1 : ℝ) ∈ CexEF75.I (fun _ : Fin 1 => (-1 : ℝ)) := by
    simp [CexEF75.I]
  have hper : CexEF75.Φ 1 (fun _ : Fin 1 => (-1 : ℝ)) = fun _ => -1 := by
    simp [CexEF75.Φ]
  have hz : (fun _ : Fin 1 => (1/2 : ℝ)) ∈ CexEF75.M := Or.inr ⟨by norm_num, by norm_num⟩
  have key := h CexEF75.f CexEF75.M CexEF75.M_open CexEF75.I CexEF75.Φ CexEF75.maxflow
    _ hx₀ 1 one_pos hTI hper _ hz
  have h1 : (1 : ℝ) ∈ CexEF75.I (fun _ : Fin 1 => (1/2 : ℝ)) := by rw [key]; trivial
  simp [CexEF75.I] at h1
  norm_num at h1
