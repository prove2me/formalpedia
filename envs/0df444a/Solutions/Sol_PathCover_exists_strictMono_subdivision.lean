-- Prove2me | solution 1 for PathCover.exists_strictMono_subdivision
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-10T09:46:47.296803+00:00
-- url     : https://prove2.me/submissions/86f45877-2433-435b-8a38-d197173a8e6b

import Mathlib.Topology.Path
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

open scoped unitInterval
open Set

theorem solution {X : Type*} [TopologicalSpace X] {ι : Type*} {a b : X}
    (A : ι → Set X) (hopen : ∀ i, IsOpen (A i)) (hcover : (⋃ i, A i) = Set.univ)
    (f : Path a b) :
    ∃ (n : ℕ) (t : Fin (n + 1) → I) (lab : Fin n → ι),
      0 < n ∧ StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      ∀ (k : Fin n) (s : I), s ∈ Set.Icc (t k.castSucc) (t k.succ) →
        f s ∈ A (lab k) := by
  -- Pull the cover back along `f`.
  have hc₁ : ∀ i, IsOpen (f ⁻¹' A i) := fun i => (hopen i).preimage f.continuous
  have hc₂ : (univ : Set I) ⊆ ⋃ i, f ⁻¹' A i := by
    intro s _
    have hs : f s ∈ ⋃ i, A i := by rw [hcover]; trivial
    simpa using hs
  -- Lebesgue number for the pulled-back cover of the (compact) unit interval.
  obtain ⟨δ, δpos, hδ⟩ := lebesgue_number_lemma_of_metric (isCompact_univ (X := I)) hc₁ hc₂
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt δpos
  set n : ℕ := N + 1 with hn
  have hnpos : 0 < n := Nat.succ_pos N
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hNn : (1 : ℝ) / (n : ℝ) < δ := by
    have : ((n : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast [hn]; ring
    rw [this]; exact hN
  -- The uniform partition `k / n`.
  have hmem : ∀ k : Fin (n + 1), ((k : ℕ) : ℝ) / (n : ℝ) ∈ I := by
    intro k
    refine Set.mem_Icc.mpr ⟨by positivity, ?_⟩
    rw [div_le_one hn0]
    exact_mod_cast Nat.lt_succ_iff.mp k.isLt
  set t : Fin (n + 1) → I := fun k => ⟨((k : ℕ) : ℝ) / (n : ℝ), hmem k⟩ with ht
  have htcoe : ∀ k : Fin (n + 1), ((t k : ℝ)) = ((k : ℕ) : ℝ) / (n : ℝ) := fun k => rfl
  -- Strict monotonicity is immediate for the uniform partition.
  have hsm : StrictMono t := by
    intro k l hkl
    rw [← Subtype.coe_lt_coe, htcoe, htcoe]
    refine div_lt_div_of_pos_right ?_ hn0
    exact_mod_cast hkl
  -- Each block has diameter `1 / n < δ`, so it sits inside a ball, hence inside a cover member.
  have key : ∀ k : Fin n, ∃ i, ∀ s : I, s ∈ Set.Icc (t k.castSucc) (t k.succ) → f s ∈ A i := by
    intro k
    obtain ⟨i, hi⟩ := hδ (t k.castSucc) (mem_univ _)
    refine ⟨i, fun s hs => hi ?_⟩
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    have h1 : ((t k.castSucc : I) : ℝ) ≤ (s : ℝ) := hs.1
    have h2 : ((s : I) : ℝ) ≤ ((t k.succ : I) : ℝ) := hs.2
    have e1 : ((t k.castSucc : I) : ℝ) = ((k : ℕ) : ℝ) / (n : ℝ) := by
      rw [htcoe]; simp
    have e2 : ((t k.succ : I) : ℝ) = (((k : ℕ) : ℝ) + 1) / (n : ℝ) := by
      rw [htcoe, Fin.val_succ]; push_cast; ring_nf
    rw [abs_sub_lt_iff]
    constructor
    · calc (s : ℝ) - ((t k.castSucc : I) : ℝ)
          ≤ ((t k.succ : I) : ℝ) - ((t k.castSucc : I) : ℝ) := by linarith
        _ = 1 / (n : ℝ) := by rw [e1, e2]; field_simp; ring
        _ < δ := hNn
    · have : ((t k.castSucc : I) : ℝ) - (s : ℝ) ≤ 0 := by linarith
      linarith
  choose lab hlab using key
  exact ⟨n, t, lab, hnpos, hsm, by
      apply Subtype.ext; rw [htcoe]; simp,
    by apply Subtype.ext; rw [htcoe]; simp [Fin.val_last, hn0.ne'], hlab⟩
