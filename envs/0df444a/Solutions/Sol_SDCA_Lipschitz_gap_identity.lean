-- Prove2me | solution 1 for SDCA.Lipschitz.gap_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:47:50.200055+00:00
-- url     : https://prove2.me/submissions/d4951f9b-0346-4031-a237-5a02477391a9

import Mathlib
import Definitions.Def_SDCA_Lipschitz_Model

set_option autoImplicit false
open SDCA.Lipschitz

theorem esum_eq_bot_iff {ι : Type*} (s : Finset ι) (f : ι → EReal) :
    ∑ i ∈ s, f i = ⊥ ↔ ∃ i ∈ s, f i = ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, EReal.add_eq_bot_iff, ih]
    simp

theorem esum_eq_top {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → EReal)
    (h : ∀ i ∈ s, f i ≠ ⊥) (j : ι) (hj : j ∈ s) (hjt : f j = ⊤) : ∑ i ∈ s, f i = ⊤ := by
  rw [← Finset.add_sum_erase s f hj, hjt]
  have : ∑ i ∈ s.erase j, f i ≠ ⊥ := by
    rw [Ne, esum_eq_bot_iff]
    rintro ⟨i, hi, hfi⟩
    exact h i (Finset.mem_of_mem_erase hi) hfi
  exact EReal.top_add_of_ne_bot this

theorem coe_esum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) := by
  let g : ℝ →+ EReal := ⟨⟨(↑), EReal.coe_zero⟩, EReal.coe_add⟩
  exact map_sum g _ _

theorem conj_ne_bot (ψ : ℝ → ℝ) (u : ℝ) : conj ψ u ≠ ⊥ := by
  intro h
  have := le_iSup (fun z : ℝ => ((z * u - ψ z : ℝ) : EReal)) 0
  have h' : (⨆ z : ℝ, ((z * u - ψ z : ℝ) : EReal)) = ⊥ := h
  rw [h'] at this
  exact absurd (le_bot_iff.mp this) (EReal.coe_ne_bot _)

theorem solution {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (hn : 0 < n) (hlam : 0 < lam) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (α : Fin n → ℝ) :
    ((primal φ x lam (wOf x lam α) : ℝ) : EReal) - dual φ x lam α =
      (((1 / (n : ℝ)) : ℝ) : EReal) *
        ∑ i, (((φ i (inner ℝ (wOf x lam α) (x i)) + α i * inner ℝ (wOf x lam α) (x i) : ℝ) : EReal)
          + conj (φ i) (-α i)) := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hln : lam * n ≠ 0 := by positivity
  set v := wOf x lam α with hv
  by_cases htop : ∃ j, conj (φ j) (-α j) = ⊤
  · obtain ⟨j, hj⟩ := htop
    have hD : dual φ x lam α = ⊥ := by
      unfold dual
      rw [← hv]
      have : ∑ i, -conj (φ i) (-α i) = ⊥ := by
        rw [esum_eq_bot_iff]
        exact ⟨j, Finset.mem_univ _, by rw [hj]; rfl⟩
      rw [this, EReal.coe_mul_bot_of_pos (by positivity), EReal.bot_sub]
    have hR : ∑ i, (((φ i (inner ℝ v (x i)) + α i * inner ℝ v (x i) : ℝ) : EReal)
          + conj (φ i) (-α i)) = ⊤ := by
      refine esum_eq_top _ _ ?_ j (Finset.mem_univ _) ?_
      · intro i _
        rw [Ne, EReal.add_eq_bot_iff]
        push Not
        exact ⟨EReal.coe_ne_bot _, conj_ne_bot _ _⟩
      · rw [hj, EReal.coe_add_top]
    rw [hD, hR, EReal.coe_sub_bot, EReal.coe_mul_top_of_pos (by positivity)]
  · push Not at htop
    have hreal : ∀ i, ∃ c : ℝ, conj (φ i) (-α i) = (c : EReal) := by
      intro i
      lift conj (φ i) (-α i) to ℝ using ⟨htop i, conj_ne_bot _ _⟩ with c hc
      exact ⟨c, rfl⟩
    choose c hc using hreal
    have hinner : ∑ i, α i * inner ℝ v (x i) = lam * n * ‖v‖ ^ 2 := by
      have h1 : (lam * n) • v = ∑ i, α i • x i := by
        rw [hv]; unfold wOf
        rw [smul_smul, mul_one_div_cancel hln, one_smul]
      have := congrArg (fun y => inner ℝ v y) h1
      simp only [inner_smul_right, inner_sum] at this
      rw [← this, real_inner_self_eq_norm_sq]
    have hL : dual φ x lam α =
        ((1 / (n : ℝ) * ∑ i, (-c i) - lam / 2 * ‖v‖ ^ 2 : ℝ) : EReal) := by
      unfold dual
      rw [← hv]
      simp only [hc]
      simp only [EReal.coe_sub, EReal.coe_mul, coe_esum, EReal.coe_neg]
    have hR : ∑ i, (((φ i (inner ℝ v (x i)) + α i * inner ℝ v (x i) : ℝ) : EReal)
          + conj (φ i) (-α i)) =
        ((∑ i, (φ i (inner ℝ v (x i)) + α i * inner ℝ v (x i) + c i) : ℝ) : EReal) := by
      rw [coe_esum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hc i]; simp only [EReal.coe_add]
    rw [hL, hR, ← EReal.coe_mul, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
    unfold primal
    have hs : ∑ i, (φ i (inner ℝ v (x i)) + α i * inner ℝ v (x i) + c i) =
        ∑ i, φ i (inner ℝ v (x i)) + lam * n * ‖v‖ ^ 2 + ∑ i, c i := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hinner]
    rw [hs, Finset.sum_neg_distrib]
    field_simp
    ring
