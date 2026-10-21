-- Prove2me | solution 1 for WassTwoStage.Copositive.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:29:38.628906+00:00
-- url     : https://prove2.me/submissions/9ef7ab9e-a618-479f-9cc4-74b77cfa9108

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems

set_option autoImplicit false
open Matrix Filter Topology

theorem solution {k : ℕ} (Mt : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (hM : Mt.IsSymm) :
    MurtyKabadi.Reduction.Copositive Mt ↔
      ∀ z : Fin k → ℝ, 0 ≤ z →
        0 ≤ Sum.elim z (fun _ => (1 : ℝ)) ⬝ᵥ (Mt *ᵥ Sum.elim z (fun _ => (1 : ℝ))) := by
  constructor
  · intro h z hz
    apply h
    intro i
    rcases i with i | i
    · simpa using hz i
    · simp
  · intro h x hx
    unfold MurtyKabadi.Reduction.Q
    -- decompose x = Sum.elim z (fun _ => t)
    set z : Fin k → ℝ := fun i => x (Sum.inl i) with hzdef
    set t : ℝ := x (Sum.inr ()) with htdef
    have hz : 0 ≤ z := fun i => hx _
    have ht : 0 ≤ t := hx _
    have hxe : x = Sum.elim z (fun _ => t) := by
      ext i; rcases i with i | ⟨⟩ <;> simp [hzdef, htdef]
    -- the quadratic form is a polynomial; key scaling identity
    have key : ∀ (s : ℝ), 0 < s →
        0 ≤ Sum.elim z (fun _ => s) ⬝ᵥ (Mt *ᵥ Sum.elim z (fun _ => s)) := by
      intro s hs
      have h1 := h (s⁻¹ • z) (smul_nonneg (inv_nonneg.2 hs.le) hz)
      have e : (Sum.elim z (fun _ : Unit => s) : Fin k ⊕ Unit → ℝ) = s • (Sum.elim (s⁻¹ • z) (fun _ : Unit => (1 : ℝ)) : Fin k ⊕ Unit → ℝ) := by
        ext i; rcases i with i | ⟨⟩
        · simp [hs.ne']
        · simp
      rw [e, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
      have : 0 ≤ s * s := by positivity
      nlinarith [mul_nonneg this h1]
    rw [hxe]
    rcases ht.eq_or_lt with h0 | hpos
    · rw [← h0]
      -- limit as s → 0+
      have hc : Continuous (fun s : ℝ => Sum.elim z (fun _ => s) ⬝ᵥ (Mt *ᵥ Sum.elim z (fun _ => s))) := by
        unfold dotProduct Matrix.mulVec
        apply continuous_finset_sum
        intro i _
        apply Continuous.mul
        · rcases i with i | ⟨⟩ <;> simp <;> fun_prop
        · apply continuous_finset_sum
          intro j _
          apply Continuous.mul continuous_const
          rcases j with j | ⟨⟩ <;> simp <;> fun_prop
      have hlim := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      refine ge_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin] with s hs using key s hs
    · exact key t hpos
