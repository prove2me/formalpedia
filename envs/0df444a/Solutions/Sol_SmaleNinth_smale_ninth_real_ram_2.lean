-- Prove2me | solution 2 for SmaleNinth.smale_ninth_real_ram
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T02:49:22.305392+00:00
-- url     : https://prove2.me/submissions/44c43182-8d56-4eb0-a843-10fc5830e5b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_SmaleNinth_oai_feasibility_real
import Theorems.Thm_SmaleNinth_real_ram_of_oai_program

open Matrix LinearOptimization OAI.Optimization.LinearProgramming

/-- The easy direction of Farkas' lemma: a certificate excludes every feasible point. -/
theorem SmaleNinth.oai_certificate_infeasible {m d : ℕ} {A : Matrix (Fin m) (Fin d) ℝ}
    {b y : Fin m → ℝ} (hy : Certificate A b y) {x : Fin d → ℝ} (hx : Feasible A b x) : False := by
  obtain ⟨hy0, hAy, hby, -⟩ := hy
  have h1 : y ⬝ᵥ (A *ᵥ x) ≤ y ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hx hy0
  have h2 : y ⬝ᵥ (A *ᵥ x) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hAy, zero_dotProduct]
  rw [dotProduct_comm] at hby
  linarith

theorem solution :
    ∃ (R : SmaleNinth.RAMProgram) (C d : ℕ),
      ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          SmaleNinth.RAMDecidesInTime R (SmaleNinth.encodeLP A b) (C * (m * n + m + 2) ^ d) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) := by
  obtain ⟨p, c, e, hp⟩ := SmaleNinth.oai_feasibility_real
  obtain ⟨R, C, d, hR⟩ := SmaleNinth.real_ram_of_oai_program p c e
  refine ⟨R, C, d, fun m n A b => hR m n A b fun hm hn => ?_⟩
  obtain ⟨k, t, htr, hk, hout⟩ := hp m n hm hn (-A) (-b)
  refine ⟨k, t, htr, hk, ?_⟩
  rcases hout with ⟨h0, hx⟩ | ⟨h1, hy⟩
  · exact ⟨0, h0, iff_of_true rfl ⟨_, hx⟩⟩
  · refine ⟨1, h1, iff_of_false (by decide) ?_⟩
    rintro ⟨x, hx⟩
    exact SmaleNinth.oai_certificate_infeasible hy hx
