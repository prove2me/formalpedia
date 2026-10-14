-- Prove2me | solution 1 for TwoEchelonCVRP.LowerBound.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:52:40.707962+00:00
-- url     : https://prove2.me/submissions/cd1f0bdf-3531-4fbc-a8c0-1f755afb7118

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LowerBound_Model
import Definitions.Def_TwoEchelonCVRP_LowerBound_RF
import Definitions.Def_TwoEchelonCVRP_LowerBound_ExtRoutes
open TwoEchelonCVRP.LowerBound
/-- Theorem 4 (p. 302): for any enlarged family `𝓡̂_k ⊇ 𝓡_k` of not necessarily elementary routes,
the marginal costs `β_{ik}` of (24) solve the penalty system (12). -/
theorem solution (I : Instance) (RS : RouteSystem I) (E : ExtRoutes RS)
    (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ) :
    SatisfiesPenalty RS (E.beta24 lam μ μ0) lam μ μ0 := by 
  classical
  intro l
  have hea (i : Fin I.nc) : E.a i (E.emb l) = RS.a i l := by
    simp [ExtRoutes.a, E.emb_tour, RouteSystem.a]
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ (RS.tour2_ne l)
  have hd : 0 < ∑ i, (RS.a i l : ℝ)*(I.q i : ℝ) := by
    apply Finset.sum_pos' (fun i hi => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    refine ⟨j, Finset.mem_univ j, mul_pos ?_ ?_⟩
    · exact_mod_cast List.count_pos_iff.mpr hj
    · exact_mod_cast I.q_pos j
  have hi (i : Fin I.nc) : (RS.a i l : ℝ)*E.beta24 lam μ μ0 i (RS.sat l) ≤
      (RS.a i l : ℝ)*(I.q i : ℝ)*E.ratio lam μ μ0 (E.emb l) := by
    by_cases hm : i ∈ RS.tour2 l
    · have he : E.emb l ∈ E.Rhat i (RS.sat l) := by simp [ExtRoutes.Rhat, E.emb_sat, E.emb_tour, hm]
      have hn : (E.Rhat i (RS.sat l)).Nonempty := ⟨E.emb l, he⟩
      have hmin := Finset.inf'_le (E.ratio lam μ μ0) he
      have hb : E.beta24 lam μ μ0 i (RS.sat l) ≤ (I.q i : ℝ)*E.ratio lam μ μ0 (E.emb l) := by
        dsimp [ExtRoutes.beta24]
        rw [dif_pos hn]
        exact mul_le_mul_of_nonneg_left hmin (Nat.cast_nonneg _)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (RS.a i l))
    · simp [RouteSystem.a, List.count_eq_zero_of_not_mem hm]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  rw [← Finset.sum_mul] at hs
  have heq : (∑ i, (RS.a i l : ℝ)*(I.q i : ℝ))*E.ratio lam μ μ0 (E.emb l) =
      RS.c l - ∑ i, (RS.a i l : ℝ)*lam i - μ (RS.sat l) - μ0 := by
    simp only [ExtRoutes.ratio, E.emb_cost, E.emb_sat, hea]
    field_simp
  rw [heq] at hs
  exact hs


