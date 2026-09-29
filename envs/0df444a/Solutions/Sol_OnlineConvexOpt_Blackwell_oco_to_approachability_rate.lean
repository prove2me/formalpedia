-- Prove2me | solution 1 for OnlineConvexOpt.Blackwell.oco_to_approachability_rate
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:43:21.330874+00:00
-- url     : https://prove2.me/submissions/8dcc6f41-eb11-4085-a34e-32e248f18c23

import Mathlib
import Definitions.Def_OnlineConvexOpt_Blackwell_SupportFunction

namespace OnlineConvexOpt.Blackwell

lemma aux_ocoar_supp_zero {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    SupportFunction ({0} : Set (EuclideanSpace ℝ (Fin d))) v = 0 := by
  unfold SupportFunction
  have h : ∀ x : EuclideanSpace ℝ (Fin d),
      (⨆ (_ : x ∈ ({0} : Set (EuclideanSpace ℝ (Fin d)))), inner ℝ v x) = 0 := by
    intro x
    by_cases hx : x ∈ ({0} : Set (EuclideanSpace ℝ (Fin d)))
    · have hx0 : x = 0 := hx
      subst hx0
      have : Nonempty ((0 : EuclideanSpace ℝ (Fin d)) ∈ ({0} : Set _)) := ⟨hx⟩
      simp
    · have : IsEmpty (x ∈ ({0} : Set (EuclideanSpace ℝ (Fin d)))) := ⟨hx⟩
      exact Real.iSup_of_isEmpty _
  simp only [h]
  exact ciSup_const

end OnlineConvexOpt.Blackwell

open OnlineConvexOpt.Blackwell

theorem solution : ¬ (∀ {d : ℕ} (K2 : Set (EuclideanSpace ℝ (Fin d))) (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSconv : Convex ℝ S) (hSbdd : Bornology.IsBounded S) (hSclosed : IsClosed S)
    (hSne : S.Nonempty)
    (u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hO : ∀ w : EuclideanSpace ℝ (Fin d), ‖w‖ ≤ 1 → ∀ y ∈ K2,
      inner ℝ w (u (O w) y) - SupportFunction S w ≤ 0)
    (A : (ℕ → EuclideanSpace ℝ (Fin d) → ℝ) → ℕ → EuclideanSpace ℝ (Fin d))
    (RegretBoundA : ℝ) (T : ℕ) (hT : 1 ≤ T)
    (y w x uvec : ℕ → EuclideanSpace ℝ (Fin d))
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hy : ∀ t : ℕ, 1 ≤ t → t ≤ T → y t ∈ K2)
    (hu0 : uvec 0 = 0)
    (hf : ∀ t : ℕ, 1 ≤ t → t ≤ T → f t = fun v => inner ℝ v (uvec (t - 1)) - SupportFunction S v)
    (hw : ∀ t : ℕ, 1 ≤ t → t ≤ T → w t = A f t)
    (hx : ∀ t : ℕ, 1 ≤ t → t ≤ T → x t = O (w t))
    (huvec : ∀ t : ℕ, 1 ≤ t → t ≤ T → uvec t = u (x t) (y t))
    (hAreg :
      (⨆ wstar ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
          ∑ t ∈ Finset.Icc 1 T, f t wstar) -
        ∑ t ∈ Finset.Icc 1 T, f t (w t) ≤ RegretBoundA),
    Metric.infDist ((T : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, uvec t) S ≤ RegretBoundA / T) := by
  intro H
  set e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single (0 : Fin 1) (1 : ℝ) with he_def
  have he : ‖e‖ = 1 := by rw [he_def, PiLp.norm_single]; norm_num
  let uv : ℕ → EuclideanSpace ℝ (Fin 1) := fun t => if t = 0 then 0 else -e
  let ff : ℕ → EuclideanSpace ℝ (Fin 1) → ℝ := fun t v =>
    inner ℝ v (uv (t - 1)) - SupportFunction ({0} : Set (EuclideanSpace ℝ (Fin 1))) v
  have hff : ∀ v, ff 1 v = 0 := by
    intro v
    simp [ff, uv, aux_ocoar_supp_zero]
  have hAreg : (⨆ wstar ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1,
          ∑ t ∈ Finset.Icc 1 1, ff t wstar) -
        ∑ t ∈ Finset.Icc 1 1, ff t ((fun _ => e) t) ≤ 0 := by
    simp only [Finset.Icc_self, Finset.sum_singleton, hff]
    have : (⨆ wstar ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, (0 : ℝ)) = 0 := by
      have h2 : ∀ wstar : EuclideanSpace ℝ (Fin 1),
          (⨆ (_ : wstar ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1), (0 : ℝ)) = 0 :=
        fun _ => Real.iSup_const_zero
      simp only [h2]
      exact Real.iSup_const_zero
    rw [this]; norm_num
  have key := @H 1 Set.univ {0} (convex_singleton 0) Bornology.isBounded_singleton
    isClosed_singleton (Set.singleton_nonempty 0) (fun x _ => x) (fun w => -w)
    (by
      intro w _ y _
      rw [aux_ocoar_supp_zero, inner_neg_right, real_inner_self_eq_norm_sq]
      nlinarith [sq_nonneg ‖w‖])
    (fun _ _ => e) 0 1 le_rfl (fun _ => 0) (fun _ => e) (fun _ => -e) uv ff
    (fun _ _ _ => Set.mem_univ _) (by simp [uv])
    (fun t _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (by
      intro t h1 h2
      have : t = 1 := le_antisymm h2 h1
      subst this
      simp [uv])
    hAreg
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, inv_one, one_smul,
    Metric.infDist_singleton, div_one] at key
  simp [uv, dist_zero_right, he] at key
  linarith
