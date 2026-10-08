-- Prove2me | solution 1 for OnlineConvexOpt.Blackwell.oco_to_approachability_rate_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:05:35.740306+00:00
-- url     : https://prove2.me/submissions/a10859d6-acf5-43ed-a633-5e0ad95224cb

import Mathlib
import Definitions.Def_OnlineConvexOpt_Blackwell_SupportFunction_v2



namespace OnlineConvexOpt.Blackwell

theorem ocorate_core
    {d : ℕ} (K2 : Set (EuclideanSpace ℝ (Fin d))) (S : Set (EuclideanSpace ℝ (Fin d)))
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
    (hf : ∀ t : ℕ, 1 ≤ t → t ≤ T → f t = fun v => inner ℝ v (uvec t) - SupportFunction S v)
    (hw : ∀ t : ℕ, 1 ≤ t → t ≤ T → w t = A f t)
    (hwB : ∀ t : ℕ, 1 ≤ t → t ≤ T → ‖w t‖ ≤ 1)
    (hx : ∀ t : ℕ, 1 ≤ t → t ≤ T → x t = O (w t))
    (huvec : ∀ t : ℕ, 1 ≤ t → t ≤ T → uvec t = u (x t) (y t))
    (hAreg :
      sSup ((fun wstar => ∑ t ∈ Finset.Icc 1 T, f t wstar) ''
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) -
        ∑ t ∈ Finset.Icc 1 T, f t (w t) ≤ RegretBoundA) :
    Metric.infDist ((T : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, uvec t) S ≤ RegretBoundA / T := by
  have hTpos : (0:ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  set U := ∑ t ∈ Finset.Icc 1 T, uvec t with hU
  set z := (T : ℝ)⁻¹ • U with hz
  have hUz : U = (T:ℝ) • z := by rw [hz, smul_smul, mul_inv_cancel₀ hTpos.ne', one_smul]
  obtain ⟨p, hpS, hp⟩ := exists_norm_eq_iInf_of_complete_convex hSne hSclosed.isComplete hSconv z
  have hproj := (norm_eq_iInf_iff_real_inner_le_zero hSconv hpS).1 hp
  set c := ‖z - p‖⁻¹ with hc
  set wst := c • (z - p) with hwst
  have hc0 : 0 ≤ c := inv_nonneg.2 (norm_nonneg _)
  have hcn : c * ‖z - p‖ ^ 2 = ‖z - p‖ := by
    rcases eq_or_ne ‖z - p‖ 0 with h | h
    · rw [h]; simp
    · rw [hc]; field_simp
  have hwstn : ‖wst‖ ≤ 1 := by
    rw [hwst, norm_smul, Real.norm_of_nonneg hc0, hc]
    rcases eq_or_ne ‖z - p‖ 0 with h | h
    · rw [h]; simp
    · rw [inv_mul_cancel₀ h]
  -- support function bound
  obtain ⟨M, hM⟩ := hSbdd.exists_norm_le
  have hbdd : ∀ v : EuclideanSpace ℝ (Fin d), BddAbove ((fun s => (inner ℝ v s : ℝ)) '' S) := by
    intro v
    refine ⟨‖v‖ * M, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    calc (inner ℝ v s : ℝ) ≤ ‖v‖ * ‖s‖ := real_inner_le_norm _ _
      _ ≤ ‖v‖ * M := mul_le_mul_of_nonneg_left (hM s hs) (norm_nonneg _)
  have hsupp_ge : ∀ v s, s ∈ S → (inner ℝ v s : ℝ) ≤ SupportFunction S v := by
    intro v s hs
    exact le_csSup (hbdd v) ⟨s, hs, rfl⟩
  have hsupp : SupportFunction S wst ≤ inner ℝ wst p := by
    apply csSup_le (hSne.image _)
    rintro _ ⟨s, hs, rfl⟩
    have := hproj s hs
    simp only [hwst, inner_smul_left, RCLike.conj_to_real]
    rw [inner_sub_right] at this
    nlinarith
  -- sum of f at wst
  have hsumf : ∀ v, ∑ t ∈ Finset.Icc 1 T, f t v = inner ℝ v U - T * SupportFunction S v := by
    intro v
    rw [Finset.sum_congr rfl (fun t ht => by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 ht
      rw [hf t h1 h2])]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul, hU, inner_sum]
  have hkey : (T:ℝ) * ‖z - p‖ ≤ ∑ t ∈ Finset.Icc 1 T, f t wst := by
    rw [hsumf, hUz, inner_smul_right]
    have : (inner ℝ wst z : ℝ) - inner ℝ wst p = ‖z - p‖ := by
      rw [← inner_sub_right, hwst, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq,
        hcn]
    nlinarith
  -- bdd above of image
  obtain ⟨s0, hs0⟩ := hSne
  have hBdd : BddAbove ((fun wstar => ∑ t ∈ Finset.Icc 1 T, f t wstar) ''
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    refine ⟨‖U‖ + T * ‖s0‖, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_closedBall_zero_iff] at hv
    show ∑ t ∈ Finset.Icc 1 T, f t v ≤ _
    rw [hsumf]
    have h1 : (inner ℝ v U : ℝ) ≤ ‖U‖ := by
      calc (inner ℝ v U : ℝ) ≤ ‖v‖ * ‖U‖ := real_inner_le_norm _ _
        _ ≤ 1 * ‖U‖ := mul_le_mul_of_nonneg_right hv (norm_nonneg _)
        _ = ‖U‖ := one_mul _
    have h2 : -‖s0‖ ≤ SupportFunction S v := by
      refine le_trans ?_ (hsupp_ge v s0 hs0)
      have := abs_real_inner_le_norm v s0
      have h3 : ‖v‖ * ‖s0‖ ≤ ‖s0‖ := by nlinarith [norm_nonneg s0]
      nlinarith [neg_abs_le (inner ℝ v s0 : ℝ)]
    nlinarith
  have hle1 : ∑ t ∈ Finset.Icc 1 T, f t wst ≤ sSup ((fun wstar => ∑ t ∈ Finset.Icc 1 T, f t wstar) ''
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    le_csSup hBdd ⟨wst, mem_closedBall_zero_iff.2 hwstn, rfl⟩
  have hplay : ∑ t ∈ Finset.Icc 1 T, f t (w t) ≤ 0 := by
    apply Finset.sum_nonpos
    intro t ht
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 ht
    rw [hf t h1 h2]
    simp only
    rw [huvec t h1 h2, hx t h1 h2]
    exact hO (w t) (hwB t h1 h2) (y t) (hy t h1 h2)
  have hdist : Metric.infDist z S ≤ ‖z - p‖ := by
    rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hpS
  rw [le_div_iff₀ hTpos]
  nlinarith
end OnlineConvexOpt.Blackwell

open OnlineConvexOpt.Blackwell


theorem solution
    {d : ℕ} (K2 : Set (EuclideanSpace ℝ (Fin d))) (S : Set (EuclideanSpace ℝ (Fin d)))
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
    (hf : ∀ t : ℕ, 1 ≤ t → t ≤ T → f t = fun v => inner ℝ v (uvec t) - SupportFunction S v)
    (hw : ∀ t : ℕ, 1 ≤ t → t ≤ T → w t = A f t)
    (hwB : ∀ t : ℕ, 1 ≤ t → t ≤ T → ‖w t‖ ≤ 1)
    (hx : ∀ t : ℕ, 1 ≤ t → t ≤ T → x t = O (w t))
    (huvec : ∀ t : ℕ, 1 ≤ t → t ≤ T → uvec t = u (x t) (y t))
    (hAreg :
      sSup ((fun wstar => ∑ t ∈ Finset.Icc 1 T, f t wstar) ''
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) -
        ∑ t ∈ Finset.Icc 1 T, f t (w t) ≤ RegretBoundA) :
    Metric.infDist ((T : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, uvec t) S ≤ RegretBoundA / T := by
  exact ocorate_core K2 S hSconv hSbdd hSclosed hSne u O hO A RegretBoundA T hT y w x uvec f hy hf hw hwB hx huvec hAreg
