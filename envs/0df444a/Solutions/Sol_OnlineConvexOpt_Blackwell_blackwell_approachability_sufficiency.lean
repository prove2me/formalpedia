-- Prove2me | solution 1 for OnlineConvexOpt.Blackwell.blackwell_approachability_sufficiency
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:34:00.545945+00:00
-- url     : https://prove2.me/submissions/68febc28-239a-4c7e-b58d-1fdc731be780

import Mathlib
import Definitions.Def_OnlineConvexOpt_Blackwell_Approachability

namespace OnlineConvexOpt.Blackwell

/-- Adversary's reply: anything different from `x`, inside `[0,1]`. -/
noncomputable def aux_bw_g (x : ℝ) : ℝ := if x = 0 then 1 else 0

/-- Prefixes of the adaptive adversary sequence. -/
noncomputable def aux_bw_f (A : (ℕ → ℝ) → ℕ → ℝ) : ℕ → (ℕ → ℝ)
  | 0 => fun _ => 0
  | n + 1 => Function.update (aux_bw_f A n) n (aux_bw_g (A (aux_bw_f A n) n))

lemma aux_bw_g_ne (x : ℝ) : aux_bw_g x ≠ x := by
  unfold aux_bw_g
  split_ifs with h
  · rw [h]; norm_num
  · exact fun h' => h h'.symm

lemma aux_bw_g_mem (x : ℝ) : aux_bw_g x ∈ Set.Icc (0:ℝ) 1 := by
  unfold aux_bw_g
  split_ifs <;> simp

lemma aux_bw_f_stable (A : (ℕ → ℝ) → ℕ → ℝ) (s : ℕ) :
    ∀ m, s < m → aux_bw_f A m s = aux_bw_f A (s + 1) s := by
  intro m hm
  induction m with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | h
    · rw [aux_bw_f, Function.update_of_ne (by omega), ih h]
    · subst h; rfl

end OnlineConvexOpt.Blackwell

open OnlineConvexOpt.Blackwell

theorem solution : ¬ (∀ {E1 E2 F : Type} [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2]
    [NormedSpace ℝ E2] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K1 : Set E1) (K2 : Set E2) (u : E1 → E2 → F) (S : Set F)
    (hSconv : Convex ℝ S) (hSbdd : Bornology.IsBounded S) (hSclosed : IsClosed S)
    (hK1bdd : Bornology.IsBounded K1) (hK1closed : IsClosed K1) (hK1conv : Convex ℝ K1)
    (hK2bdd : Bornology.IsBounded K2) (hK2closed : IsClosed K2) (hK2conv : Convex ℝ K2)
    (hK1ne : K1.Nonempty) (hK2ne : K2.Nonempty)
    (hcond : ∀ y ∈ K2, ∃ x ∈ K1, u x y ∈ S),
    IsApproachable K1 K2 u S) := by
  intro h
  have hA := h (E1 := ℝ) (E2 := ℝ) (F := ℝ) (Set.Icc 0 1) (Set.Icc 0 1)
    (fun x y => if x = y then (0:ℝ) else 1) {0} (convex_singleton 0)
    Bornology.isBounded_singleton isClosed_singleton (Metric.isBounded_Icc 0 1) isClosed_Icc
    (convex_Icc 0 1) (Metric.isBounded_Icc 0 1) isClosed_Icc (convex_Icc 0 1)
    ⟨0, by simp⟩ ⟨0, by simp⟩ (fun y hy => ⟨y, hy, by simp⟩)
  obtain ⟨A, _hK, hna, hlim⟩ := hA
  set y : ℕ → ℝ := fun t => aux_bw_f A (t + 1) t with hy
  have hpre : ∀ t, ∀ s, s < t → y s = aux_bw_f A t s := by
    intro t s hs
    simp only [hy]
    exact (aux_bw_f_stable A s t hs).symm
  have hAt : ∀ t, A y t = A (aux_bw_f A t) t := fun t => hna _ _ t (hpre t)
  have hyt : ∀ t, y t = aux_bw_g (A (aux_bw_f A t) t) := by
    intro t
    simp only [hy, aux_bw_f, Function.update_self]
  have hu : ∀ t, (if A y t = y t then (0:ℝ) else 1) = 1 := by
    intro t
    rw [if_neg]
    rw [hAt t, hyt t]
    exact fun h' => aux_bw_g_ne _ h'.symm
  have hymem : ∀ t : ℕ, 1 ≤ t → y t ∈ Set.Icc (0:ℝ) 1 := by
    intro t _
    rw [hyt t]; exact aux_bw_g_mem _
  have hT := hlim y hymem
  have hev : (fun T : ℕ => Metric.infDist ((T : ℝ)⁻¹ •
      ∑ t ∈ Finset.Icc 1 T, (if A y t = y t then (0:ℝ) else 1)) ({0} : Set ℝ)) =ᶠ[Filter.atTop]
      fun _ => (1:ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with T hT1
    simp only [hu, Finset.sum_const, Nat.card_Icc, smul_eq_mul, nsmul_eq_mul, Metric.infDist_singleton]
    have : ((T : ℝ))⁻¹ * ((T + 1 - 1 : ℕ) : ℝ) = 1 := by
      rw [Nat.add_sub_cancel]
      have : (T:ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
      field_simp
    rw [mul_one, this, dist_zero_right, norm_one]
  have h1 : Filter.Tendsto (fun T : ℕ => Metric.infDist ((T : ℝ)⁻¹ •
      ∑ t ∈ Finset.Icc 1 T, (if A y t = y t then (0:ℝ) else 1)) ({0} : Set ℝ))
      Filter.atTop (nhds 1) := tendsto_const_nhds.congr' hev.symm
  have := tendsto_nhds_unique hT h1
  norm_num at this
