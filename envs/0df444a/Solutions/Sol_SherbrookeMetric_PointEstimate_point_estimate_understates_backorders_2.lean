-- Prove2me | solution 2 for SherbrookeMetric.PointEstimate.point_estimate_understates_backorders
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T15:28:37.372162+00:00
-- url     : https://prove2.me/submissions/0e285166-1496-47ee-bc83-2a5aa2671f30

import Mathlib
import Definitions.Def_SherbrookeMetric_PointEstimate_backorders
import Theorems.Thm_SherbrookeMetric_PointEstimate_backorders_strictConvexOn

-- carved verbatim out of submission 121bd557-b91d-4cc0-8b67-9a356fd07840, lines 167-182

section
set_option autoImplicit false
open SherbrookeMetric.PointEstimate ServiceParts.StockLevels

lemma pmf_hasSum (a : ℝ) : HasSum (fun x : ℕ => poissonPmf a x) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (a : ℝ)).mul_left (Real.exp (-a))
  have e : Real.exp (-a) * NormedSpace.exp a = 1 := by
    rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]; simp
  rw [e] at h
  exact h.congr_fun (fun x => by unfold poissonPmf; ring)

lemma mean_hasSum (a : ℝ) : HasSum (fun x : ℕ => (x : ℝ) * poissonPmf a x) a := by
  have h := (pmf_hasSum a).mul_left a
  rw [mul_one] at h
  have e0 : a - ∑ i ∈ Finset.range 1, (i : ℝ) * poissonPmf a i = a := by simp
  have h3 : HasSum (fun n : ℕ => (((n + 1 : ℕ)) : ℝ) * poissonPmf a (n + 1))
      (a - ∑ i ∈ Finset.range 1, (i : ℝ) * poissonPmf a i) := by
    rw [e0]
    refine h.congr_fun (fun n => ?_)
    unfold poissonPmf
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  exact (hasSum_nat_add_iff' 1).mp h3

noncomputable def G : ℕ → ℝ → ℝ
  | 0, a => a
  | s + 1, a => G s a - 1 + ∑ x ∈ Finset.range (s + 1), poissonPmf a x

lemma G_zero (a : ℝ) : G 0 a = a := rfl

lemma G_succ (s : ℕ) (a : ℝ) :
    G (s + 1) a = G s a - 1 + ∑ x ∈ Finset.range (s + 1), poissonPmf a x := rfl

lemma hasSum_term (s : ℕ) (a : ℝ) :
    HasSum (fun x : ℕ => if s < x then ((x : ℝ) - s) * poissonPmf a x else 0) (G s a) := by
  induction s with
  | zero =>
    rw [G_zero]
    refine (mean_hasSum a).congr_fun (fun x => ?_)
    by_cases hx : x = 0
    · subst hx; simp
    · have : 0 < x := Nat.pos_of_ne_zero hx
      simp [this]
  | succ s ih =>
    have hq : HasSum (fun x : ℕ => if s < x then poissonPmf a x else 0)
        (1 - ∑ x ∈ Finset.range (s + 1), poissonPmf a x) := by
      have h2 : HasSum (fun x : ℕ => if x ∈ Finset.range (s + 1) then poissonPmf a x else 0)
          (∑ x ∈ Finset.range (s + 1), (if x ∈ Finset.range (s + 1) then poissonPmf a x else 0)) :=
        hasSum_sum_of_ne_finset_zero (fun b hb => by simp [hb])
      have hs : ∑ x ∈ Finset.range (s + 1), (if x ∈ Finset.range (s + 1) then poissonPmf a x else 0)
          = ∑ x ∈ Finset.range (s + 1), poissonPmf a x :=
        Finset.sum_congr rfl (fun x hx => if_pos hx)
      rw [hs] at h2
      refine ((pmf_hasSum a).sub h2).congr_fun (fun x => ?_)
      by_cases hx : s < x
      · have : ¬ x ∈ Finset.range (s + 1) := by simp; omega
        simp [hx, this]
      · have : x ∈ Finset.range (s + 1) := by simp; omega
        simp [hx, this]
    have hG : G (s + 1) a = G s a - (1 - ∑ x ∈ Finset.range (s + 1), poissonPmf a x) := by
      rw [G_succ]; ring
    rw [hG]
    refine (ih.sub hq).congr_fun (fun x => ?_)
    by_cases h1 : s + 1 < x
    · have h2 : s < x := by omega
      simp only [if_pos h1, if_pos h2]; push_cast; ring
    · by_cases h2 : s < x
      · have : x = s + 1 := by omega
        subst this
        simp
      · simp [h1, h2]

lemma backorders_eq (s : ℕ) (a : ℝ) : backorders s a = G s a := (hasSum_term s a).tsum_eq

theorem solution {K : Type*} [Fintype K] (w lam : K → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) (hlam : ∀ k, 0 < lam k) :
    ((∃ k k', 0 < w k ∧ 0 < w k' ∧ lam k ≠ lam k') →
      ∀ s : ℕ, 1 ≤ s →
        backorders s (∑ k, w k * lam k) < ∑ k, w k * backorders s (lam k)) ∧
    backorders 0 (∑ k, w k * lam k) = ∑ k, w k * backorders 0 (lam k) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨k, k', hk, hk', hne⟩ s hs
    have hsc := SherbrookeMetric.PointEstimate.backorders_strictConvexOn s hs
    have h := (hsc.map_sum_lt_iff_of_nonneg (t := Finset.univ) (w := w) (p := lam)
      (fun i _ => hw i) hw1 (fun i _ => hlam i)).mpr
      ⟨k, Finset.mem_univ _, k', Finset.mem_univ _, hk.ne', hk'.ne', hne⟩
    simpa only [smul_eq_mul] using h
  · have h0 : ∀ a, backorders 0 a = a := fun a => backorders_eq 0 a
    simp only [h0]

end
