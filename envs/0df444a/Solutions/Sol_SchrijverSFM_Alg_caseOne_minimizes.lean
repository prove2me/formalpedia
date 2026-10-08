-- Prove2me | solution 1 for SchrijverSFM.Alg.caseOne_minimizes
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:06:32.299121+00:00
-- url     : https://prove2.me/submissions/8a61a2a9-3795-41a9-adc0-7245de5fd028

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting

open SchrijverSFM.Alg NonmonotoneSubmod.Shared Finset

private theorem marginal {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (X Y : Finset (Fin n)) (hXY : X ⊆ Y) (v : Fin n) (hv : v ∉ Y) :
    f (insert v Y) - f Y ≤ f (insert v X) - f X := by
  have hu : insert v X ∪ Y = insert v Y := by
    ext a
    simp only [mem_union, mem_insert]
    constructor
    · rintro ((rfl | ha) | ha)
      · exact Or.inl rfl
      · exact Or.inr (hXY ha)
      · exact Or.inr ha
    · rintro (rfl | ha)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ha
  have hi : insert v X ∩ Y = X := by
    ext a
    simp only [mem_inter, mem_insert]
    constructor
    · rintro ⟨rfl | ha, hy⟩
      · exact False.elim (hv hy)
      · exact ha
    · intro ha
      exact ⟨Or.inr ha, hXY ha⟩
  have h := hsub (insert v X) Y
  rw [hu, hi] at h
  linarith

private theorem greedy_facts {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (hf0 : f ∅ = 0) (σ : Equiv.Perm (Fin n)) :
    (∀ U : Finset (Fin n), IsLowerIdeal σ U → xsum (greedy f σ) U = f U) ∧
      greedy f σ ∈ baseB f := by
  classical
  have all (U : Finset (Fin n)) : xsum (greedy f σ) U ≤ f U ∧
      (IsLowerIdeal σ U → xsum (greedy f σ) U = f U) := by
    refine Finset.strongInductionOn U ?_
    intro U ih
    by_cases hU : U = ∅
    · subst U
      simp [xsum, hf0]
    obtain ⟨v, hv, hmax⟩ := exists_max_image U σ (nonempty_iff_ne_empty.mpr hU)
    let V := U.erase v
    have hvV : v ∉ V := by simp [V]
    have hVU : V ⊂ U := erase_ssubset hv
    have hVb : V ⊆ before σ v := by
      intro x hx
      have hxU := (mem_erase.mp hx).2
      have hne := (mem_erase.mp hx).1
      have hle := hmax x hxU
      have hneq : σ x ≠ σ v := fun h => hne (σ.injective h)
      exact mem_filter.mpr ⟨mem_univ _, lt_of_le_of_ne hle hneq⟩
    have hvb : v ∉ before σ v := by simp [before]
    have hrec := ih V hVU
    have hins : insert v V = U := insert_erase hv
    have hsum : xsum (greedy f σ) U = greedy f σ v + xsum (greedy f σ) V := by
      rw [← hins]
      exact sum_insert hvV
    have hmar := marginal f hsub V (before σ v) hVb v hvb
    constructor
    · rw [hsum]
      change f (insert v (before σ v)) - f (before σ v) + xsum (greedy f σ) V ≤ f U
      rw [hins] at hmar
      linarith [hrec.1]
    · intro hideal
      have hVe : V = before σ v := by
        apply Subset.antisymm hVb
        intro x hx
        have hlt := (mem_filter.mp hx).2
        exact mem_erase.mpr ⟨fun h => by subst x; exact lt_irrefl _ hlt, hideal v hv x hlt⟩
      have hVi : IsLowerIdeal σ V := by
        intro u hu w hw
        have hub := (mem_filter.mp (hVb hu)).2
        rw [hVe]
        exact mem_filter.mpr ⟨mem_univ _, hw.trans hub⟩
      rw [hsum, hrec.2 hVi]
      unfold greedy
      rw [← hVe, hins]
      ring
  have hfull : IsLowerIdeal σ (univ : Finset (Fin n)) := by
    intro u hu w hw
    exact mem_univ _
  exact ⟨fun U hU => (all U).2 hU, fun U => (all U).1, (all univ).2 hfull⟩

theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (hf0 : f ∅ = 0) (S : State n) (hS : Valid S) (h1 : caseOne f S) :
    ∀ W : Finset (Fin n), f (caseOneSet f S) ≤ f W := by
  classical
  let U := caseOneSet f S
  have hideal (q) (hq : q ∈ S) : IsLowerIdeal q.1 U := by
    intro u hu v hv
    obtain ⟨w, hw, huw⟩ := (mem_filter.mp hu).2
    exact mem_filter.mpr ⟨mem_univ _, w, hw,
      (Relation.ReflTransGen.single (show arc S v u from ⟨q, hq, hv⟩)).trans huw⟩
  have hnonpos (v) (hv : v ∈ U) : point f S v ≤ 0 := by
    by_contra hn
    have hp : v ∈ posSet f S := mem_filter.mpr ⟨mem_univ _, lt_of_not_ge hn⟩
    obtain ⟨w, hw, hvw⟩ := (mem_filter.mp hv).2
    exact h1 ⟨w, hw, v, hp, hvw⟩
  have hnonneg (v) (hv : v ∉ U) : 0 ≤ point f S v := by
    by_contra hn
    have hw : v ∈ negSet f S := mem_filter.mpr ⟨mem_univ _, lt_of_not_ge hn⟩
    exact hv (mem_filter.mpr ⟨mem_univ _, v, hw, Relation.ReflTransGen.refl⟩)
  have hsum (W : Finset (Fin n)) :
      xsum (point f S) W = (S.map (fun q => q.2 * xsum (greedy f q.1) W)).sum := by
    unfold xsum point
    clear hS h1 hideal hnonpos hnonneg U
    induction S with
    | nil => simp
    | cons q S ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [sum_add_distrib, ih, mul_sum]
  have hU : xsum (point f S) U = f U := by
    rw [hsum]
    have he : S.map (fun q => q.2 * xsum (greedy f q.1) U) =
        S.map (fun q => q.2 * f U) := by
      apply List.map_congr_left
      intro q hq
      rw [(greedy_facts f hsub hf0 q.1).1 U (hideal q hq)]
    rw [he, List.sum_map_mul_right, hS.2.2, one_mul]
  have hbase (W : Finset (Fin n)) : xsum (point f S) W ≤ f W := by
    rw [hsum]
    calc
      _ ≤ (S.map (fun q => q.2 * f W)).sum := by
        exact List.sum_le_sum fun q hq =>
          mul_le_mul_of_nonneg_left ((greedy_facts f hsub hf0 q.1).2.1 W) (hS.2.1 q hq).le
      _ = f W := by rw [List.sum_map_mul_right, hS.2.2, one_mul]
  intro W
  rw [← hU]
  apply le_trans _ (hbase W)
  unfold xsum
  have heU := sum_sdiff (f := point f S) (show U ∩ W ⊆ U from inter_subset_left)
  have heW := sum_sdiff (f := point f S) (show U ∩ W ⊆ W from inter_subset_right)
  have ha : (∑ v ∈ U \ W, point f S v) ≤ 0 :=
    sum_nonpos fun v hv => hnonpos v (mem_sdiff.mp hv).1
  have hb : 0 ≤ ∑ v ∈ W \ U, point f S v :=
    sum_nonneg fun v hv => hnonneg v (mem_sdiff.mp hv).2
  have ha' : (∑ v ∈ U \ (U ∩ W), point f S v) ≤ 0 := by
    simpa [sdiff_inter_self_right] using ha
  have hb' : 0 ≤ ∑ v ∈ W \ (U ∩ W), point f S v := by
    simpa [sdiff_inter_self_left] using hb
  linarith

#print axioms solution
