-- Prove2me | solution 2 for ShapleyFolkman.shapley_folkman_lemma
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-10T05:27:14.699771+00:00
-- url     : https://prove2.me/submissions/c2b4ca7a-7189-4e42-89fa-587d881d62c2

import Mathlib
open scoped Pointwise

theorem solution (N m : ℕ) (S : Fin m → Set (EuclideanSpace ℝ (Fin N)))
    (x : EuclideanSpace ℝ (Fin N)) (hx : x ∈ convexHull ℝ (∑ i, S i)) :
    ∃ y : Fin m → EuclideanSpace ℝ (Fin N),
      (∀ i, y i ∈ convexHull ℝ (S i)) ∧ ∑ i, y i = x ∧
        {i | y i ∉ S i}.ncard ≤ N := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨fun _ => 0, fun i => i.elim0, ?_, ?_⟩
    · simp only [Finset.univ_eq_empty, Finset.sum_empty] at hx ⊢
      rw [show (0 : Set (EuclideanSpace ℝ (Fin N))) = {0} from rfl, convexHull_singleton] at hx
      exact hx.symm
    · simp [Set.eq_empty_of_isEmpty]
  set T : Set (EuclideanSpace ℝ (Fin N) × (Fin m → ℝ)) := {p | ∃ i, p.1 ∈ S i ∧ p.2 = Pi.single i 1} with hT
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- step 1
  rw [convexHull_sum] at hx
  obtain ⟨g, hg, hgx⟩ := Set.mem_finsetSum _ _ _ |>.mp hx
  have hp0 : ((1 / (m : ℝ)) • x, fun _ => 1 / (m : ℝ)) ∈ convexHull ℝ T := by
    have hgi : ∀ i, (g i, (Pi.single i 1 : Fin m → ℝ)) ∈ convexHull ℝ T := by
      intro i
      have h1 : (g i, (Pi.single i 1 : Fin m → ℝ)) ∈
          convexHull ℝ (S i ×ˢ ({Pi.single i 1} : Set (Fin m → ℝ))) := by
        rw [convexHull_prod, convexHull_singleton]
        exact ⟨hg (Finset.mem_univ i), rfl⟩
      refine convexHull_mono ?_ h1
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      exact ⟨i, ha, hb⟩
    have := (convex_convexHull ℝ T).sum_mem (t := Finset.univ)
      (w := fun _ => 1 / (m : ℝ)) (z := fun i => (g i, (Pi.single i 1 : Fin m → ℝ)))
      (fun _ _ => by positivity) (by simp [hmR.ne']) (fun i _ => hgi i)
    convert this using 1
    ext1
    · simp [Prod.fst_sum, ← Finset.smul_sum, hgx]
    · funext k
      simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  -- step 2
  obtain ⟨ι, _, z, w, hzT, hzai, hwpos, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hp0
  have hzT' : ∀ j, ∃ i, (z j).1 ∈ S i ∧ (z j).2 = Pi.single i 1 := fun j => hzT ⟨j, rfl⟩
  choose c hcS hc2 using hzT'
  have hli : LinearIndependent ℝ z := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have hsum : ∑ j, a j = 0 := by
      have := congrArg (fun v : EuclideanSpace ℝ (Fin N) × (Fin m → ℝ) => ∑ k, v.2 k) ha
      simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply, hc2,
        Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at this
      rw [Finset.sum_comm] at this
      simpa using this
    rw [affineIndependent_iff_of_fintype] at hzai
    refine hzai a hsum ?_
    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hsum 0,
      Finset.weightedVSubOfPoint_apply]
    simpa using ha
  have hcard : Fintype.card ι ≤ N + m := by
    have := hli.fintype_card_le_finrank
    simpa [finrank_euclideanSpace] using this
  -- step 3
  let F : Fin m → Finset ι := fun i => Finset.univ.filter (fun j => c j = i)
  have hFw : ∀ i, ∑ j ∈ F i, w j = 1 / (m : ℝ) := by
    intro i
    have := congrArg (fun v : EuclideanSpace ℝ (Fin N) × (Fin m → ℝ) => v.2 i) hwz
    simp only [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, hc2,
      Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at this
    rw [← this, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    simp [F, eq_comm]
  let y : Fin m → EuclideanSpace ℝ (Fin N) := fun i => ∑ j ∈ F i, ((m : ℝ) * w j) • (z j).1
  refine ⟨y, ?_, ?_, ?_⟩
  · intro i
    refine (convex_convexHull ℝ (S i)).sum_mem (w := fun j => (m : ℝ) * w j)
      (z := fun j => (z j).1) (fun j _ => by have := hwpos j; positivity)
      ?_ (fun j hj => subset_convexHull ℝ _ ?_)
    · rw [← Finset.mul_sum, hFw]; field_simp
    · have := (Finset.mem_filter.mp hj).2
      rw [← this]; exact hcS j
  · have h1 := congrArg Prod.fst hwz
    simp only [Prod.fst_sum, Prod.smul_fst] at h1
    simp only [y, F, mul_smul, ← Finset.smul_sum]
    rw [Finset.sum_fiberwise (g := c) (f := fun j => w j • (z j).1), h1,
      smul_smul, mul_one_div_cancel hmR.ne', one_smul]
  · have hne : ∀ i, 1 ≤ (F i).card := by
      intro i
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      have := hFw i
      rw [Finset.card_eq_zero.mp h0, Finset.sum_empty] at this
      have : (0 : ℝ) < 1 / m := by positivity
      linarith
    set B := Finset.univ.filter (fun i => 2 ≤ (F i).card)
    have hsub : {i | y i ∉ S i} ⊆ (B : Set (Fin m)) := by
      intro i hi
      simp only [B, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi ⊢
      by_contra hlt
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (show (F i).card = 1 by have := hne i; omega)
      apply hi
      have hwj : (m : ℝ) * w j = 1 := by
        have := hFw i; rw [hj, Finset.sum_singleton] at this
        rw [this]; field_simp
      have hjF : j ∈ F i := hj ▸ Finset.mem_singleton_self j
      have hcj : c j = i := (Finset.mem_filter.mp hjF).2
      simp only [y, hj, Finset.sum_singleton, hwj, one_smul]
      rw [← hcj]; exact hcS j
    calc {i | y i ∉ S i}.ncard ≤ (B : Set (Fin m)).ncard := Set.ncard_le_ncard hsub
      _ = B.card := Set.ncard_coe_finset B
      _ ≤ N := by
        have hsumF : ∑ i, (F i).card = Fintype.card ι := by
          rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := c)
            (fun _ _ => Finset.mem_univ _)]
        have hle : ∑ i : Fin m, (1 + if 2 ≤ (F i).card then 1 else 0) ≤ ∑ i, (F i).card := by
          apply Finset.sum_le_sum
          intro i _
          have := hne i
          split_ifs <;> omega
        rw [Finset.sum_add_distrib, ← Finset.card_filter] at hle
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          mul_one] at hle
        have hB : B.card = (Finset.univ.filter fun i => 2 ≤ (F i).card).card := rfl
        omega
