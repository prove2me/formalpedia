-- Prove2me | solution 1 for ScenarioReduction.Redistribution.optimal_weights
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T01:47:14.175419+00:00
-- url     : https://prove2.me/submissions/93dbfb6c-7acc-475c-ac02-8aa08c29d718

import Mathlib
import Definitions.Def_ScenarioReduction_Redistribution_transportValue

open Finset ScenarioReduction.Redistribution in
theorem solution {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω) (p : Fin N → ℝ)
    (hc : ∀ a b : Ω, 0 ≤ c a b) (hc1 : ∀ a b : Ω, c a b = 0 ↔ a = b)
    (hc2 : ∀ a b : Ω, c a b = c b a)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) :
    IsLeast {x : ℝ | ∃ q : Fin N → ℝ, IsReducedWeight J q ∧ x = transportValue c ω p J q}
        (∑ i ∈ J, p i * minOver Jᶜ (fun j => c (ω i) (ω j))) ∧
      optWeightsValue c ω p J = ∑ i ∈ J, p i * minOver Jᶜ (fun j => c (ω i) (ω j)) ∧
      ∀ jsel : Fin N → Fin N, IsArgminSelector c ω J jsel →
        IsReducedWeight J (qbar p J jsel) ∧
          transportValue c ω p J (qbar p J jsel) = ∑ i ∈ J, p i * minOver Jᶜ (fun j => c (ω i) (ω j)) := by
  classical
  have hm : ∀ i, ∀ j ∈ Jᶜ, minOver Jᶜ (fun j => c (ω i) (ω j)) ≤ c (ω i) (ω j) := by
    intro i j hj
    unfold minOver
    rw [dif_pos hJ]
    exact Finset.inf'_le _ hj
  -- general lower bound on the cost of any transport plan
  have hlow : ∀ (q : Fin N → ℝ) (η : Fin N → Fin N → ℝ), IsTransportPlan p J q η →
      ∑ i ∈ J, p i * minOver Jᶜ (fun j => c (ω i) (ω j)) ≤ transportCost c ω J η := by
    intro q η hη
    obtain ⟨hη0, hrow, _⟩ := hη
    unfold transportCost
    calc ∑ i ∈ J, p i * minOver Jᶜ (fun j => c (ω i) (ω j))
        = ∑ i ∈ J, ∑ j ∈ Jᶜ, minOver Jᶜ (fun j => c (ω i) (ω j)) * η i j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.mul_sum, hrow i, mul_comm]
      _ ≤ ∑ i ∈ J, ∑ j ∈ Jᶜ, c (ω i) (ω j) * η i j := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_right (hm i j hj) (hη0 i j (Finset.mem_compl.mp hj))
      _ ≤ ∑ i, ∑ j ∈ Jᶜ, c (ω i) (ω j) * η i j := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro i _ _
          apply Finset.sum_nonneg
          intro j hj
          exact mul_nonneg (hc _ _) (hη0 i j (Finset.mem_compl.mp hj))
  -- lower bound for every feasible q
  have hlowq : ∀ q : Fin N → ℝ, IsReducedWeight J q →
      ∑ i ∈ J, p i * minOver Jᶜ (fun j => c (ω i) (ω j)) ≤ transportValue c ω p J q := by
    intro q hq
    obtain ⟨hq0, hq1⟩ := hq
    unfold transportValue
    apply le_csInf
    · refine ⟨_, fun i j => p i * q j, ⟨?_, ?_, ?_⟩, rfl⟩
      · intro i j hj
        exact mul_nonneg (hp i).le (hq0 j hj)
      · intro i
        rw [← Finset.mul_sum, hq1, mul_one]
      · intro j _
        rw [← Finset.sum_mul, hp1, one_mul]
    · rintro x ⟨η, hη, rfl⟩
      exact hlow q η hη
  -- achievability for any argmin selector
  have hach : ∀ jsel : Fin N → Fin N, IsArgminSelector c ω J jsel →
      IsReducedWeight J (qbar p J jsel) ∧
        transportValue c ω p J (qbar p J jsel) =
          ∑ i ∈ J, p i * minOver Jᶜ (fun j => c (ω i) (ω j)) := by
    intro jsel hsel
    have hmin : ∀ i ∈ J, minOver Jᶜ (fun j => c (ω i) (ω j)) = c (ω i) (ω (jsel i)) := by
      intro i hi
      unfold minOver
      rw [dif_pos hJ]
      apply le_antisymm
      · exact Finset.inf'_le _ (Finset.mem_compl.mpr (hsel i hi).1)
      · exact Finset.le_inf' _ _ (fun j hj => (hsel i hi).2 j (Finset.mem_compl.mp hj))
    let η : Fin N → Fin N → ℝ := fun i j =>
      if i ∈ J then (if j = jsel i then p i else 0) else (if j = i then p i else 0)
    have hη0 : ∀ i, ∀ j ∉ J, 0 ≤ η i j := by
      intro i j _
      simp only [η]
      split_ifs <;> first | exact (hp i).le | exact le_rfl
    have hrow : ∀ i, ∑ j ∈ Jᶜ, η i j = p i := by
      intro i
      by_cases hi : i ∈ J
      · simp only [η, if_pos hi]
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_compl.mpr (hsel i hi).1)]
      · simp only [η, if_neg hi]
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_compl.mpr hi)]
    have hcol : ∀ j ∉ J, ∑ i, η i j = qbar p J jsel j := by
      intro j hj
      have hpt : ∀ i, η i j =
          (if i ∈ J then (if jsel i = j then p i else 0) else 0) + (if j = i then p i else 0) := by
        intro i
        by_cases hi : i ∈ J
        · have hij : j ≠ i := fun h => hj (h ▸ hi)
          simp only [η, if_pos hi, if_neg hij, add_zero]
          by_cases hji : j = jsel i
          · rw [if_pos hji, if_pos hji.symm]
          · rw [if_neg hji, if_neg (fun h => hji h.symm)]
        · simp only [η, if_neg hi, zero_add]
      rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_ite_eq]
      rw [if_pos (Finset.mem_univ _), Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_filter]
      unfold qbar
      ring
    have hcost : transportCost c ω J η = ∑ i ∈ J, p i * minOver Jᶜ (fun j => c (ω i) (ω j)) := by
      unfold transportCost
      have hr : ∀ i, ∑ j ∈ Jᶜ, c (ω i) (ω j) * η i j =
          if i ∈ J then p i * minOver Jᶜ (fun j => c (ω i) (ω j)) else 0 := by
        intro i
        by_cases hi : i ∈ J
        · simp only [η, if_pos hi, mul_ite, mul_zero]
          rw [Finset.sum_ite_eq', if_pos (Finset.mem_compl.mpr (hsel i hi).1), hmin i hi, mul_comm]
        · simp only [η, if_neg hi, mul_ite, mul_zero]
          rw [Finset.sum_ite_eq', if_pos (Finset.mem_compl.mpr hi), (hc1 _ _).mpr rfl, zero_mul]
      rw [Finset.sum_congr rfl (fun i _ => hr i), Finset.sum_ite_mem, Finset.univ_inter]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro j _
      exact add_nonneg (hp j).le (Finset.sum_nonneg fun i _ => (hp i).le)
    · calc ∑ j ∈ Jᶜ, qbar p J jsel j = ∑ j ∈ Jᶜ, ∑ i, η i j :=
            Finset.sum_congr rfl (fun j hj => (hcol j (Finset.mem_compl.mp hj)).symm)
        _ = ∑ i, ∑ j ∈ Jᶜ, η i j := Finset.sum_comm
        _ = 1 := by rw [Finset.sum_congr rfl (fun i _ => hrow i), hp1]
    · unfold transportValue
      apply IsLeast.csInf_eq
      refine ⟨⟨η, ⟨hη0, hrow, hcol⟩, hcost.symm⟩, ?_⟩
      rintro x ⟨η', hη', rfl⟩
      exact hlow _ η' hη'
  have hex : ∃ jsel : Fin N → Fin N, IsArgminSelector c ω J jsel := by
    choose g hg using fun i => Finset.exists_min_image Jᶜ (fun j => c (ω i) (ω j)) hJ
    exact ⟨g, fun i _ => ⟨Finset.mem_compl.mp (hg i).1,
      fun j hj => (hg i).2 j (Finset.mem_compl.mpr hj)⟩⟩
  have hleast : IsLeast {x : ℝ | ∃ q : Fin N → ℝ, IsReducedWeight J q ∧ x = transportValue c ω p J q}
      (∑ i ∈ J, p i * minOver Jᶜ (fun j => c (ω i) (ω j))) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨g, hg⟩ := hex
      exact ⟨qbar p J g, (hach g hg).1, (hach g hg).2.symm⟩
    · rintro x ⟨q, hq, rfl⟩
      exact hlowq q hq
  refine ⟨hleast, ?_, hach⟩
  unfold optWeightsValue
  exact hleast.csInf_eq
