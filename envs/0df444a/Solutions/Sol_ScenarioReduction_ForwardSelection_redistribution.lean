-- Prove2me | solution 1 for ScenarioReduction.ForwardSelection.redistribution
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:24:03.620024+00:00
-- url     : https://prove2.me/submissions/7b08bd74-296f-4c28-adce-4e6c1ec09b12

import Definitions.Def_ScenarioReduction_ForwardSelection_fmCost
import Definitions.Def_ScenarioReduction_ForwardSelection_reductionCost
import Definitions.Def_ScenarioReduction_ForwardSelection_IsTransportPlan
import Mathlib.Tactic
set_option autoImplicit false
open ScenarioReduction.ForwardSelection Finset

private theorem transport_lower {N : ℕ} (c : Fin N → Fin N → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hdiag : ∀ i, c i i = 0)
    (p q : Fin N → ℝ) (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty)
    (η : Fin N → Fin N → ℝ) (hη : IsTransportPlan J p q η) :
    reductionCost c p J hJ ≤ transportCost c J η := by
  let d (i : Fin N) := Jᶜ.inf' hJ (fun j => c i j)
  have hd0 (i : Fin N) : 0 ≤ d i := Finset.le_inf' hJ _ (fun j _ => hc i j)
  have hdz (i : Fin N) (hi : i ∉ J) : d i=0 := by
    apply le_antisymm _ (hd0 i)
    have hi' := Finset.inf'_le (fun j => c i j) (mem_compl.mpr hi)
    simpa [hdiag] using hi'
  have hsum : (∑ i ∈ J, p i*d i) = ∑ i, p i*d i := by
    apply sum_subset (subset_univ J)
    intro i hi hni
    rw [hdz i hni,mul_zero]
  change (∑ i ∈ J, p i*d i) ≤ _
  rw [hsum]
  unfold transportCost
  apply sum_le_sum
  intro i hi
  calc
    p i*d i = ∑ j ∈ Jᶜ, d i*η i j := by rw [← mul_sum,hη.2.2.2 i]; ring
    _ ≤ ∑ j ∈ Jᶜ, c i j*η i j := sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right
      (Finset.inf'_le _ hj) (hη.1 i j (mem_compl.mp hj)))

private theorem plan_attains {N : ℕ} (c : Fin N → Fin N → ℝ)
    (hdiag : ∀ i, c i i=0) (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i,p i=1)
    (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) (jsel : Fin N → Fin N)
    (hsel : ∀ i ∈ J, jsel i ∉ J ∧ ∀ j, j ∉ J → c i (jsel i) ≤ c i j) :
    IsReducedWeight J (redistWeight p J jsel) ∧
      ∃ η : Fin N → Fin N → ℝ, IsTransportPlan J p (redistWeight p J jsel) η ∧
        transportCost c J η = reductionCost c p J hJ := by
  let η (i j : Fin N) := if i ∈ J then (if jsel i=j then p i else 0) else (if i=j then p i else 0)
  have hn (i j : Fin N) : 0 ≤ η i j := by dsimp [η]; split_ifs <;> first | exact hp i | exact le_rfl
  have hz (i j : Fin N) (hj : j ∈ J) : η i j=0 := by
    by_cases hi : i ∈ J
    · have hne : jsel i ≠ j := fun he => (hsel i hi).1 (he ▸ hj)
      simp [η,hi,hne]
    · have hne : i ≠ j := fun he => hi (he ▸ hj)
      simp [η,hi,hne]
  have hrow (i : Fin N) : ∑ j ∈ Jᶜ, η i j=p i := by
    by_cases hi : i ∈ J
    · simp [η,hi,(hsel i hi).1]
    · simp [η,hi]
  have hcol (j : Fin N) (hj : j ∉ J) : ∑ i,η i j=redistWeight p J jsel j := by
    have hdel : ∑ i ∈ J,η i j = ∑ i ∈ J.filter (fun i => jsel i=j),p i := by
      rw [sum_filter]
      apply sum_congr rfl
      intro i hi
      simp [η,hi]
    have hkeep : ∑ i ∈ Jᶜ,η i j=p j := by
      calc
        _ = ∑ i ∈ Jᶜ,if i=j then p i else 0 := by
          apply sum_congr rfl
          intro i hi
          simp [η,mem_compl.mp hi]
        _ = p j := by simp [hj]
    rw [← sum_add_sum_compl J (fun i => η i j),hdel,hkeep]
    simp [redistWeight,hj,add_comm]
  have hq : IsReducedWeight J (redistWeight p J jsel) := by
    refine ⟨?_,?_,?_⟩
    · intro j hj
      rw [← hcol j hj]
      exact sum_nonneg (fun i _ => hn i j)
    · intro j hj
      simp [redistWeight,hj]
    · calc
        _ = ∑ j ∈ Jᶜ,∑ i,η i j := sum_congr rfl (fun j hj => (hcol j (mem_compl.mp hj)).symm)
        _ = ∑ i,∑ j ∈ Jᶜ,η i j := sum_comm
        _ = 1 := by simp_rw [hrow]; exact hsum
  refine ⟨hq,η,⟨fun i j _ => hn i j,fun i j hj => hz i j hj,hcol,hrow⟩,?_⟩
  have hcostrow (i : Fin N) : ∑ j ∈ Jᶜ,c i j*η i j = if i ∈ J then p i*c i (jsel i) else 0 := by
    by_cases hi : i ∈ J
    · simp [η,hi,(hsel i hi).1,mul_comm]
    · simp [η,hi,hdiag]
  unfold transportCost reductionCost
  simp_rw [hcostrow]
  rw [← sum_filter]
  simp only [filter_mem_eq_inter,univ_inter]
  apply sum_congr rfl
  intro i hi
  congr 1
  apply le_antisymm
  · exact Finset.le_inf' hJ _ (fun j hj => (hsel i hi).2 j (mem_compl.mp hj))
  · exact Finset.inf'_le _ (mem_compl.mpr (hsel i hi).1)

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (h : ℝ → ℝ) (hh : IsGrowthFunction h) (ω₀ : E)
    (ω : Fin N → E) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) :
    IsLeast {v : ℝ | ∃ q : Fin N → ℝ, ∃ η : Fin N → Fin N → ℝ, IsReducedWeight J q ∧
        IsTransportPlan J p q η ∧ v = transportCost (scenCost h ω₀ ω) J η}
      (reductionCost (scenCost h ω₀ ω) p J hJ) ∧
    ∀ jsel : Fin N → Fin N,
      (∀ i ∈ J, jsel i ∉ J ∧ ∀ j, j ∉ J → scenCost h ω₀ ω i (jsel i) ≤ scenCost h ω₀ ω i j) →
      IsReducedWeight J (redistWeight p J jsel) ∧
      IsLeast {v : ℝ | ∃ η : Fin N → Fin N → ℝ, IsTransportPlan J p (redistWeight p J jsel) η ∧
          v = transportCost (scenCost h ω₀ ω) J η}
        (reductionCost (scenCost h ω₀ ω) p J hJ)  := by
  have hc (i j : Fin N) : 0 ≤ scenCost h ω₀ ω i j := by
    unfold scenCost fmCost
    positivity
  have hdiag (i : Fin N) : scenCost h ω₀ ω i i=0 := by simp [scenCost,fmCost]
  have hex (i : Fin N) : ∃ j, j ∉ J ∧ ∀ k, k ∉ J → scenCost h ω₀ ω i j ≤ scenCost h ω₀ ω i k := by
    obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image Jᶜ (fun j => scenCost h ω₀ ω i j) hJ
    exact ⟨j,mem_compl.mp hj,fun k hk => hmin k (mem_compl.mpr hk)⟩
  choose js hjs using hex
  have hp0 (i : Fin N) : 0 ≤ p i := (hp i).le
  obtain ⟨hq,η,hη,heq⟩ := plan_attains _ hdiag p hp0 hsum J hJ js (fun i _ => hjs i)
  constructor
  · refine ⟨⟨redistWeight p J js,η,hq,hη,heq.symm⟩,?_⟩
    rintro z ⟨q',η',hq',hη',rfl⟩
    exact transport_lower _ hc hdiag p q' J hJ η' hη'
  · intro jsel hsel
    obtain ⟨hq,η,hη,heq⟩ := plan_attains _ hdiag p hp0 hsum J hJ jsel hsel
    refine ⟨hq,⟨⟨η,hη,heq.symm⟩,?_⟩⟩
    rintro z ⟨η',hη',rfl⟩
    exact transport_lower _ hc hdiag p _ J hJ η' hη'
