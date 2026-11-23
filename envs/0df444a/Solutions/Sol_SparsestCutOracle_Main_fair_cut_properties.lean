-- Prove2me | solution 1 for SparsestCutOracle.Main.fair_cut_properties
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:32:28.915209+00:00
-- url     : https://prove2.me/submissions/20f5a9d1-b34c-44b8-8898-c40e0a73b481

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_FairFlow

namespace SparsestCutOracle.Main

private lemma sum_netFlow_compl {n : ℕ} {f : Flow n}
    (hf : ∀ u v, f u v = -f v u) (X : Finset (Fin n)) :
    (∑ u ∈ X, netFlow f u) = ∑ u ∈ X, ∑ v ∈ Xᶜ, f u v := by
  have hinternal : (∑ u ∈ X, ∑ v ∈ X, f u v) = 0 := by
    have hneg : (∑ u ∈ X, ∑ v ∈ X, f u v) =
        -(∑ u ∈ X, ∑ v ∈ X, f u v) := by
      calc
        (∑ u ∈ X, ∑ v ∈ X, f u v) = ∑ v ∈ X, ∑ u ∈ X, f u v :=
          Finset.sum_comm
        _ = ∑ v ∈ X, ∑ u ∈ X, -f v u := by
          apply Finset.sum_congr rfl
          intro v hv
          apply Finset.sum_congr rfl
          intro u hu
          exact hf u v
        _ = -(∑ v ∈ X, ∑ u ∈ X, f v u) := by
          simp only [Finset.sum_neg_distrib]
        _ = -(∑ u ∈ X, ∑ v ∈ X, f u v) := by rw [Finset.sum_comm]
    linarith
  calc
    (∑ u ∈ X, netFlow f u) = ∑ u ∈ X, ∑ v, f u v := rfl
    _ = ∑ u ∈ X, ((∑ v ∈ X, f u v) + ∑ v ∈ Xᶜ, f u v) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact (Finset.sum_add_sum_compl X (f u)).symm
    _ = (∑ u ∈ X, ∑ v ∈ X, f u v) + ∑ u ∈ X, ∑ v ∈ Xᶜ, f u v := by
      rw [Finset.sum_add_distrib]
    _ = ∑ u ∈ X, ∑ v ∈ Xᶜ, f u v := by rw [hinternal, zero_add]

private lemma cut_comm {n : ℕ} (G : ClusterDecomp.WGraph (Fin n))
    (S T : Finset (Fin n)) : cut G S T = cut G T S := by
  unfold cut ClusterDecomp.WGraph.cut ClusterDecomp.cutCap
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  exact G.symm v u

end SparsestCutOracle.Main

open SparsestCutOracle.Main

/-- Claim 1 (Lemma 7 in [HMR26]), pp.9–10, including both local inequalities. -/
theorem solution {n : ℕ} (G : ClusterDecomp.WGraph (Fin n))
    (s t : Fin n → ℝ) (ω : ℝ) (U : Finset (Fin n))
    (h : FairCut G s t ω U) :
    cut G U Uᶜ + mass t U ≤ ω * mass s U ∧
    cut G U Uᶜ + mass s Uᶜ ≤ ω * mass t Uᶜ ∧
    (∀ A : Finset (Fin n), A ⊆ U →
      cut G A Uᶜ + mass t A ≤ ω * (mass s A + cut G A (U \ A))) ∧
    (∀ B : Finset (Fin n), B ⊆ Uᶜ →
      cut G B U + mass s B ≤ ω * (mass t B + cut G B (Uᶜ \ B))) := by
  obtain ⟨f, hω, hs, ht, ⟨hanti, hcap⟩, hsource, htarget,
    hsourceSat, htargetSat, hedge⟩ := h
  have hωpos : 0 < ω := lt_of_lt_of_le zero_lt_one hω
  have hωnonneg : 0 ≤ ω := hωpos.le

  have hlocal3 : ∀ A : Finset (Fin n), A ⊆ U →
      cut G A Uᶜ + mass t A ≤ ω * (mass s A + cut G A (U \ A)) := by
    intro A hA
    have hcomp : Aᶜ = (U \ A) ∪ Uᶜ := by
      ext v
      simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hv
        by_cases hvU : v ∈ U
        · exact Or.inl ⟨hvU, hv⟩
        · exact Or.inr hvU
      · rintro (⟨hvU, hvA⟩ | hvU)
        · exact hvA
        · intro hvA
          exact hvU (hA hvA)
    have hdisj : Disjoint (U \ A) Uᶜ := by
      apply Finset.disjoint_left.mpr
      intro v hvU hvUc
      exact (Finset.mem_compl.mp hvUc) (Finset.mem_sdiff.mp hvU).1
    have hnet : (∑ v ∈ A, netFlow f v) =
        (∑ v ∈ A, ∑ u ∈ U \ A, f v u) +
          ∑ v ∈ A, ∑ u ∈ Uᶜ, f v u := by
      calc
        (∑ v ∈ A, netFlow f v) = ∑ v ∈ A, ∑ u ∈ Aᶜ, f v u :=
          SparsestCutOracle.Main.sum_netFlow_compl hanti A
        _ = ∑ v ∈ A, ∑ u ∈ (U \ A) ∪ Uᶜ, f v u := by rw [hcomp]
        _ = (∑ v ∈ A, ∑ u ∈ U \ A, f v u) +
            ∑ v ∈ A, ∑ u ∈ Uᶜ, f v u := by
          simp_rw [Finset.sum_union hdisj]
          rw [Finset.sum_add_distrib]
    have hcross : cut G A Uᶜ ≤ ω * ∑ v ∈ A, ∑ u ∈ Uᶜ, f v u := by
      calc
        cut G A Uᶜ = ∑ v ∈ A, ∑ u ∈ Uᶜ, G.w v u := rfl
        _ ≤ ∑ v ∈ A, ∑ u ∈ Uᶜ, ω * f v u := by
          apply Finset.sum_le_sum
          intro v hv
          apply Finset.sum_le_sum
          intro u hu
          have he := hedge v (hA hv) u hu
          have he' := (div_le_iff₀ hωpos).mp he
          nlinarith
        _ = ω * ∑ v ∈ A, ∑ u ∈ Uᶜ, f v u := by
          simp only [Finset.mul_sum]
    have hinternal : -(ω * cut G A (U \ A)) ≤
        ω * ∑ v ∈ A, ∑ u ∈ U \ A, f v u := by
      calc
        -(ω * cut G A (U \ A)) =
            ∑ v ∈ A, ∑ u ∈ U \ A, -(ω * G.w v u) := by
          simp only [cut, ClusterDecomp.WGraph.cut, ClusterDecomp.cutCap,
            Finset.mul_sum, Finset.sum_neg_distrib]
        _ ≤ ∑ v ∈ A, ∑ u ∈ U \ A, ω * f v u := by
          apply Finset.sum_le_sum
          intro v hv
          apply Finset.sum_le_sum
          intro u hu
          have he := (abs_le.mp (hcap v u)).1
          have he' := mul_le_mul_of_nonneg_left he hωnonneg
          nlinarith
        _ = ω * ∑ v ∈ A, ∑ u ∈ U \ A, f v u := by
          simp only [Finset.mul_sum]
    have hvertices : ω * (∑ v ∈ A, netFlow f v) ≤
        ω * mass s A - mass t A := by
      calc
        ω * (∑ v ∈ A, netFlow f v) = ∑ v ∈ A, ω * netFlow f v := by
          rw [Finset.mul_sum]
        _ ≤ ∑ v ∈ A, (ω * s v - t v) := by
          apply Finset.sum_le_sum
          intro v hv
          by_cases hst : 0 ≤ s v - t v
          · have he := (hsource v hst).2
            have he' := mul_le_mul_of_nonneg_left he hωnonneg
            have hnonneg := mul_nonneg (sub_nonneg.mpr hω) (ht v)
            nlinarith
          · have hst' : s v - t v ≤ 0 := le_of_not_ge hst
            have he := htargetSat v hst' (hA hv)
            have he' := (le_div_iff₀ hωpos).mp he
            have hnonneg := mul_nonneg (sub_nonneg.mpr hω) (hs v)
            nlinarith
        _ = ω * mass s A - mass t A := by
          simp only [mass, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hnet] at hvertices
    nlinarith

  have hlocal4 : ∀ B : Finset (Fin n), B ⊆ Uᶜ →
      cut G B U + mass s B ≤ ω * (mass t B + cut G B (Uᶜ \ B)) := by
    intro B hB
    have hcomp : Bᶜ = U ∪ (Uᶜ \ B) := by
      ext v
      simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hv
        by_cases hvU : v ∈ U
        · exact Or.inl hvU
        · exact Or.inr ⟨hvU, hv⟩
      · rintro (hvU | ⟨hvU, hvB⟩)
        · intro hvB
          exact (Finset.mem_compl.mp (hB hvB)) hvU
        · exact hvB
    have hdisj : Disjoint U (Uᶜ \ B) := by
      apply Finset.disjoint_left.mpr
      intro v hvU hv
      exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hv).1) hvU
    have hnet : (∑ v ∈ B, netFlow f v) =
        (∑ v ∈ B, ∑ u ∈ U, f v u) +
          ∑ v ∈ B, ∑ u ∈ Uᶜ \ B, f v u := by
      calc
        (∑ v ∈ B, netFlow f v) = ∑ v ∈ B, ∑ u ∈ Bᶜ, f v u :=
          SparsestCutOracle.Main.sum_netFlow_compl hanti B
        _ = ∑ v ∈ B, ∑ u ∈ U ∪ (Uᶜ \ B), f v u := by rw [hcomp]
        _ = (∑ v ∈ B, ∑ u ∈ U, f v u) +
            ∑ v ∈ B, ∑ u ∈ Uᶜ \ B, f v u := by
          simp_rw [Finset.sum_union hdisj]
          rw [Finset.sum_add_distrib]
    have hcross : ω * (∑ v ∈ B, ∑ u ∈ U, f v u) ≤ -cut G B U := by
      calc
        ω * (∑ v ∈ B, ∑ u ∈ U, f v u) =
            ∑ v ∈ B, ∑ u ∈ U, ω * f v u := by
          simp only [Finset.mul_sum]
        _ ≤ ∑ v ∈ B, ∑ u ∈ U, -G.w v u := by
          apply Finset.sum_le_sum
          intro v hv
          apply Finset.sum_le_sum
          intro u hu
          have he := hedge u hu v (hB hv)
          have he' := (div_le_iff₀ hωpos).mp he
          have ha := hanti v u
          have hsymm := G.symm u v
          nlinarith
        _ = -cut G B U := by
          simp only [cut, ClusterDecomp.WGraph.cut, ClusterDecomp.cutCap,
            Finset.sum_neg_distrib]
    have hinternal : ω * (∑ v ∈ B, ∑ u ∈ Uᶜ \ B, f v u) ≤
        ω * cut G B (Uᶜ \ B) := by
      calc
        ω * (∑ v ∈ B, ∑ u ∈ Uᶜ \ B, f v u) =
            ∑ v ∈ B, ∑ u ∈ Uᶜ \ B, ω * f v u := by
          simp only [Finset.mul_sum]
        _ ≤ ∑ v ∈ B, ∑ u ∈ Uᶜ \ B, ω * G.w v u := by
          apply Finset.sum_le_sum
          intro v hv
          apply Finset.sum_le_sum
          intro u hu
          have he := (abs_le.mp (hcap v u)).2
          exact mul_le_mul_of_nonneg_left he hωnonneg
        _ = ω * cut G B (Uᶜ \ B) := by
          simp only [cut, ClusterDecomp.WGraph.cut, ClusterDecomp.cutCap,
            Finset.mul_sum]
    have hvertices : mass s B - ω * mass t B ≤
        ω * (∑ v ∈ B, netFlow f v) := by
      calc
        mass s B - ω * mass t B = ∑ v ∈ B, (s v - ω * t v) := by
          simp only [mass, Finset.sum_sub_distrib, Finset.mul_sum]
        _ ≤ ∑ v ∈ B, ω * netFlow f v := by
          apply Finset.sum_le_sum
          intro v hv
          by_cases hst : 0 ≤ s v - t v
          · have he := hsourceSat v hst (Finset.mem_compl.mp (hB hv))
            have he' := (div_le_iff₀ hωpos).mp he
            have hnonneg := mul_nonneg (sub_nonneg.mpr hω) (ht v)
            nlinarith
          · have hst' : s v - t v ≤ 0 := le_of_not_ge hst
            have he := (htarget v hst').2
            have he' := mul_le_mul_of_nonneg_left he hωnonneg
            have hnonneg := mul_nonneg (sub_nonneg.mpr hω) (hs v)
            nlinarith
        _ = ω * (∑ v ∈ B, netFlow f v) := by rw [Finset.mul_sum]
    rw [hnet] at hvertices
    nlinarith

  refine ⟨?_, ?_, hlocal3, hlocal4⟩
  · have he := hlocal3 U (by rfl)
    simpa [cut, ClusterDecomp.WGraph.cut, ClusterDecomp.cutCap] using he
  · have he := hlocal4 Uᶜ (by rfl)
    rw [SparsestCutOracle.Main.cut_comm G Uᶜ U] at he
    simpa [cut, ClusterDecomp.WGraph.cut, ClusterDecomp.cutCap] using he
