-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_chartBundle_exists_gens_5a8ab43d7914
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:41:26.585271+00:00
-- url     : https://prove2.me/submissions/d906d8a5-a441-4557-9ef6-8a9b628d21f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_sum_mul_pow_eq_one_1fdd236d5c86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_chartBundle_pow_smul_mem_e5a323984de9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
variable {R : Type*} [CommRing R] [Algebra R Ω] {τ : Type*} {x : τ → Ω} {r : ℕ}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (B : ChartBundle R x r E) {i : τ} (hi : x i ≠ 0) :
    ∃ (k : ℕ) (G : Fin k × Fin r → E), (∀ j, G j ∈ B.lat i) ∧
      ∀ e ∈ B.lat i, ∃ β : Fin k × Fin r → Ω, (∀ j, β j ∈ chartRing R x i) ∧
        e = ∑ j, β j • G j := by
  classical
  obtain ⟨k, f, c, hf, hc, hsum, hb⟩ := B.frame i hi
  choose b _ _ hiff using hb
  have hbsat : ∀ l q, ∃ n : ℕ, f l ^ n • b l q ∈ B.lat i := by
    intro l q
    refine (hiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, by simp [Pi.single_apply]⟩
    rw [pow_zero, one_mul]
    by_cases h : q' = q
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  choose n hn using hbsat
  set n₀ := Finset.univ.sup fun lq : Fin k × Fin r => n lq.1 lq.2 with hn₀
  have hle : ∀ l q, n l q ≤ n₀ := fun l q =>
    Finset.le_sup (f := fun lq : Fin k × Fin r => n lq.1 lq.2) (Finset.mem_univ (l, q))
  refine ⟨k, fun lq => f lq.1 ^ n₀ • b lq.1 lq.2, fun lq => ?_, fun e he => ?_⟩
  · have : f lq.1 ^ n₀ • b lq.1 lq.2 = f lq.1 ^ (n₀ - n lq.1 lq.2) • f lq.1 ^ n lq.1 lq.2 • b lq.1 lq.2 := by
      rw [smul_smul, pow_sub_mul_pow _ (hle _ _)]
    show f lq.1 ^ n₀ • b lq.1 lq.2 ∈ B.lat i
    rw [this]
    exact chartBundle_pow_smul_mem B (hf _) _ (hn _ _)
  · have hco : ∀ l, ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing R x i) ∧
        e = ∑ q, a q • b l q := fun l => (hiff l e).1 ⟨0, by simpa using he⟩
    choose a ha he' using hco
    choose m hm using ha
    set M := Finset.univ.sup fun lq : Fin k × Fin r => m lq.1 lq.2 with hM
    have hleM : ∀ l q, m l q ≤ M := fun l q =>
      Finset.le_sup (f := fun lq : Fin k × Fin r => m lq.1 lq.2) (Finset.mem_univ (l, q))
    have hfa : ∀ l q, f l ^ M * a l q ∈ chartRing R x i := fun l q => by
      rw [← pow_sub_mul_pow _ (hleM l q), mul_assoc]
      exact mul_mem (pow_mem (hf l) _) (hm l q)
    obtain ⟨d, hd, hd1⟩ := exists_sum_mul_pow_eq_one (chartRing R x i) f c hf hc hsum (M + n₀)
    refine ⟨fun lq => d lq.1 * (f lq.1 ^ M * a lq.1 lq.2), fun lq => mul_mem (hd _) (hfa _ _), ?_⟩
    rw [Fintype.sum_prod_type]
    calc e = (∑ l, d l * f l ^ (M + n₀)) • e := by rw [hd1, one_smul]
      _ = ∑ l, d l • (f l ^ (M + n₀) • e) := by
        rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun l _ => by rw [mul_smul]
      _ = ∑ l, ∑ q, (d l * (f l ^ M * a l q)) • f l ^ n₀ • b l q := by
        refine Finset.sum_congr rfl fun l _ => ?_
        conv_lhs => rw [he' l]
        rw [Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [smul_smul]
        congr 1
        ring
end GroundTheory.Heights₂.Heights.Model
