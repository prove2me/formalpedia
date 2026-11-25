-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.denseRange_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:58:04.078593+00:00
-- url     : https://prove2.me/submissions/e9e07bd9-c7db-458c-b4e2-e895d70a091e

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Kloc
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_mem_range_of_aeval_rat_eq_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
private theorem exists_root_norm_sub_pow_le_eval {K : Type*} [NormedField K] [IsAlgClosed K] (n : ℕ) :
    ∀ G : Polynomial K, G.Monic → G.natDegree = n + 1 → ∀ b : K,
      ∃ β, G.IsRoot β ∧ ‖b - β‖ ^ (n + 1) ≤ ‖G.eval b‖ := by
  induction n with
  | zero =>
    intro G hG hd b
    have hdeg : G.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hG.ne_zero, hd]
      simp
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root G hdeg
    refine ⟨α, hα, ?_⟩
    have hQ := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hα
    have hQm : (G /ₘ (Polynomial.X - Polynomial.C α)).Monic :=
      (Polynomial.monic_X_sub_C α).of_mul_monic_left (by rw [hQ]; exact hG)
    have hQd : (G /ₘ (Polynomial.X - Polynomial.C α)).natDegree = 0 := by
      have h := (Polynomial.monic_X_sub_C α).natDegree_mul hQm
      rw [hQ, hd, Polynomial.natDegree_X_sub_C] at h
      omega
    have hQ1 : G /ₘ (Polynomial.X - Polynomial.C α) = 1 := by
      first
        | exact Polynomial.eq_one_of_monic_natDegree_zero hQm hQd
        | exact hQm.natDegree_eq_zero.mp hQd
        | exact (Polynomial.Monic.natDegree_eq_zero_iff_eq_one hQm).mp hQd
    have he : G.eval b = (b - α) * (G /ₘ (Polynomial.X - Polynomial.C α)).eval b := by
      conv_lhs => rw [← hQ]
      rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [he, hQ1, Polynomial.eval_one, mul_one, pow_one]
  | succ n ih =>
    intro G hG hd b
    have hdeg : G.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hG.ne_zero, hd]
      exact_mod_cast Nat.succ_ne_zero (n + 1)
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root G hdeg
    have hQ := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hα
    have hQm : (G /ₘ (Polynomial.X - Polynomial.C α)).Monic :=
      (Polynomial.monic_X_sub_C α).of_mul_monic_left (by rw [hQ]; exact hG)
    have hQd : (G /ₘ (Polynomial.X - Polynomial.C α)).natDegree = n + 1 := by
      have h := (Polynomial.monic_X_sub_C α).natDegree_mul hQm
      rw [hQ, hd, Polynomial.natDegree_X_sub_C] at h
      omega
    have he : G.eval b = (b - α) * (G /ₘ (Polynomial.X - Polynomial.C α)).eval b := by
      conv_lhs => rw [← hQ]
      rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    obtain ⟨β, hβ, hb⟩ := ih _ hQm hQd b
    have hβG : G.IsRoot β := by
      rw [Polynomial.IsRoot.def] at hβ ⊢
      rw [← hQ, Polynomial.eval_mul, hβ, mul_zero]
    have hGb : ‖G.eval b‖ = ‖b - α‖ * ‖(G /ₘ (Polynomial.X - Polynomial.C α)).eval b‖ := by
      rw [he, norm_mul]
    rcases le_total ‖b - α‖ ‖b - β‖ with h | h
    · refine ⟨α, hα, ?_⟩
      rw [hGb, pow_succ']
      exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) h _).trans hb) (norm_nonneg _)
    · refine ⟨β, hβG, ?_⟩
      rw [hGb, pow_succ']
      exact mul_le_mul h hb (by positivity) (norm_nonneg _)
end ReciprocityTheory.Neutral.Cmp
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) [IsAlgClosed Ω] : DenseRange ι := by
  classical
  rw [Metric.denseRange_iff]
  intro b ε hε
  have hint : IsIntegral ℚ_[p] b := (Algebra.IsAlgebraic.isAlgebraic b).isIntegral
  have hfm : (minpoly ℚ_[p] b).Monic := minpoly.monic hint
  have hpos : 0 < (minpoly ℚ_[p] b).natDegree := minpoly.natDegree_pos hint
  obtain ⟨n, hn⟩ : ∃ n, (minpoly ℚ_[p] b).natDegree = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hFb : ((minpoly ℚ_[p] b).map (algebraMap ℚ_[p] (PadicAlgCl p))).eval b = 0 := by
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ_[p] b
  set f := minpoly ℚ_[p] b with hf
  set M : ℝ := max 1 ‖b‖ with hMdef
  have hM : 1 ≤ M := le_max_left _ _
  have hbM : ‖b‖ ≤ M := le_max_right _ _
  have hMp : 0 < M := by linarith
  set δ : ℝ := ε ^ (n + 1) / (2 * ((n : ℝ) + 2) * M ^ (n + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  choose q hq using fun i : ℕ => Padic.rat_dense p (f.coeff i) hδ
  set s : Polynomial ℚ := ∑ i ∈ Finset.range (n + 1), Polynomial.C (q i) * Polynomial.X ^ i with hs
  have hsdeg : s.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [hs, Finset.sum_range]
    exact Polynomial.degree_sum_fin_lt _
  set g : Polynomial ℚ := Polynomial.X ^ (n + 1) + s with hg
  have hgm : g.Monic := Polynomial.monic_X_pow_add hsdeg
  have hgn : g.natDegree = n + 1 := by
    rw [hg, Polynomial.natDegree_add_eq_left_of_degree_lt (by rw [Polynomial.degree_X_pow]; exact hsdeg),
      Polynomial.natDegree_X_pow]
  set G := g.map (algebraMap ℚ (PadicAlgCl p)) with hG
  set F := f.map (algebraMap ℚ_[p] (PadicAlgCl p)) with hF
  have hGm : G.Monic := hgm.map _
  have hGn : G.natDegree = n + 1 := by rw [hG, Polynomial.natDegree_map]; exact hgn
  have hDn : (G - F).natDegree < n + 2 := by
    refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) ?_
    rw [hGn, hF, Polynomial.natDegree_map, hn, max_self]
    omega
  have hGb : G.eval b = ∑ i ∈ Finset.range (n + 2), (G - F).coeff i * b ^ i := by
    rw [← Polynomial.eval_eq_sum_range' hDn, Polynomial.eval_sub, hFb, sub_zero]
  have hterm : ∀ i ∈ Finset.range (n + 2), ‖(G - F).coeff i * b ^ i‖ ≤ δ * M ^ (n + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow]
    have hbi : ‖b‖ ^ i ≤ M ^ (n + 1) :=
      (pow_le_pow_left₀ (norm_nonneg _) hbM i).trans (pow_le_pow_right₀ hM (by omega))
    have hc : ‖(G - F).coeff i‖ ≤ δ := by
      rw [Polynomial.coeff_sub, hG, hF, Polynomial.coeff_map, Polynomial.coeff_map]
      rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
      · have hgc : g.coeff i = q i := by
          rw [hg, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), zero_add, hs,
            Polynomial.finset_sum_coeff]
          simp only [Polynomial.coeff_C_mul_X_pow]
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hi')]
        rw [hgc, eq_ratCast (algebraMap ℚ (PadicAlgCl p)), ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)),
          ← map_sub, PadicAlgCl.norm_extends, norm_sub_rev]
        exact (hq i).le
      · have hi2 : i = n + 1 := by omega
        have hg1 : g.coeff i = 1 := by
          have h := hgm.coeff_natDegree
          rw [hgn] at h
          rw [hi2, h]
        have hf1 : f.coeff i = 1 := by
          have h := hfm.coeff_natDegree
          rw [hn] at h
          rw [hi2, h]
        rw [hg1, hf1, map_one, map_one, sub_self, norm_zero]
        exact hδ.le
    exact mul_le_mul hc hbi (by positivity) hδ.le
  have hGlt : ‖G.eval b‖ < ε ^ (n + 1) := by
    rw [hGb]
    refine lt_of_le_of_lt (norm_sum_le _ _) ?_
    refine lt_of_le_of_lt (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have e : ((n + 2 : ℕ) : ℝ) * (δ * M ^ (n + 1)) = ε ^ (n + 1) / 2 := by
      rw [hδdef]
      push_cast
      field_simp
    rw [e]
    have : 0 < ε ^ (n + 1) := by positivity
    linarith
  obtain ⟨β, hβ, hβb⟩ := exists_root_norm_sub_pow_le_eval n G hGm hGn b
  have hβε : ‖b - β‖ < ε := lt_of_pow_lt_pow_left₀ (n + 1) hε.le (lt_of_le_of_lt hβb hGlt)
  have hβr : β ∈ ι.range := mem_range_of_aeval_rat_eq_zero ι hgm.ne_zero (by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact hβ)
  obtain ⟨y, hy⟩ := RingHom.mem_range.mp hβr
  refine ⟨y, ?_⟩
  rw [dist_eq_norm, hy]
  exact hβε
end ReciprocityTheory.Neutral.Cmp
