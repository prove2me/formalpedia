-- Prove2me | solution 1 for SparseLpLq.SmallP.Supplement.theorem_c_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:40:41.328805+00:00
-- url     : https://prove2.me/submissions/8437cd64-f1b4-4c29-b549-2c97d0015383

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting
import Definitions.Def_SparseLpLq_SmallP_Supplement_Penalty

open scoped ENNReal Matrix Topology

open SparseLpLq
open SparseLpLq.SmallP
open SparseLpLq.SmallP.Supplement

open SparseLpLq.SmallP
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (xt : Fin n → ℝ) (hxt : xt ∈ FEA A b σ 1) (ε : ℝ) (hε : 0 < ε)
    (c : ℝ) (hc : 0 < c)
    (hcC3 : ∀ x : Fin n → ℝ, distFEA A b σ x ≤ c * max (qNorm 1 (A *ᵥ x - b) - σ) 0)
    (lam : ℝ) (hlam : c * ((n : ℝ) ^ (p / 2 - 1) * ε) ^ (-1 / p) * lpObj p xt ≤ lam)
    (xlam : Fin n → ℝ) (hxlam : ∀ y : Fin n → ℝ, Fpen A b σ p lam xlam ≤ Fpen A b σ p lam y) :
    (∃ y, IsProjFEA A b σ xlam y) ∧
      ∀ y, IsProjFEA A b σ xlam y → IsEpsMin14 A b σ p ε y := by
        obtain ⟨hp0, hp1⟩ := hp
        have hpne : p ≠ 0 := hp0.ne'
        have hlp : ∀ x : Fin n → ℝ, lpObj p x = ∑ i, |x i| ^ p := fun x => by
          simp [lpObj, hpne]
        have hlpnn : ∀ x : Fin n → ℝ, 0 ≤ lpObj p x := fun x => by
          rw [hlp]; exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
        have hFfeas : ∀ z ∈ FEA A b σ 1, Fpen A b σ p lam z = lpObj p z := by
          intro z hz
          have : qNorm 1 (A *ᵥ z - b) - σ ≤ 0 := by simp only [FEA, Set.mem_setOf_eq] at hz; linarith
          simp [Fpen, max_eq_right this]
        -- closedness of the image set
        set S : Set (EuclideanSpace ℝ (Fin n)) :=
          (fun y : Fin n → ℝ => (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))) '' FEA A b σ 1 with hS
        have hS' : S = (fun v : EuclideanSpace ℝ (Fin n) => WithLp.ofLp v) ⁻¹' FEA A b σ 1 := by
          ext v
          constructor
          · rintro ⟨y, hy, rfl⟩; simpa using hy
          · intro hv; exact ⟨WithLp.ofLp v, hv, by simp⟩
        have hFEAclosed : IsClosed (FEA A b σ 1) := by
          apply isClosed_le _ continuous_const
          unfold qNorm
          exact continuous_norm.comp ((PiLp.continuous_toLp 1 _).comp
            ((Continuous.matrix_mulVec continuous_const continuous_id).sub continuous_const))
        have hSclosed : IsClosed S := by
          rw [hS']; exact hFEAclosed.preimage (PiLp.continuous_ofLp 2 _)
        have hSne : S.Nonempty := hfeas.image _
        have hq2 : ∀ u v : Fin n → ℝ, qNorm 2 (u - v) =
            dist (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 v) := by
          intro u v
          rw [dist_eq_norm, ← WithLp.toLp_sub]; rfl
        obtain ⟨w, hwS, hw⟩ := hSclosed.exists_infDist_eq_dist hSne (WithLp.toLp 2 xlam)
        obtain ⟨y0, hy0, rfl⟩ := hwS
        have hproj0 : IsProjFEA A b σ xlam y0 := by
          refine ⟨hy0, fun z hz => ?_⟩
          rw [hq2, hq2, ← hw]
          exact Metric.infDist_le_dist_of_mem ⟨z, hz, rfl⟩
        refine ⟨⟨y0, hproj0⟩, ?_⟩
        rintro y ⟨hy, hymin⟩
        refine ⟨hy, fun z hz => ?_⟩
        -- positivity of lpObj xt
        have hLpos : 0 < lpObj p xt := by
          rcases (hlpnn xt).lt_or_eq with h | h
          · exact h
          exfalso
          rw [hlp] at h
          have h0 : ∀ i, xt i = 0 := by
            intro i
            have := (Finset.sum_eq_zero_iff_of_nonneg
              (fun i _ => Real.rpow_nonneg (abs_nonneg (xt i)) p)).1 h.symm i (Finset.mem_univ _)
            rw [Real.rpow_eq_zero (abs_nonneg _) hpne] at this
            exact abs_eq_zero.1 this
          have hx0 : xt = 0 := funext h0
          have : qNorm 1 (A *ᵥ xt - b) = qNorm 1 b := by
            rw [hx0]; unfold qNorm; simp [WithLp.toLp_neg]
          simp only [FEA, Set.mem_setOf_eq] at hxt
          linarith
        have hnpos : (0 : ℝ) < n := by
          rcases Nat.eq_zero_or_pos n with h | h
          · subst h; simp [hlp] at hLpos
          · exact_mod_cast h
        set K : ℝ := (n : ℝ) ^ (p / 2 - 1) * ε with hK
        have hKpos : 0 < K := mul_pos (Real.rpow_pos_of_pos hnpos _) hε
        have hlampos : 0 < lam :=
          lt_of_lt_of_le (mul_pos (mul_pos hc (Real.rpow_pos_of_pos hKpos _)) hLpos) hlam
        set M : ℝ := max (qNorm 1 (A *ᵥ xlam - b) - σ) 0 with hM
        have hM0 : 0 ≤ M := le_max_right _ _
        have hlamM : lam * M ≤ lpObj p xt := by
          have h1 := hxlam xt
          rw [hFfeas xt hxt] at h1
          have h2 := hlpnn xlam
          simp only [Fpen] at h1
          linarith
        set d : ℝ := qNorm 2 (xlam - y) with hd
        have hd0 : 0 ≤ d := norm_nonneg _
        have hddist : d ≤ distFEA A b σ xlam := by
          have := hymin y0 hy0
          rw [hq2 xlam y0, ← hw] at this
          exact this
        have hdcM : d ≤ c * M := hddist.trans (hcC3 xlam)
        have hKK : K ^ (-1 / p) * K ^ (1 / p) = 1 := by
          rw [neg_div, Real.rpow_neg hKpos.le]
          exact inv_mul_cancel₀ (Real.rpow_pos_of_pos hKpos _).ne'
        have hcM : c * M ≤ K ^ (1 / p) := by
          have hK1 : 0 < K ^ (1 / p) := Real.rpow_pos_of_pos hKpos _
          have h3 : c * lpObj p xt ≤ lam * K ^ (1 / p) := by
            have := mul_le_mul_of_nonneg_right hlam hK1.le
            calc c * lpObj p xt = c * K ^ (-1 / p) * lpObj p xt * K ^ (1 / p) := by
                  rw [mul_assoc c, mul_comm (K ^ (-1/p)) (lpObj p xt), mul_assoc, mul_assoc, hKK,
                    mul_one]
              _ ≤ lam * K ^ (1 / p) := this
          have h4 : lam * (c * M) ≤ lam * K ^ (1 / p) := by
            calc lam * (c * M) = c * (lam * M) := by ring
              _ ≤ c * lpObj p xt := mul_le_mul_of_nonneg_left hlamM hc.le
              _ ≤ _ := h3
          exact le_of_mul_le_mul_left h4 hlampos
        have hdK : d ^ p ≤ K := by
          have := Real.rpow_le_rpow hd0 (hdcM.trans hcM) hp0.le
          rwa [← Real.rpow_mul hKpos.le, one_div_mul_cancel hpne, Real.rpow_one] at this
        -- Hölder
        have hHold : ∑ i, |xlam i - y i| ^ p ≤ (n : ℝ) ^ (1 - p / 2) * d ^ p := by
          have hpq : (p / 2)⁻¹.HolderConjugate (1 - p / 2)⁻¹ :=
            Real.HolderConjugate.inv_one_sub_inv (by linarith) (by linarith)
          have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hpq
            (f := fun i => |xlam i - y i| ^ p) (g := fun _ => (1 : ℝ))
            (fun i _ => Real.rpow_nonneg (abs_nonneg _) _) (fun _ _ => zero_le_one)
          simp only [mul_one, Real.one_rpow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, one_div, inv_inv] at h
          have h2 : ∀ i, (|xlam i - y i| ^ p) ^ (p / 2)⁻¹ = (xlam i - y i) ^ 2 := by
            intro i
            rw [← Real.rpow_mul (abs_nonneg _)]
            have : p * (p / 2)⁻¹ = (2 : ℕ) := by field_simp; norm_num
            rw [this, Real.rpow_natCast, sq_abs]
          simp only [h2] at h
          have hd2 : d ^ p = (∑ i, (xlam i - y i) ^ 2) ^ (p / 2) := by
            rw [hd]
            unfold qNorm
            rw [EuclideanSpace.norm_eq, Real.sqrt_eq_rpow, ← Real.rpow_mul
              (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
            congr 1
            · simp
            · ring
          rw [hd2]
          linarith [h]
        -- subadditivity
        have hsub : lpObj p y ≤ lpObj p xlam + ∑ i, |xlam i - y i| ^ p := by
          rw [hlp, hlp, ← Finset.sum_add_distrib]
          refine Finset.sum_le_sum (fun i _ => ?_)
          calc |y i| ^ p ≤ (|xlam i| + |xlam i - y i|) ^ p := by
                apply Real.rpow_le_rpow (abs_nonneg _) _ hp0.le
                calc |y i| = |xlam i - (xlam i - y i)| := by ring_nf
                  _ ≤ |xlam i| + |xlam i - y i| := abs_sub _ _
            _ ≤ _ := Real.rpow_add_le_add_rpow (abs_nonneg _) (abs_nonneg _) hp0.le hp1.le
        have hxz : lpObj p xlam ≤ lpObj p z := by
          have h1 := hxlam z
          rw [hFfeas z hz] at h1
          have h2 : 0 ≤ lam * M := mul_nonneg hlampos.le hM0
          simp only [Fpen] at h1
          linarith
        have hnK : (n : ℝ) ^ (1 - p / 2) * K = ε := by
          rw [hK, ← mul_assoc, ← Real.rpow_add hnpos]; simp
        have := mul_le_mul_of_nonneg_left hdK (Real.rpow_nonneg hnpos.le (1 - p / 2))
        linarith
