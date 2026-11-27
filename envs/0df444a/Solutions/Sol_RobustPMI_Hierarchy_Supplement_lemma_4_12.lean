-- Prove2me | solution 1 for RobustPMI.Hierarchy.Supplement.lemma_4_12
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:25:02.263294+00:00
-- url     : https://prove2.me/submissions/8c378842-9ab2-4887-bf9e-76314c186c10

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Definitions.Def_RobustPMI_Hierarchy_Supplement_Model

open RobustPMI
open RobustPMI.Hierarchy
open RobustPMI.Hierarchy.Supplement

open MvPolynomial Matrix Filter Topology

/-- Lemma 4.12 (p. 22): under Assumption 4 (i), for every `k ≥ max{⌈k_x/2⌉, ⌈k_y/2⌉}` and every
`S ∈ 𝓜^m_k(G)` there is `λ ∈ ℝ` with `f(y) − λ − 𝓛_S(P(y, x)) ∈ 𝒬°_k(Θ)`, the interior of
`𝒬_k(Θ)` in the space `ℝ[y]_{2k}`. -/
theorem solution {ℓ n m q s : ℕ} (f : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP : P.IsSymm) (hG : G.IsSymm) (h4 : Assumption4i θ)
    (k : ℕ) (hkx : (kx P G + 1) / 2 ≤ k) (hky : (ky f θ P + 1) / 2 ≤ k)
    (S : MatSeq (Fin n) (Fin m)) (hS : S ∈ MM k G) :
    ∃ lam : ℝ, InInteriorQTheta k θ (f - C lam - rieszP S P) := by
      classical
      obtain ⟨hs, b, hb0, hθ0⟩ := h4
      set i0 : Fin s := ⟨0, hs⟩ with hi0
      set Q := QTheta k θ with hQdef
      have hdegMat : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (A : Matrix ι κ (MvPolynomial (Fin ℓ) ℝ)) (d : ℕ),
          (∀ i j, (A i j).totalDegree ≤ d) → degMat A ≤ d := by
        intro ι κ _ _ A d h
        exact Finset.sup_le fun p _ => h p.1 p.2
      have hdegMat' : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (A : Matrix ι κ (MvPolynomial (Fin ℓ) ℝ)) i j,
          (A i j).totalDegree ≤ degMat A := by
        intro ι κ _ _ A i j
        exact Finset.le_sup (f := fun p : ι × κ => (A p.1 p.2).totalDegree) (Finset.mem_univ (i, j))
      have hSOSadd : ∀ {ι : Type} [Fintype ι] (A B : Matrix ι ι (MvPolynomial (Fin ℓ) ℝ)),
          IsSOSMat A → IsSOSMat B → IsSOSMat (A + B) := by
        intro ι _ A B ⟨l1, T1, h1⟩ ⟨l2, T2, h2⟩
        refine ⟨l1 + l2, Matrix.of fun r j => Fin.addCases (fun r1 => T1 r1 j) (fun r2 => T2 r2 j) r, ?_⟩
        subst h1 h2
        ext i j
        simp [Matrix.mul_apply, Fin.sum_univ_add]
      have hSOSsmul : ∀ {ι : Type} [Fintype ι] (c : ℝ) (A : Matrix ι ι (MvPolynomial (Fin ℓ) ℝ)),
          0 ≤ c → IsSOSMat A → IsSOSMat (c • A) := by
        intro ι _ c A hc ⟨l, T, h⟩
        refine ⟨l, Real.sqrt c • T, ?_⟩
        subst h
        rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hc]
      have hSOS0 : ∀ {ι : Type} [Fintype ι], IsSOSMat (0 : Matrix ι ι (MvPolynomial (Fin ℓ) ℝ)) := by
        intro ι _
        exact ⟨0, 0, by simp⟩
      have hpairAdd : ∀ (A B : Matrix (Fin 1 × Fin s) (Fin 1 × Fin s) (MvPolynomial (Fin ℓ) ℝ)),
          pairM (A + B) (Matrix.diagonal θ) = pairM A (Matrix.diagonal θ) + pairM B (Matrix.diagonal θ) := by
        intro A B
        ext i j
        simp [pairM, trBlocks, Matrix.add_mul, Finset.sum_add_distrib]
      have hpairSmul : ∀ (c : ℝ) (A : Matrix (Fin 1 × Fin s) (Fin 1 × Fin s) (MvPolynomial (Fin ℓ) ℝ)),
          pairM (c • A) (Matrix.diagonal θ) = c • pairM A (Matrix.diagonal θ) := by
        intro c A
        ext i j
        simp [pairM, trBlocks, Finset.smul_sum]
      have hadd : ∀ a b, a ∈ Q → b ∈ Q → a + b ∈ Q := by
        rintro a b ⟨A0, A1, hA0, hA1, dA0, dA1, hA⟩ ⟨B0, B1, hB0, hB1, dB0, dB1, hB⟩
        refine ⟨A0 + B0, A1 + B1, hSOSadd _ _ hA0 hB0, hSOSadd _ _ hA1 hB1, ?_, ?_, ?_⟩
        · refine hdegMat _ _ fun i j => ?_
          exact (totalDegree_add _ _).trans (max_le ((hdegMat' _ i j).trans dA0) ((hdegMat' _ i j).trans dB0))
        · rw [hpairAdd]
          refine hdegMat _ _ fun i j => ?_
          exact (totalDegree_add _ _).trans (max_le ((hdegMat' _ i j).trans dA1) ((hdegMat' _ i j).trans dB1))
        · rw [hpairAdd]
          ext i j
          have h1 := congrFun (congrFun hA i) j
          have h2 := congrFun (congrFun hB i) j
          simp only [Matrix.of_apply, Matrix.add_apply] at h1 h2 ⊢
          rw [h1, h2]; ring
      have hsmul : ∀ (c : ℝ) a, 0 ≤ c → a ∈ Q → c • a ∈ Q := by
        rintro c a hc ⟨A0, A1, hA0, hA1, dA0, dA1, hA⟩
        refine ⟨c • A0, c • A1, hSOSsmul _ _ hc hA0, hSOSsmul _ _ hc hA1, ?_, ?_, ?_⟩
        · refine hdegMat _ _ fun i j => ?_
          exact (totalDegree_smul_le _ _).trans ((hdegMat' _ i j).trans dA0)
        · rw [hpairSmul]
          refine hdegMat _ _ fun i j => ?_
          exact (totalDegree_smul_le _ _).trans ((hdegMat' _ i j).trans dA1)
        · rw [hpairSmul]
          ext i j
          have h1 := congrFun (congrFun hA i) j
          simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply] at h1 ⊢
          rw [h1, smul_add]
      have hsq : ∀ p : MvPolynomial (Fin ℓ) ℝ, p.totalDegree ≤ k → p ^ 2 ∈ Q := by
        intro p hp
        refine ⟨Matrix.of fun _ _ => p ^ 2, 0, ⟨1, Matrix.of fun _ _ => p, ?_⟩, hSOS0, ?_, ?_, ?_⟩
        · ext i j; simp [Matrix.mul_apply, sq]
        · refine hdegMat _ _ fun i j => ?_
          simp only [Matrix.of_apply]
          exact (totalDegree_pow _ _).trans (by omega)
        · refine hdegMat _ _ fun i j => ?_
          simp [pairM, trBlocks]
        · ext i j; simp [pairM, trBlocks]
      have hθ : ∀ p : MvPolynomial (Fin ℓ) ℝ, p.totalDegree + 1 ≤ k → p ^ 2 * θ i0 ∈ Q := by
        intro p hp
        let T : Matrix (Fin 1) (Fin 1 × Fin s) (MvPolynomial (Fin ℓ) ℝ) :=
          Matrix.of fun _ c => if c.2 = i0 then p else 0
        have hpair : pairM (Tᵀ * T) (Matrix.diagonal θ) = Matrix.of fun _ _ => p ^ 2 * θ i0 := by
          ext i j
          fin_cases i; fin_cases j
          simp [T, pairM, trBlocks, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
            Matrix.diagonal_apply, Fintype.sum_prod_type, sq]
        have hdθ : (θ i0).totalDegree ≤ 2 := by
          rw [hθ0]
          refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_C]; norm_num) ?_)
          refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
          exact (totalDegree_pow _ _).trans (by simp)
        refine ⟨0, Tᵀ * T, hSOS0, ⟨1, T, rfl⟩, ?_, ?_, ?_⟩
        · exact hdegMat _ _ fun i j => by simp
        · rw [hpair]
          refine hdegMat _ _ fun i j => ?_
          simp only [Matrix.of_apply]
          refine (totalDegree_mul _ _).trans ?_
          have := totalDegree_pow p 2
          omega
        · rw [hpair]; ext i j; simp
      have hzero : (0 : MvPolynomial (Fin ℓ) ℝ) ∈ Q := by
        simpa using hsq 0 (by simp)
      have hconst : ∀ c : ℝ, 0 ≤ c → C c ∈ Q := by
        intro c hc
        have := hsq (C (Real.sqrt c)) (by simp)
        rwa [← map_pow, Real.sq_sqrt hc] at this
      have hsum : ∀ (ι : Type) (t : Finset ι) (g : ι → MvPolynomial (Fin ℓ) ℝ),
          (∀ i ∈ t, g i ∈ Q) → ∑ i ∈ t, g i ∈ Q := by
        intro ι t g hg
        exact Finset.sum_induction _ (· ∈ Q) hadd hzero hg
      have hdegmono : ∀ β : Fin ℓ →₀ ℕ, (monomial β (1 : ℝ)).totalDegree = β.degree := by
        intro β
        rw [totalDegree_monomial _ one_ne_zero, Finsupp.degree_apply]
        rfl
      have hmono : ∀ N : ℕ, ∀ β : Fin ℓ →₀ ℕ, β.degree = N → N ≤ k →
          C ((b ^ 2) ^ N) - (monomial β (1 : ℝ)) ^ 2 ∈ Q := by
        intro N
        induction N with
        | zero =>
          intro β hβ _
          rw [Finsupp.degree_eq_zero_iff] at hβ
          subst hβ
          simpa using hzero
        | succ N ih =>
          intro β hβ hN
          have hβ0 : β ≠ 0 := by
            rintro rfl; simp at hβ
          obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hβ0
          have hle : Finsupp.single i 1 ≤ β := by
            rw [Finsupp.single_le_iff]; simp at hi; omega
          set β' := β - Finsupp.single i 1 with hβ'
          have hβeq : β = β' + Finsupp.single i 1 := (tsub_add_cancel_of_le hle).symm
          have hdeg' : β'.degree = N := by
            have := congrArg Finsupp.degree hβeq
            rw [map_add, Finsupp.degree_single] at this
            omega
          set mm := monomial β' (1 : ℝ) with hmm
          have hmβ : monomial β (1 : ℝ) = mm * X i := by
            rw [hβeq, hmm, X, monomial_mul, one_mul]
          have hdm : mm.totalDegree = N := by rw [hmm, hdegmono, hdeg']
          have hid : C ((b ^ 2) ^ (N + 1)) - (monomial β (1 : ℝ)) ^ 2 =
              (b ^ 2) • (C ((b ^ 2) ^ N) - mm ^ 2) + mm ^ 2 * θ i0 +
                ∑ j ∈ Finset.univ.erase i, (mm * X j) ^ 2 := by
            rw [hθ0, hmβ, smul_eq_C_mul]
            have hs := Finset.add_sum_erase Finset.univ (fun j => (mm * X j) ^ 2) (Finset.mem_univ i)
            have hs2 : ∑ j, (mm * X j) ^ 2 = mm ^ 2 * ∑ j, X j ^ 2 := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
            simp only [map_pow] at hs hs2 ⊢
            linear_combination -hs - hs2
          rw [hid]
          refine hadd _ _ (hadd _ _ (hsmul _ _ (by positivity) (ih β' hdeg' (by omega)))
            (hθ mm (by omega))) (hsum _ _ _ fun j _ => hsq _ ?_)
          refine (totalDegree_mul _ _).trans ?_
          rw [hdm, totalDegree_X]; omega

      set B : ℝ := (1 + b ^ 2) ^ k with hBdef
      have hB0 : 0 ≤ B := by positivity
      have hBm : ∀ β : Fin ℓ →₀ ℕ, β.degree ≤ k → C B - (monomial β (1 : ℝ)) ^ 2 ∈ Q := by
        intro β hβ
        have hle : (b ^ 2) ^ β.degree ≤ B := by
          calc (b ^ 2) ^ β.degree ≤ (1 + b ^ 2) ^ β.degree :=
                pow_le_pow_left₀ (by positivity) (by linarith) _
            _ ≤ (1 + b ^ 2) ^ k := pow_le_pow_right₀ (by nlinarith [sq_nonneg b]) hβ
        have := hadd _ _ (hconst (B - (b ^ 2) ^ β.degree) (by linarith)) (hmono _ β rfl hβ)
        convert this using 1
        rw [map_sub]; ring
      have hpm : ∀ α : Fin ℓ →₀ ℕ, α.degree ≤ 2 * k → ∀ c : ℝ,
          C (B * |c|) + monomial α c ∈ Q := by
        intro α hα c
        obtain ⟨β, hβα, hβd⟩ := Finsupp.exists_le_degree_eq α (min k α.degree) (min_le_right _ _)
        set γ := α - β with hγ
        have hαeq : α = β + γ := (add_tsub_cancel_of_le hβα).symm
        have hγd : γ.degree ≤ k := by
          have := congrArg Finsupp.degree hαeq
          rw [map_add] at this
          omega
        have hβk : β.degree ≤ k := by omega
        have hkey : ∀ σ : ℝ, σ * σ = 1 →
            C B + C σ * (monomial β (1 : ℝ) * monomial γ (1 : ℝ)) ∈ Q := by
          intro σ hσ
          have hσ' : C σ * C σ = (1 : MvPolynomial (Fin ℓ) ℝ) := by rw [← map_mul, hσ, map_one]
          have h1 := hsmul (1 / 2) _ (by norm_num)
            (hsq (monomial β (1 : ℝ) + C σ * monomial γ (1 : ℝ)) ?_)
          · have h2 := hsmul (1 / 2) _ (by norm_num) (hBm β hβk)
            have h3 := hsmul (1 / 2) _ (by norm_num) (hBm γ hγd)
            have := hadd _ _ (hadd _ _ h1 h2) h3
            convert this using 1
            simp only [smul_eq_C_mul]
            have hhalf : (C (1 / 2 : ℝ) : MvPolynomial (Fin ℓ) ℝ) + C (1 / 2 : ℝ) = 1 := by
              rw [← map_add]; norm_num
            linear_combination (-(C B + C σ * (monomial β (1 : ℝ) * monomial γ (1 : ℝ)))) * hhalf -
              (C (1 / 2 : ℝ) * monomial γ (1 : ℝ) ^ 2) * hσ'
          · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
            · rw [hdegmono]; exact hβk
            · refine (totalDegree_mul _ _).trans ?_
              rw [totalDegree_C, hdegmono]; omega
        have hmα : monomial α c = C c * (monomial β (1 : ℝ) * monomial γ (1 : ℝ)) := by
          rw [monomial_mul, one_mul, ← hαeq, C_mul_monomial, mul_one]
        rcases le_or_gt 0 c with hc | hc
        · have := hsmul c _ hc (hkey 1 (by norm_num))
          convert this using 1
          rw [hmα, smul_eq_C_mul, abs_of_nonneg hc, C_mul, C_1]; ring
        · have := hsmul (-c) _ (by linarith) (hkey (-1) (by norm_num))
          convert this using 1
          rw [hmα, smul_eq_C_mul, abs_of_neg hc, C_mul, C_neg, C_neg, C_1]; ring
      have hmem_monos : ∀ α : Fin ℓ →₀ ℕ, α ∈ monos (σ := Fin ℓ) (2 * k) ↔ α.degree ≤ 2 * k := by
        intro α
        simp only [monos, Finset.mem_filter, Finset.mem_Iic, and_iff_right_iff_imp]
        intro h
        refine Finsupp.le_def.2 fun i => ?_
        simpa using (Finsupp.le_degree i α).trans h
      have hL : ∀ (c : monos (σ := Fin ℓ) (2 * k) → ℝ) (t : ℝ), B * ∑ α, |c α| ≤ t →
          C t + ∑ α, monomial α.1 (c α) ∈ Q := by
        intro c t ht
        have h1 := hconst (t - B * ∑ α, |c α|) (by linarith)
        have h2 := hsum _ Finset.univ (fun α => C (B * |c α|) + monomial α.1 (c α))
          fun α _ => hpm α.1 ((hmem_monos α.1).1 α.2) (c α)
        have := hadd _ _ h1 h2
        convert this using 1
        rw [Finset.sum_add_distrib, ← map_sum, Finset.mul_sum, map_sub, map_sum]; ring
      have hrecon : ∀ p : MvPolynomial (Fin ℓ) ℝ, p.totalDegree ≤ 2 * k →
          ∑ α : monos (σ := Fin ℓ) (2 * k), monomial α.1 (coeff α.1 p) = p := by
        intro p hp
        rw [Finset.sum_coe_sort (monos (σ := Fin ℓ) (2 * k)) (fun α => monomial α (coeff α p))]
        conv_rhs => rw [p.as_sum]
        symm
        apply Finset.sum_subset
        · intro α hα
          rw [hmem_monos]
          exact (le_totalDegree hα).trans hp
        · intro α _ hα
          rw [notMem_support_iff] at hα
          rw [hα, map_zero]

      have hky2 : ky f θ P ≤ 2 * k := by omega
      have hsumdeg : ∀ p : MvPolynomial (Fin ℓ ⊕ Fin n) ℝ,
          (sumAlgEquiv ℝ (Fin ℓ) (Fin n) p).totalDegree ≤ degY p := by
        intro p
        conv_lhs => rw [p.as_sum]
        rw [map_sum]
        refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun α hα => ?_)
        refine le_trans ?_ (Finset.le_sup (f := fun α : Fin ℓ ⊕ Fin n →₀ ℕ => ∑ j, α (Sum.inl j)) hα)
        rw [monomial_eq, map_mul, map_finsuppProd]
        refine (totalDegree_mul _ _).trans ?_
        rw [sumAlgEquiv_C_inl, totalDegree_C, zero_add]
        refine (totalDegree_finsetProd _ _).trans ?_
        calc ∑ v ∈ α.support, ((sumAlgEquiv ℝ (Fin ℓ) (Fin n)) (X v ^ α v)).totalDegree
            ≤ ∑ v ∈ α.support, α v * Sum.elim (fun _ => 1) (fun _ => 0) v := by
              refine Finset.sum_le_sum fun v _ => ?_
              rw [map_pow]
              refine (totalDegree_pow _ _).trans ?_
              rcases v with j | j
              · simp [sumAlgEquiv_X_inl]
              · simp [sumAlgEquiv_X_inr]
          _ ≤ ∑ v, α v * Sum.elim (fun _ => 1) (fun _ => 0) v :=
              Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          _ = ∑ j, α (Sum.inl j) := by simp [Fintype.sum_sum_type]
      have hRdeg : (rieszP S P).totalDegree ≤ 2 * k := by
        unfold rieszP
        refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun β hβ => ?_)
        refine (totalDegree_monomial_le _ _).trans ?_
        simp only [suppMat, Finset.mem_biUnion, Finset.mem_univ, true_and] at hβ
        obtain ⟨⟨i, j⟩, hij⟩ := hβ
        dsimp only at hij
        have h1 := le_totalDegree hij
        have h2 : ((Py P) i j).totalDegree ≤ degY (P i j) := by
          simp only [Py, Matrix.map_apply]; exact hsumdeg _
        have h3 : degY (P i j) ≤ ky f θ P := by
          unfold ky
          refine le_trans ?_ (le_max_right _ _)
          refine le_trans ?_ (le_max_right _ _)
          exact Finset.le_sup (f := fun p : Fin m × Fin m => degY (P p.1 p.2)) (Finset.mem_univ (i, j))
        have h4 : (β.sum fun _ => id) = β.sum fun _ e => e := rfl
        omega
      have hfdeg : f.totalDegree ≤ 2 * k := le_trans (le_max_left _ _) hky2
      set h0 := f - rieszP S P with hh0
      have hh0deg : h0.totalDegree ≤ 2 * k :=
        (totalDegree_sub _ _).trans (max_le hfdeg hRdeg)
      refine ⟨-(B * ∑ α : monos (σ := Fin ℓ) (2 * k), (|coeff α.1 h0| + 1)), ?_⟩
      set lam := -(B * ∑ α : monos (σ := Fin ℓ) (2 * k), (|coeff α.1 h0| + 1)) with hlam
      have hheq : f - C lam - rieszP S P = h0 - C lam := by rw [hh0]; ring
      rw [hheq]
      have hhdeg : (h0 - C lam).totalDegree ≤ 2 * k :=
        (totalDegree_sub _ _).trans (max_le hh0deg (by simp))
      refine ⟨hhdeg, ?_⟩
      set u := coeffVec (2 * k) (h0 - C lam) with hu
      rw [mem_interior]
      refine ⟨Metric.ball u 1, ?_, Metric.isOpen_ball, Metric.mem_ball_self one_pos⟩
      intro v hv
      rw [Metric.mem_ball, dist_pi_lt_iff one_pos] at hv
      set g := ∑ α : monos (σ := Fin ℓ) (2 * k), monomial α.1 (v α) with hg
      refine ⟨g, ⟨?_, ?_⟩, ?_⟩
      · set c : monos (σ := Fin ℓ) (2 * k) → ℝ := fun α => v α - u α + coeff α.1 h0 with hc
        have hgeq : g = C (-lam) + ∑ α, monomial α.1 (c α) := by
          have e1 := hrecon _ hhdeg
          have e2 := hrecon _ hh0deg
          simp only [hc, map_add, map_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
          rw [e2, hg]
          have e3 : ∑ α : monos (σ := Fin ℓ) (2 * k), monomial α.1 (u α) = h0 - C lam := e1
          rw [e3, map_neg]; ring
        rw [hgeq]
        refine hL c (-lam) ?_
        rw [hlam, neg_neg]
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ => ?_) hB0
        have := hv α
        rw [Real.dist_eq] at this
        calc |c α| ≤ |v α - u α| + |coeff α.1 h0| := abs_add_le _ _
          _ ≤ |coeff α.1 h0| + 1 := by linarith
      · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun α _ => ?_)
        refine (totalDegree_monomial_le _ _).trans ?_
        have := (hmem_monos α.1).1 α.2
        exact this
      · funext α
        simp only [coeffVec, hg, coeff_sum, coeff_monomial]
        rw [Finset.sum_eq_single α]
        · simp
        · intro β _ hβ
          rw [if_neg]
          exact fun h => hβ (Subtype.ext h)
        · simp
