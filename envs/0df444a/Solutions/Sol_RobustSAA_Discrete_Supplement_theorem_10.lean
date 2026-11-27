-- Prove2me | solution 1 for RobustSAA.Discrete.Supplement.theorem_10
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:14:28.582549+00:00
-- url     : https://prove2.me/submissions/b2a0f5d4-288b-4a3a-9a7e-d765f375f4bd

import Mathlib
import Definitions.Def_RobustSAA_Discrete_Supplement_Cones
import Definitions.Def_RobustSAA_Discrete_Supplement_UnivStat

open RobustSAA
open RobustSAA.Discrete
open RobustSAA.Discrete.Supplement

theorem solution (N : ℕ) (hN : 0 < N) :
    IsConvexCone (K_KS N) ∧ IsConvexCone (K_Kuiper N) ∧ IsConvexCone (K_CvM N) ∧
    IsConvexCone (K_Watson N) ∧ IsConvexCone (K_AD N) ∧
    (∀ (Q : ℝ) (ζ : Fin N → ℝ), ksZ ζ ≤ Q ↔ (A_KS N).mulVec ζ - b_KS N Q ∈ K_KS N) ∧
    (∀ (Q : ℝ) (ζ : Fin N → ℝ),
      kuiperZ ζ ≤ Q ↔ (A_KS N).mulVec ζ - b_Kuiper N Q ∈ K_Kuiper N) ∧
    (∀ Q : ℝ, 0 ≤ Q → 1 / (12 * (N : ℝ) ^ 2) ≤ Q ^ 2 → ∀ ζ : Fin N → ℝ,
      cvmZ ζ ≤ Q ↔ (A_CvM N).mulVec ζ - b_CvM N Q ∈ K_CvM N) ∧
    (∀ Q : ℝ, 0 ≤ Q → ∀ ζ : Fin N → ℝ,
      watsonZ ζ ≤ Q ↔ (A_Watson N).mulVec ζ - b_Watson N Q ∈ K_Watson N) ∧
    (∀ Q : ℝ, 0 ≤ Q → ∀ ζ : Fin N → ℝ,
      adZ ζ ≤ ENNReal.ofReal Q ↔ (A_AD N).mulVec ζ - b_AD N Q ∈ K_AD N) := by
        haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
        have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
        -- Kuiper cone characterization
        have kuip : ∀ v : Fin N ⊕ Fin N → ℝ, v ∈ K_Kuiper N ↔ ∀ i j, 0 ≤ v (Sum.inl i) + v (Sum.inr j) := by
          intro v
          simp only [K_Kuiper, Set.mem_setOf_eq]
          constructor
          · intro h i j
            have h1 : (⨅ i : Fin N, v (Sum.inl i)) ≤ v (Sum.inl i) := ciInf_le (Finite.bddBelow_range _) i
            have h2 : (⨅ i : Fin N, v (Sum.inr i)) ≤ v (Sum.inr j) := ciInf_le (Finite.bddBelow_range _) j
            linarith
          · intro h
            obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i : Fin N => v (Sum.inl i))
            obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := fun i : Fin N => v (Sum.inr i))
            rw [← hi, ← hj]; exact h i j
        -- SOC convex cone
        have socCone : ∀ (ι : Type) [Fintype ι], IsConvexCone (soc ι) := by
          intro ι _
          have mink : ∀ x y : ι → ℝ, Real.sqrt (∑ i, (x i + y i) ^ 2) ≤
              Real.sqrt (∑ i, x i ^ 2) + Real.sqrt (∑ i, y i ^ 2) := by
            intro x y
            rw [Real.sqrt_le_left (by positivity)]
            have cs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ x y
            have e1 := Real.sq_sqrt (show 0 ≤ ∑ i, x i ^ 2 by positivity)
            have e2 := Real.sq_sqrt (show 0 ≤ ∑ i, y i ^ 2 by positivity)
            have : ∑ i, (x i + y i) ^ 2 = ∑ i, x i ^ 2 + 2 * ∑ i, x i * y i + ∑ i, y i ^ 2 := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl (fun i _ => by ring)
            nlinarith
          have hom : ∀ (c : ℝ), 0 ≤ c → ∀ x : ι → ℝ, Real.sqrt (∑ i, (c * x i) ^ 2) = c * Real.sqrt (∑ i, x i ^ 2) := by
            intro c hc x
            have : ∑ i, (c * x i) ^ 2 = c ^ 2 * ∑ i, x i ^ 2 := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
            rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hc]
          refine ⟨?_, ?_⟩
          · intro v hv w hw a b ha hb hab
            simp only [soc, Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hv hw ⊢
            calc Real.sqrt (∑ i, (a * v (some i) + b * w (some i)) ^ 2)
                ≤ Real.sqrt (∑ i, (a * v (some i)) ^ 2) + Real.sqrt (∑ i, (b * w (some i)) ^ 2) := mink _ _
              _ = a * Real.sqrt (∑ i, v (some i) ^ 2) + b * Real.sqrt (∑ i, w (some i) ^ 2) := by
                rw [hom a ha, hom b hb]
              _ ≤ a * v none + b * w none := by gcongr
          · intro c hc v hv
            simp only [soc, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at hv ⊢
            rw [hom c hc]; exact mul_le_mul_of_nonneg_left hv hc
        have p1 : IsConvexCone (K_KS N) := by
          refine ⟨?_, ?_⟩
          · intro v hv w hw a b ha hb hab j
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            have := hv j; have := hw j; positivity
          · intro c hc v hv j
            simp only [Pi.smul_apply, smul_eq_mul]
            have := hv j; positivity
        have p2 : IsConvexCone (K_Kuiper N) := by
          refine ⟨?_, ?_⟩
          · intro v hv w hw a b ha hb hab
            rw [kuip] at hv hw ⊢
            intro i j
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            have := hv i j; have := hw i j
            nlinarith
          · intro c hc v hv
            rw [kuip] at hv ⊢
            intro i j
            simp only [Pi.smul_apply, smul_eq_mul]
            have := hv i j
            nlinarith
        have p3 : IsConvexCone (K_CvM N) := socCone (Fin N)
        have p4 : IsConvexCone (K_Watson N) := socCone (Option (Fin N))
        have hodd : ∀ n : ℕ, ∑ j ∈ Finset.range n, (2 * ((j : ℕ) : ℝ) + 1) = (n : ℝ) ^ 2 := by
          intro n
          induction n with
          | zero => simp
          | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
        have hwpos : ∀ i : Fin N, 0 < (2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * (N : ℝ) ^ 2) := by
          intro i; apply div_pos _ (by positivity); have : (0 : ℝ) ≤ (i : ℕ) := by positivity
          linarith
        have hwsum : ∑ i : Fin N, (2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * (N : ℝ) ^ 2) = 1 / 2 := by
          have := hodd N
          rw [← Fin.sum_univ_eq_sum_range (fun j => (2 * ((j : ℕ) : ℝ) + 1))] at this
          rw [← Finset.sum_div]
          have e : ∑ i : Fin N, (2 * ((i : ℕ) + 1 : ℝ) - 1) = ∑ j : Fin N, (2 * ((j : ℕ) : ℝ) + 1) :=
            Finset.sum_congr rfl (fun i _ => by ring)
          rw [e, this]; field_simp
        -- concavity (superadditivity) of weighted geometric mean
        have gm : ∀ (ι : Type) [Fintype ι] (w : ι → ℝ), (∀ i, 0 < w i) → ∑ i, w i = 1 →
            ∀ u v : ι → ℝ, (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ v i) →
            ∏ i, u i ^ w i + ∏ i, v i ^ w i ≤ ∏ i, (u i + v i) ^ w i := by
          intro ι _ w hw hw1 u v hu hv
          by_cases hp : ∀ i, 0 < u i + v i
          · set Pp := ∏ i, (u i + v i) ^ w i
            have hPp : 0 < Pp := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hp i) _)
            have hu' : ∏ i, u i ^ w i = Pp * ∏ i, (u i / (u i + v i)) ^ w i := by
              simp only [Pp]
              rw [← Finset.prod_mul_distrib]
              refine Finset.prod_congr rfl (fun i _ => ?_)
              rw [Real.div_rpow (hu i) (hp i).le, mul_div_cancel₀ _ (Real.rpow_pos_of_pos (hp i) _).ne']
            have hv' : ∏ i, v i ^ w i = Pp * ∏ i, (v i / (u i + v i)) ^ w i := by
              simp only [Pp]
              rw [← Finset.prod_mul_distrib]
              refine Finset.prod_congr rfl (fun i _ => ?_)
              rw [Real.div_rpow (hv i) (hp i).le, mul_div_cancel₀ _ (Real.rpow_pos_of_pos (hp i) _).ne']
            have a1 := Real.geom_mean_le_arith_mean_weighted Finset.univ w (fun i => u i / (u i + v i))
              (fun i _ => (hw i).le) hw1 (fun i _ => div_nonneg (hu i) (hp i).le)
            have a2 := Real.geom_mean_le_arith_mean_weighted Finset.univ w (fun i => v i / (u i + v i))
              (fun i _ => (hw i).le) hw1 (fun i _ => div_nonneg (hv i) (hp i).le)
            have hs : ∑ i, w i * (u i / (u i + v i)) + ∑ i, w i * (v i / (u i + v i)) = 1 := by
              rw [← Finset.sum_add_distrib, ← hw1]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              field_simp [(hp i).ne']
            rw [hu', hv']
            have : Pp * ∏ i, (u i / (u i + v i)) ^ w i + Pp * ∏ i, (v i / (u i + v i)) ^ w i ≤ Pp * 1 := by
              rw [← mul_add]; apply mul_le_mul_of_nonneg_left _ hPp.le
              linarith
            linarith
          · push_neg at hp
            obtain ⟨k, hk⟩ := hp
            have huk : u k = 0 := by linarith [hu k, hv k]
            have hvk : v k = 0 := by linarith [hu k, hv k]
            have z1 : ∏ i, u i ^ w i = 0 :=
              Finset.prod_eq_zero (Finset.mem_univ k) (by rw [huk, Real.zero_rpow (hw k).ne'])
            have z2 : ∏ i, v i ^ w i = 0 :=
              Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hvk, Real.zero_rpow (hw k).ne'])
            rw [z1, z2, add_zero]
            exact Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (add_nonneg (hu i) (hv i)) _)
        have gmh : ∀ (ι : Type) [Fintype ι] (w : ι → ℝ), (∀ i, 0 < w i) → ∑ i, w i = 1 →
            ∀ c : ℝ, 0 ≤ c → ∀ u : ι → ℝ, (∀ i, 0 ≤ u i) →
            ∏ i, (c * u i) ^ w i = c * ∏ i, u i ^ w i := by
          intro ι _ w hw hw1 c hc u hu
          simp_rw [Real.mul_rpow hc (hu _)]
          rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_nonneg hc (fun i _ => (hw i).le), hw1,
            Real.rpow_one]
        set W : Fin N ⊕ Fin N → ℝ := fun k => (2 * (((k.elim id id : Fin N) : ℕ) + 1 : ℝ) - 1) /
          (2 * (N : ℝ) ^ 2) with hW
        have hWpos : ∀ k, 0 < W k := by
          intro k; rcases k with i | i <;> exact hwpos i
        have hWsum : ∑ k, W k = 1 := by
          rw [Fintype.sum_sum_type]; simp only [W, Sum.elim_inl, Sum.elim_inr, id]
          rw [hwsum]; norm_num
        have hG : ∀ v : Option (Fin N ⊕ Fin N) → ℝ, (∀ i, 0 ≤ v (some (Sum.inl i))) →
            (∀ i, 0 ≤ v (some (Sum.inr i))) →
            ∏ i : Fin N, (v (some (Sum.inl i)) * v (some (Sum.inr i))) ^
              ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * (N : ℝ) ^ 2)) = ∏ k, v (some k) ^ W k := by
          intro v h1 h2
          rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl (fun i _ => ?_)
          simp only [W, Sum.elim_inl, Sum.elim_inr, id]
          exact Real.mul_rpow (h1 i) (h2 i)
        have p5 : IsConvexCone (K_AD N) := by
          refine ⟨?_, ?_⟩
          · intro v hv v' hv' a b ha hb hab
            obtain ⟨h1, h2, h3⟩ := hv
            obtain ⟨h1', h2', h3'⟩ := hv'
            have n1 : ∀ i, 0 ≤ (a • v + b • v') (some (Sum.inl i)) := by
              intro i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              have := h1 i; have := h1' i; positivity
            have n2 : ∀ i, 0 ≤ (a • v + b • v') (some (Sum.inr i)) := by
              intro i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              have := h2 i; have := h2' i; positivity
            refine ⟨n1, n2, ?_⟩
            rw [hG _ n1 n2]
            rw [hG _ h1 h2] at h3
            rw [hG _ h1' h2'] at h3'
            have hvk : ∀ k, 0 ≤ v (some k) := by intro k; rcases k with i | i; exact h1 i; exact h2 i
            have hvk' : ∀ k, 0 ≤ v' (some k) := by intro k; rcases k with i | i; exact h1' i; exact h2' i
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            calc |a * v none + b * v' none| ≤ |a * v none| + |b * v' none| := abs_add_le _ _
              _ = a * |v none| + b * |v' none| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
              _ ≤ a * ∏ k, v (some k) ^ W k + b * ∏ k, v' (some k) ^ W k := by gcongr
              _ = ∏ k, (a * v (some k)) ^ W k + ∏ k, (b * v' (some k)) ^ W k := by
                rw [gmh _ W hWpos hWsum a ha _ hvk, gmh _ W hWpos hWsum b hb _ hvk']
              _ ≤ ∏ k, (a * v (some k) + b * v' (some k)) ^ W k :=
                gm _ W hWpos hWsum _ _ (fun k => mul_nonneg ha (hvk k)) (fun k => mul_nonneg hb (hvk' k))
          · intro c hc v hv
            obtain ⟨h1, h2, h3⟩ := hv
            have n1 : ∀ i, 0 ≤ (c • v) (some (Sum.inl i)) := by
              intro i; simp only [Pi.smul_apply, smul_eq_mul]; have := h1 i; positivity
            have n2 : ∀ i, 0 ≤ (c • v) (some (Sum.inr i)) := by
              intro i; simp only [Pi.smul_apply, smul_eq_mul]; have := h2 i; positivity
            refine ⟨n1, n2, ?_⟩
            rw [hG _ n1 n2]
            rw [hG _ h1 h2] at h3
            have hvk : ∀ k, 0 ≤ v (some k) := by intro k; rcases k with i | i; exact h1 i; exact h2 i
            simp only [Pi.smul_apply, smul_eq_mul]
            rw [gmh _ W hWpos hWsum c hc _ hvk, abs_mul, abs_of_nonneg hc]
            exact mul_le_mul_of_nonneg_left h3 hc
        have p6 : ∀ (Q : ℝ) (ζ : Fin N → ℝ), ksZ ζ ≤ Q ↔ (A_KS N).mulVec ζ - b_KS N Q ∈ K_KS N := by
          intro Q ζ
          have hA : ∀ i, (A_KS N).mulVec ζ (Sum.inl i) = ζ i ∧ (A_KS N).mulVec ζ (Sum.inr i) = -ζ i := by
            intro i
            simp [A_KS, Matrix.fromRows_mulVec, Matrix.neg_mulVec]
          unfold ksZ
          rw [ciSup_le_iff (Finite.bddAbove_range _)]
          simp only [K_KS, Set.mem_setOf_eq, Pi.sub_apply, Sum.forall, b_KS, (hA _).1, (hA _).2, max_le_iff]
          constructor
          · rintro h
            exact ⟨fun i => by linarith [(h i).1], fun i => by linarith [(h i).2]⟩
          · rintro ⟨h1, h2⟩ i
            exact ⟨by linarith [h1 i], by linarith [h2 i]⟩
        have p7 : ∀ (Q : ℝ) (ζ : Fin N → ℝ),
            kuiperZ ζ ≤ Q ↔ (A_KS N).mulVec ζ - b_Kuiper N Q ∈ K_Kuiper N := by
          intro Q ζ
          have hA : ∀ i, (A_KS N).mulVec ζ (Sum.inl i) = ζ i ∧ (A_KS N).mulVec ζ (Sum.inr i) = -ζ i := by
            intro i
            simp [A_KS, Matrix.fromRows_mulVec, Matrix.neg_mulVec]
          rw [kuip]
          simp only [Pi.sub_apply, b_Kuiper, (hA _).1, (hA _).2]
          unfold kuiperZ
          constructor
          · intro h i j
            have h1 : ζ j - ((j : ℕ) : ℝ) / N ≤ ⨆ i : Fin N, (ζ i - ((i : ℕ) : ℝ) / N) :=
              le_ciSup (f := fun i : Fin N => ζ i - ((i : ℕ) : ℝ) / N) (Finite.bddAbove_range _) j
            have h2 : ((i : ℕ) + 1 : ℝ) / N - ζ i ≤ ⨆ i : Fin N, (((i : ℕ) + 1 : ℝ) / N - ζ i) :=
              le_ciSup (f := fun i : Fin N => ((i : ℕ) + 1 : ℝ) / N - ζ i) (Finite.bddAbove_range _) i
            linarith
          · intro h
            obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i : Fin N => ζ i - ((i : ℕ) : ℝ) / N)
            obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i : Fin N => ((i : ℕ) + 1 : ℝ) / N - ζ i)
            rw [← hi, ← hj]
            have := h i j
            linarith
        have p8 : ∀ Q : ℝ, 0 ≤ Q → 1 / (12 * (N : ℝ) ^ 2) ≤ Q ^ 2 → ∀ ζ : Fin N → ℝ,
            cvmZ ζ ≤ Q ↔ (A_CvM N).mulVec ζ - b_CvM N Q ∈ K_CvM N := by
          intro Q hQ hQ2 ζ
          have hA0 : (A_CvM N).mulVec ζ none = 0 := by
            simp [A_CvM, Matrix.mulVec, dotProduct]
          have hA : ∀ i, (A_CvM N).mulVec ζ (some i) = ζ i := by
            intro i
            simp [A_CvM, Matrix.mulVec, dotProduct]
          simp only [K_CvM, soc, Set.mem_setOf_eq, Pi.sub_apply, hA0, hA, b_CvM, zero_sub, neg_neg]
          have hR : 0 ≤ (N : ℝ) * Q ^ 2 - 1 / (12 * (N : ℝ)) := by
            have : 1 / (12 * (N : ℝ)) = N * (1 / (12 * (N : ℝ) ^ 2)) := by field_simp
            rw [this]; nlinarith
          rw [Real.sqrt_le_sqrt_iff hR, cvmZ, Real.sqrt_le_left hQ]
          have hsum : ∑ i : Fin N, ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N) - ζ i) ^ 2 =
              ∑ i : Fin N, (ζ i - (2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N)) ^ 2 :=
            Finset.sum_congr rfl (fun i _ => by ring)
          rw [hsum]
          set S := ∑ i : Fin N, (ζ i - (2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N)) ^ 2
          constructor
          · intro h
            have : 1 / (12 * (N : ℝ)) + S ≤ N * Q ^ 2 := by
              have e : 1 / (12 * (N : ℝ)) + S = N * (1 / (12 * (N : ℝ) ^ 2) + 1 / (N : ℝ) * S) := by
                field_simp
              rw [e]; exact mul_le_mul_of_nonneg_left h hNpos.le
            linarith
          · intro h
            have e : 1 / (12 * (N : ℝ) ^ 2) + 1 / (N : ℝ) * S = (1 / (12 * (N : ℝ)) + S) / N := by
              field_simp
            rw [e, div_le_iff₀ hNpos]
            linarith
        have p9 : ∀ Q : ℝ, 0 ≤ Q → ∀ ζ : Fin N → ℝ,
            watsonZ ζ ≤ Q ↔ (A_Watson N).mulVec ζ - b_Watson N Q ∈ K_Watson N := by
          intro Q hQ ζ
          have hsq : ∀ n : ℕ, ∑ j ∈ Finset.range n, (2 * ((j : ℕ) : ℝ) + 1) ^ 2 =
              (n : ℝ) * (4 * (n : ℝ) ^ 2 - 1) / 3 := by
            intro n
            induction n with
            | zero => simp
            | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
          have hC2 : ∑ j : Fin N, ((2 * ((j : ℕ) + 1 : ℝ) - 1) / (2 * N)) ^ 2 =
              (4 * (N : ℝ) ^ 2 - 1) / (12 * N) := by
            have := hsq N
            rw [← Fin.sum_univ_eq_sum_range (fun j => (2 * ((j : ℕ) : ℝ) + 1) ^ 2)] at this
            have e : ∑ j : Fin N, ((2 * ((j : ℕ) + 1 : ℝ) - 1) / (2 * N)) ^ 2 =
                (1 / (4 * (N : ℝ) ^ 2)) * ∑ j : Fin N, (2 * ((j : ℕ) : ℝ) + 1) ^ 2 := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_)
              field_simp; ring
            rw [e, this]; field_simp; ring
          set c : Fin N → ℝ := fun j => (2 * ((j : ℕ) + 1 : ℝ) - 1) / (2 * N) with hc
          set S1 := ∑ j, ζ j with hS1
          set S2 := ∑ j, ζ j ^ 2 with hS2
          set P := ∑ j, c j * ζ j with hP
          have hA1 : (A_Watson N).mulVec ζ none = P - S1 / 2 := by
            show ∑ j : Fin N, (2 * ((j : ℕ) + 1 : ℝ) - 1 - N) / (2 * N) * ζ j = _
            rw [hP, hS1, Finset.sum_div, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            simp only [hc]; field_simp; try ring
          have hA2 : (A_Watson N).mulVec ζ (some none) = -(P - S1 / 2) := by
            show ∑ j : Fin N, (N - (2 * ((j : ℕ) + 1 : ℝ) - 1)) / (2 * N) * ζ j = _
            rw [hP, hS1, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            simp only [hc]; field_simp; try ring
          have hA3 : ∀ i, (A_Watson N).mulVec ζ (some (some i)) = ζ i - S1 / N := by
            intro i
            show ∑ j, ((if i = j then 1 else 0) - 1 / (N : ℝ)) * ζ j = _
            simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
              Finset.sum_ite_eq, Finset.mem_univ, if_true, hS1, Finset.sum_div]
            congr 1
            refine Finset.sum_congr rfl (fun j _ => ?_)
            ring
          have hT : ∑ i : Fin N, (ζ i - S1 / N) ^ 2 = S2 - S1 ^ 2 / N := by
            have : ∑ i : Fin N, (ζ i - S1 / N) ^ 2 =
                ∑ i : Fin N, ζ i ^ 2 - 2 * (S1 / N) * ∑ i : Fin N, ζ i + N * (S1 / N) ^ 2 := by
              rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
              have : (N : ℝ) * (S1 / N) ^ 2 = ∑ _i : Fin N, (S1 / N) ^ 2 := by simp
              rw [this, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl (fun i _ => by ring)
            rw [this, ← hS1, ← hS2]; field_simp; ring
          have hcvm : cvmZ ζ ^ 2 = 1 / (12 * (N : ℝ) ^ 2) + 1 / (N : ℝ) *
              ((4 * (N : ℝ) ^ 2 - 1) / (12 * N) - 2 * P + S2) := by
            rw [cvmZ, Real.sq_sqrt (by positivity)]
            congr 2
            have : ∑ i : Fin N, ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N) - ζ i) ^ 2 =
                ∑ i : Fin N, (c i ^ 2 - 2 * (c i * ζ i) + ζ i ^ 2) :=
              Finset.sum_congr rfl (fun i _ => by simp only [hc]; ring)
            rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hC2]
          simp only [K_Watson, soc, Set.mem_setOf_eq, Fintype.sum_option, Pi.sub_apply, hA1, hA2, hA3,
            b_Watson, sub_zero]
          rw [hT, watsonZ, Real.sqrt_le_left hQ, Real.sqrt_le_iff, hcvm]
          set D := (N : ℝ) / 24 - (N : ℝ) * Q ^ 2 / 2
          have key : (N : ℝ) * (1 / (12 * (N : ℝ) ^ 2) + 1 / (N : ℝ) *
              ((4 * (N : ℝ) ^ 2 - 1) / (12 * N) - 2 * P + S2) - (1 / (N : ℝ) * S1 - 1 / 2) ^ 2) =
              N / 12 - 2 * P + S1 + (S2 - S1 ^ 2 / N) := by
            field_simp; ring
          constructor
          · intro h
            have h' := mul_le_mul_of_nonneg_left h hNpos.le
            rw [key] at h'
            have hTn : 0 ≤ S2 - S1 ^ 2 / N := by rw [← hT]; positivity
            constructor
            · simp only [D]; nlinarith
            · simp only [D]; nlinarith
          · rintro ⟨h0, h1⟩
            have : N / 12 - 2 * P + S1 + (S2 - S1 ^ 2 / N) ≤ N * Q ^ 2 := by
              simp only [D] at h0 h1; nlinarith
            rw [← key] at this
            exact le_of_mul_le_mul_left this hNpos
        have p10 : ∀ Q : ℝ, 0 ≤ Q → ∀ ζ : Fin N → ℝ,
            adZ ζ ≤ ENNReal.ofReal Q ↔ (A_AD N).mulVec ζ - b_AD N Q ∈ K_AD N := by
          intro Q hQ ζ
          have hA0 : (A_AD N).mulVec ζ none = 0 := by
            simp [A_AD, Matrix.mulVec, dotProduct]
          have hAl : ∀ i, (A_AD N).mulVec ζ (some (Sum.inl i)) = ζ i := by
            intro i; simp [A_AD, Matrix.mulVec, dotProduct]
          have hAr : ∀ i, (A_AD N).mulVec ζ (some (Sum.inr i)) = -ζ (Fin.rev i) := by
            intro i; simp [A_AD, Matrix.mulVec, dotProduct]
          have e1 : ∀ i, -ζ (Fin.rev i) - -1 = 1 - ζ (Fin.rev i) := fun i => by ring
          simp only [K_AD, Set.mem_setOf_eq, Pi.sub_apply, hA0, hAl, hAr, b_AD, sub_zero, zero_sub,
            abs_neg, e1, abs_of_pos (Real.exp_pos _)]
          unfold adZ
          split_ifs with h
          · rw [ENNReal.ofReal_le_ofReal_iff hQ, Real.sqrt_le_left hQ]
            have hpos : ∀ i, 0 < ζ i * (1 - ζ (Fin.rev i)) := by
              intro i; have := h i; have := h (Fin.rev i); apply mul_pos <;> linarith
            have hprod : ∏ i : Fin N, (ζ i * (1 - ζ (Fin.rev i))) ^
                ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * (N : ℝ) ^ 2)) =
                Real.exp (∑ i : Fin N, (Real.log (ζ i) + Real.log (1 - ζ (Fin.rev i))) *
                  ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * (N : ℝ) ^ 2))) := by
              rw [Real.exp_sum]
              refine Finset.prod_congr rfl (fun i _ => ?_)
              have := h i; have := h (Fin.rev i)
              rw [Real.rpow_def_of_pos (hpos i), Real.log_mul (by linarith) (by linarith)]
            rw [hprod, Real.exp_le_exp]
            have hsum : ∑ i : Fin N, ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (N : ℝ) ^ 2) *
                (Real.log (ζ i) + Real.log (1 - ζ (Fin.rev i))) =
                2 * ∑ i : Fin N, (Real.log (ζ i) + Real.log (1 - ζ (Fin.rev i))) *
                  ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * (N : ℝ) ^ 2)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              field_simp
            unfold adSqZ
            rw [hsum]
            have hl : ∀ i, 0 ≤ ζ i := fun i => (h i).1.le
            have hr : ∀ i, 0 ≤ 1 - ζ (Fin.rev i) := fun i => by linarith [(h (Fin.rev i)).2]
            constructor
            · intro h'; exact ⟨hl, hr, by linarith⟩
            · rintro ⟨_, _, h'⟩; linarith
          · simp only [top_le_iff, ENNReal.ofReal_ne_top, false_iff]
            rintro ⟨h1, h2, h3⟩
            apply h
            have hne : ∀ i, ζ i * (1 - ζ (Fin.rev i)) ≠ 0 := by
              intro i hz
              have : ∏ i : Fin N, (ζ i * (1 - ζ (Fin.rev i))) ^
                  ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * (N : ℝ) ^ 2)) = 0 :=
                Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hz, Real.zero_rpow (hwpos i).ne'])
              rw [this] at h3
              linarith [Real.exp_pos (-(Q ^ 2 + 1) / 2)]
            intro i
            have a1 : ζ i ≠ 0 := left_ne_zero_of_mul (hne i)
            have a2 : 1 - ζ (Fin.rev (Fin.rev i)) ≠ 0 := right_ne_zero_of_mul (hne (Fin.rev i))
            have b2 := h2 (Fin.rev i)
            rw [Fin.rev_rev] at a2 b2
            exact ⟨lt_of_le_of_ne (h1 i) (Ne.symm a1), by
              rcases lt_or_eq_of_le b2 with hh | hh
              · linarith
              · exact absurd hh.symm a2⟩
        exact ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩
